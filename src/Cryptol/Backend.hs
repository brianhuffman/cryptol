{-# Language FlexibleContexts #-}
{-# Language TypeFamilies #-}
module Cryptol.Backend
  ( Backend(..)
  , sDelay
  , invalidIndex
  , cryUserError
  , cryNoPrimError
  , IndexDirection(..)

  , enumerateIntBits
  , enumerateIntBits'
  ) where

import Control.Monad.IO.Class
import Data.Kind (Type)

import Cryptol.Backend.Monad
  ( EvalError(..), CallStack, pushCallFrame )
import Cryptol.ModuleSystem.Name(Name)
import Cryptol.Parser.Position
import Cryptol.TypeCheck.Solver.InfNat(Nat'(..),widthInteger)

data IndexDirection
  = IndexForward
  | IndexBackward

invalidIndex :: Backend sym => sym -> Integer -> SEval sym a
invalidIndex sym i = raiseError sym (InvalidIndex (Just i))

cryUserError :: Backend sym => sym -> String -> SEval sym a
cryUserError sym msg = raiseError sym (UserError msg)

cryNoPrimError :: Backend sym => sym -> Name -> SEval sym a
cryNoPrimError sym nm = raiseError sym (NoPrim nm)

{-# INLINE sDelay #-}
-- | Delay the given evaluation computation, returning a thunk
--   which will run the computation when forced.  Raise a loop
--   error if the resulting thunk is forced during its own evaluation.
sDelay :: Backend sym => sym -> SEval sym a -> SEval sym (SEval sym a)
sDelay sym m = sDelayFill sym m Nothing ""

-- | Compute the list of bits in an integer in big-endian order.
--   The integer argument is a concrete upper bound for
--   the symbolic integer.
enumerateIntBits' :: Backend sym =>
  sym ->
  Integer ->
  SInteger sym ->
  SEval sym (Integer, [SBit sym])
enumerateIntBits' sym n idx =
  do let width = widthInteger n
     w <- wordFromInt sym width idx
     bs <- unpackWord sym w
     pure (width, bs)

-- | Compute the list of bits in an integer in big-endian order.
--   Fails if neither the sequence length nor the type value
--   provide an upper bound for the integer.
enumerateIntBits :: Backend sym =>
  sym ->
  Nat' ->
  SInteger sym ->
  SEval sym (Integer, [SBit sym])
enumerateIntBits sym (Nat n) idx = enumerateIntBits' sym n idx

-- | This type class defines a collection of operations on bits, words and integers that
--   are necessary to define generic evaluator primitives that operate on both concrete
--   and symbolic values uniformly.
class MonadIO (SEval sym) => Backend sym where
  type SBit sym :: Type
  type SWord sym :: Type
  type SInteger sym :: Type
  type SEval sym :: Type -> Type

  -- ==== Evaluation monad operations ====

  -- | Check if an operation is "ready", which means its
  --   evaluation will be trivial.
  isReady :: sym -> SEval sym a -> SEval sym (Maybe a)

  -- | Produce a thunk value which can be filled with its associated computation
  --   after the fact.  A preallocated thunk is returned, along with an operation to
  --   fill the thunk with the associated computation.
  --   This is used to implement recursive declaration groups.
  sDeclareHole :: sym -> String -> SEval sym (SEval sym a, SEval sym a -> SEval sym ())

  -- | Delay the given evaluation computation, returning a thunk
  --   which will run the computation when forced.  Run the 'retry'
  --   computation instead if the resulting thunk is forced during
  --   its own evaluation.
  sDelayFill :: sym -> SEval sym a -> Maybe (SEval sym a) -> String -> SEval sym (SEval sym a)

  -- | Begin evaluating the given computation eagerly in a separate thread
  --   and return a thunk which will await the completion of the given computation
  --   when forced.
  sSpark :: sym -> SEval sym a -> SEval sym (SEval sym a)

  -- | Push a call frame on to the current call stack while evaluating the given action
  sPushFrame :: sym -> Name -> Range -> SEval sym a -> SEval sym a
  sPushFrame sym nm rng m = sModifyCallStack sym (pushCallFrame nm rng) m

  -- | Use the given call stack while evaluating the given action
  sWithCallStack :: sym -> CallStack -> SEval sym a -> SEval sym a
  sWithCallStack sym stk m = sModifyCallStack sym (\_ -> stk) m

  -- | Apply the given function to the current call stack while evaluating the given action
  sModifyCallStack :: sym -> (CallStack -> CallStack) -> SEval sym a -> SEval sym a

  -- | Retrieve the current evaluation call stack
  sGetCallStack :: sym -> SEval sym CallStack

  -- | Merge the two given computations according to the predicate.
  mergeEval ::
     sym ->
     (SBit sym -> a -> a -> SEval sym a) {- ^ A merge operation on values -} ->
     SBit sym {- ^ The condition -} ->
     SEval sym a {- ^ The "then" computation -} ->
     SEval sym a {- ^ The "else" computation -} ->
     SEval sym a

  -- | Assert that a condition must hold, and indicate what sort of
  --   error is indicated if the condition fails.
  assertSideCondition :: sym -> SBit sym -> EvalError -> SEval sym ()

  -- | Indiciate that an error condition exists
  raiseError :: sym -> EvalError -> SEval sym a

  -- ==== Identifying literal values ====

  -- | Determine if this symbolic bit is a boolean literal
  bitAsLit :: sym -> SBit sym -> Maybe Bool

  -- | The number of bits in a word value.
  wordLen :: sym -> SWord sym -> Integer

  -- | Determine if this symbolic word is a literal.
  --   If so, return the bit width and value.
  wordAsLit :: sym -> SWord sym -> Maybe (Integer, Integer)

  -- | Attempt to render a word value as an ASCII character.  Return 'Nothing'
  --   if the character value is unknown (e.g., for symbolic values).
  wordAsChar :: sym -> SWord sym -> Maybe Char

  -- | Determine if this symbolic integer is a literal
  integerAsLit :: sym -> SInteger sym -> Maybe Integer

  -- ==== Creating literal values ====

  -- | Construct a literal bit value from a boolean.
  bitLit :: sym -> Bool -> SBit sym

  -- | Construct a literal word value given a bit width and a value.
  wordLit ::
    sym ->
    Integer {- ^ Width -} ->
    Integer {- ^ Value -} ->
    SEval sym (SWord sym)

  -- | Construct a literal integer value from the given integer.
  integerLit ::
    sym ->
    Integer {- ^ Value -} ->
    SEval sym (SInteger sym)

  -- ==== If/then/else operations ====
  iteBit :: sym -> SBit sym -> SBit sym -> SBit sym -> SEval sym (SBit sym)
  iteWord :: sym -> SBit sym -> SWord sym -> SWord sym -> SEval sym (SWord sym)
  iteInteger :: sym -> SBit sym -> SInteger sym -> SInteger sym -> SEval sym (SInteger sym)

  -- ==== Bit operations ====
  bitEq  :: sym -> SBit sym -> SBit sym -> SEval sym (SBit sym)
  bitOr  :: sym -> SBit sym -> SBit sym -> SEval sym (SBit sym)
  bitAnd :: sym -> SBit sym -> SBit sym -> SEval sym (SBit sym)
  bitXor :: sym -> SBit sym -> SBit sym -> SEval sym (SBit sym)
  bitComplement :: sym -> SBit sym -> SEval sym (SBit sym)

  -- ==== Word operations ====

  -- | Extract the numbered bit from the word.
  --
  --   NOTE: this assumes that the sequence of bits is big-endian and finite, so the
  --   bit numbered 0 is the most significant bit.
  wordBit ::
    sym ->
    SWord sym ->
    Integer {- ^ Bit position to extract -} ->
    SEval sym (SBit sym)

  -- | Update the numbered bit in the word.
  --
  --   NOTE: this assumes that the sequence of bits is big-endian and finite, so the
  --   bit numbered 0 is the most significant bit.
  wordUpdate ::
    sym ->
    SWord sym ->
    Integer {- ^ Bit position to update -} ->
    SBit sym ->
    SEval sym (SWord sym)

  -- | Construct a word value from a finite sequence of bits.
  --   NOTE: this assumes that the sequence of bits is big-endian and finite, so the
  --   first element of the list will be the most significant bit.
  packWord ::
    sym ->
    [SBit sym] ->
    SEval sym (SWord sym)

  -- | Deconstruct a packed word value in to a finite sequence of bits.
  --   NOTE: this produces a list of bits that represent a big-endian word, so
  --   the most significant bit is the first element of the list.
  unpackWord ::
    sym ->
    SWord sym ->
    SEval sym [SBit sym]

  -- | Construct a packed word of the specified width from an integer value.
  wordFromInt ::
    sym ->
    Integer {- ^ bit-width -} ->
    SInteger sym ->
    SEval sym (SWord sym)

  -- | Concatenate the two given word values.
  --   NOTE: the first argument represents the more-significant bits
  joinWord ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | Take the most-significant bits, and return
  --   those bits and the remainder.  The first element
  --   of the pair is the most significant bits.
  --   The two integer sizes must sum to the length of the given word value.
  splitWord ::
    sym ->
    Integer {- ^ left width -} ->
    Integer {- ^ right width -} ->
    SWord sym ->
    SEval sym (SWord sym, SWord sym)

  -- | Extract a subsequence of bits from a packed word value.
  --   The first integer argument is the number of bits in the
  --   resulting word.  The second integer argument is the
  --   number of less-significant digits to discard.  Stated another
  --   way, the operation @extractWord n i w@ is equivalent to
  --   first shifting @w@ right by @i@ bits, and then truncating to
  --   @n@ bits.
  extractWord ::
    sym ->
    Integer {- ^ Number of bits to take -} ->
    Integer {- ^ starting bit -} ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | Bitwise OR
  wordOr ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | Bitwise AND
  wordAnd ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | Bitwise XOR
  wordXor ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | Bitwise complement
  wordComplement ::
    sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | 2's complement addition of packed words.  The arguments must have
  --   equal bit width, and the result is of the same width. Overflow is silently
  --   discarded.
  wordPlus ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | 2's complement subtraction of packed words.  The arguments must have
  --   equal bit width, and the result is of the same width. Overflow is silently
  --   discarded.
  wordMinus ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | 2's complement multiplication of packed words.  The arguments must have
  --   equal bit width, and the result is of the same width. The high bits of the
  --   multiplication are silently discarded.
  wordMult ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | 2's complement unsigned division of packed words.  The arguments must have
  --   equal bit width, and the result is of the same width.  It is illegal to
  --   call with a second argument concretely equal to 0.
  wordDiv ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | 2's complement unsigned modulus of packed words.  The arguments must have
  --   equal bit width, and the result is of the same width.  It is illegal to
  --   call with a second argument concretely equal to 0.
  wordMod ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | 2's complement signed division of packed words.  The arguments must have
  --   equal bit width, and the result is of the same width.  It is illegal to
  --   call with a second argument concretely equal to 0.
  wordSignedDiv ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | 2's complement signed modulus of packed words.  The arguments must have
  --   equal bit width, and the result is of the same width.  It is illegal to
  --   call with a second argument concretely equal to 0.
  wordSignedMod ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | Shift a bitvector left by the specified amount.
  --   The shift amount is considered as an unsigned value.
  --   Shifting by more than the word length results in 0.
  wordShiftLeft ::
    sym ->
    SWord sym {- ^ value to shift -} ->
    SWord sym {- ^ amount to shift by -} ->
    SEval sym (SWord sym)

  -- | Shift a bitvector right by the specified amount.
  --   This is a logical shift, which shifts in 0 values
  --   on the left. The shift amount is considered as an
  --   unsigned value. Shifting by more than the word length
  --   results in 0.
  wordShiftRight ::
    sym ->
    SWord sym {- ^ value to shift -} ->
    SWord sym {- ^ amount to shift by -} ->
    SEval sym (SWord sym)

  -- | Shift a bitvector right by the specified amount.  This is an
  --   arithmetic shift, which shifts in copies of the high bit on the
  --   left. The shift amount is considered as an unsigned
  --   value. Shifting by more than the word length results in filling
  --   the bitvector with the high bit.
  wordSignedShiftRight ::
    sym ->
    SWord sym {- ^ value to shift -} ->
    SWord sym {- ^ amount to shift by -} ->
    SEval sym (SWord sym)

  wordRotateLeft ::
    sym ->
    SWord sym {- ^ value to rotate -} ->
    SWord sym {- ^ amount to rotate by -} ->
    SEval sym (SWord sym)

  wordRotateRight ::
    sym ->
    SWord sym {- ^ value to rotate -} ->
    SWord sym {- ^ amount to rotate by -} ->
    SEval sym (SWord sym)



  -- | 2's complement negation of bitvectors
  wordNegate ::
    sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | Compute rounded-up log-2 of the input
  wordLg2 ::
    sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | Test if two words are equal.  Arguments must have the same width.
  wordEq ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SBit sym)

  -- | Signed less-than comparison on words.  Arguments must have the same width.
  wordSignedLessThan ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SBit sym)

  -- | Unsigned less-than comparison on words.  Arguments must have the same width.
  wordLessThan ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SBit sym)

  -- | Unsigned greater-than comparison on words.  Arguments must have the same width.
  wordGreaterThan ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SBit sym)

  -- | Construct an integer value from the given packed word.
  wordToInt ::
    sym ->
    SWord sym ->
    SEval sym (SInteger sym)

  -- | Construct a signed integer value from the given packed word.
  wordToSignedInt ::
    sym ->
    SWord sym ->
    SEval sym (SInteger sym)

  -- ==== Integer operations ====

  -- | Addition of unbounded integers.
  intPlus ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Negation of unbounded integers
  intNegate ::
    sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Subtraction of unbounded integers.
  intMinus ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Multiplication of unbounded integers.
  intMult ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Integer division, rounding down. It is illegal to
  --   call with a second argument concretely equal to 0.
  --   Same semantics as Haskell's @div@ operation.
  intDiv ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Integer modulus, with division rounding down. It is illegal to
  --   call with a second argument concretely equal to 0.
  --   Same semantics as Haskell's @mod@ operation.
  intMod ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Equality comparison on integers
  intEq ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SBit sym)

  -- | Less-than comparison on integers
  intLessThan ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SBit sym)

  -- | Greater-than comparison on integers
  intGreaterThan ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SBit sym)
