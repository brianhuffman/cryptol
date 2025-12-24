-- |
-- Module      :  Cryptol.TypeCheck.Solver.Nat
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- This module defines natural numbers and various arithmetic operators on them.

{-# LANGUAGE Safe #-}

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
module Cryptol.TypeCheck.Solver.Nat where

import Data.Bits
import Cryptol.Utils.Panic

import GHC.Generics (Generic)
import Control.DeepSeq

-- | Natural numbers
newtype Nat = Nat Integer
            deriving (Show, Eq, Ord, Generic, NFData)

fromNat :: Nat -> Maybe Integer
fromNat n' =
  case n' of
    Nat i -> Just i




--------------------------------------------------------------------------------


nAdd :: Nat -> Nat -> Nat
nAdd (Nat x) (Nat y) = Nat (x + y)

{-| Some algebraic properties of interest:

> 1 * x = x
> x * (y * z) = (x * y) * z
> 0 * x = 0
> x * y = y * x
> x * (a + b) = x * a + x * b

-}
nMul :: Nat -> Nat -> Nat
nMul (Nat x) (Nat y) = Nat (x * y)


{-| Some algebraic properties of interest:

> x ^ 0        = 1
> x ^ (n + 1)  = x * (x ^ n)
> x ^ (m + n)  = (x ^ m) * (x ^ n)
> x ^ (m * n)  = (x ^ m) ^ n

-}
nExp :: Nat -> Nat -> Nat
nExp _ (Nat 0)       = Nat 1
nExp (Nat x) (Nat y) = Nat (x ^ y)

nMin :: Nat -> Nat -> Nat
nMin (Nat x) (Nat y)  = Nat (min x y)

nMax :: Nat -> Nat -> Nat
nMax (Nat x) (Nat y)  = Nat (max x y)

{- | @nSub x y = Just z@ iff @z@ is the unique value
such that @Add y z = Just x@.  -}
nSub :: Nat -> Nat -> Maybe Nat
nSub (Nat x) (Nat y)
  | x >= y                    = Just (Nat (x - y))
nSub _ _                      = Nothing


-- XXX:
-- Does it make sense to define:
--   nDiv Inf (Nat x)  = Inf
--   nMod Inf (Nat x)  = Nat 0

{- | Rounds down.

> y * q + r = x
> x / y     = q with remainder r
> 0 <= r && r < y

We don't allow `Inf` in the first argument for two reasons:
  1. It matches the behavior of `nMod`,
  2. The well-formedness constraints can be expressed as a conjunction.
-}
nDiv :: Nat -> Nat -> Maybe Nat
nDiv _       (Nat 0)  = Nothing
nDiv (Nat x) (Nat y)  = Just (Nat (div x y))

nMod :: Nat -> Nat -> Maybe Nat
nMod _       (Nat 0)  = Nothing
nMod (Nat x) (Nat y)  = Just (Nat (mod x y))

-- | @nCeilDiv msgLen blockSize@ computes the least @n@ such that
-- @msgLen <= blockSize * n@. It is undefined when @blockSize = 0@,
-- or when @blockSize = inf@. @inf@ divided by any positive
-- finite value is @inf@.
nCeilDiv :: Nat -> Nat -> Maybe Nat
nCeilDiv _       (Nat 0)  = Nothing
nCeilDiv (Nat x) (Nat y)  = Just (Nat (- div (- x) y))

-- | @nCeilMod msgLen blockSize@ computes the least @k@ such that
-- @blockSize@ divides @msgLen + k@. It is undefined when @blockSize = 0@
-- or @blockSize = inf@.  @inf@ modulus any positive finite value is @0@.
nCeilMod :: Nat -> Nat -> Maybe Nat
nCeilMod _       (Nat 0)  = Nothing
nCeilMod (Nat x) (Nat y)  = Just (Nat (mod (- x) y))

-- | Rounds up.
-- @lg2 x = y@, iff @y@ is the smallest number such that @x <= 2 ^ y@
nLg2 :: Nat -> Nat
nLg2 (Nat 0)  = Nat 0
nLg2 (Nat n)  = case genLog n 2 of
                  Just (x,exact) | exact     -> Nat x
                                 | otherwise -> Nat (x + 1)
                  Nothing -> panic "Cryptol.TypeCheck.Solver.InfNat.nLg2"
                               [ "genLog returned Nothing" ]

-- | @nWidth n@ is number of bits needed to represent all numbers
-- from 0 to n, inclusive. @nWidth x = nLg2 (x + 1)@.
nWidth :: Nat -> Nat
nWidth (Nat n)  = Nat (widthInteger n)


--------------------------------------------------------------------------------

-- | Compute the logarithm of a number in the given base, rounded down to the
-- closest integer.  The boolean indicates if we the result is exact
-- (i.e., True means no rounding happened, False means we rounded down).
-- The logarithm base is the second argument.
genLog :: Integer -> Integer -> Maybe (Integer, Bool)
genLog x 0    = if x == 1 then Just (0, True) else Nothing
genLog _ 1    = Nothing
genLog 0 _    = Nothing
genLog x base = Just (exactLoop 0 x)
  where
  exactLoop s i
    | i == 1     = (s,True)
    | i < base   = (s,False)
    | otherwise  =
        let s1 = s + 1
        in s1 `seq` case divMod i base of
                      (j,r)
                        | r == 0    -> exactLoop s1 j
                        | otherwise -> (underLoop s1 j, False)

  underLoop s i
    | i < base  = s
    | otherwise = let s1 = s + 1 in s1 `seq` underLoop s1 (div i base)


-- | Compute the number of bits required to represent the given integer.
widthInteger :: Integer -> Integer
widthInteger x = go' 0 (if x < 0 then complement x else x)
  where
    go s 0 = s
    go s n = let s' = s + 1 in s' `seq` go s' (n `shiftR` 1)

    go' s n
      | n < bit 32 = go s n
      | otherwise  = let s' = s + 32 in s' `seq` go' s' (n `shiftR` 32)


-- | Compute the exact root of a natural number.
-- The second argument specifies which root we are computing.
rootExact :: Integer -> Integer -> Maybe Integer
rootExact x y = do (z,True) <- genRoot x y
                   return z



{- | Compute the the n-th root of a natural number, rounded down to
the closest natural number.  The boolean indicates if the result
is exact (i.e., True means no rounding was done, False means rounded down).
The second argument specifies which root we are computing. -}
genRoot :: Integer -> Integer -> Maybe (Integer, Bool)
genRoot _  0    = Nothing
genRoot x0 1    = Just (x0, True)
genRoot x0 root = Just (search 0 (x0+1))
  where
  search from to = let x = from + div (to - from) 2
                       a = x ^ root
                   in case compare a x0 of
                        EQ              -> (x, True)
                        LT | x /= from  -> search x to
                           | otherwise  -> (from, False)
                        GT | x /= to    -> search from x
                           | otherwise  -> (from, False)




