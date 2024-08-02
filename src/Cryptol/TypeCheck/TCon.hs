{-# Language OverloadedStrings, DeriveGeneric, DeriveAnyClass, Safe #-}
module Cryptol.TypeCheck.TCon where

import qualified Data.Map as Map
import GHC.Generics (Generic)
import Control.DeepSeq

import Cryptol.Parser.Selector
import qualified Cryptol.ModuleSystem.Name as M
import Cryptol.Utils.Fixity
import Cryptol.Utils.Ident
import Cryptol.Utils.PP

-- | This is used for pretty prinitng.
-- XXX: it would be nice to just rely in the info from the Prelude.
infixPrimTy :: TCon -> Maybe (Ident,Fixity)
infixPrimTy = \tc -> Map.lookup tc mp
  where
  mp = Map.fromList
          [ tInfix "=="  PC PEqual    (n 20)
          , tInfix "!="  PC PNeq      (n 20)
          , tInfix ">="  PC PGeq      (n 30)
          , tInfix  "+"  TF TCAdd     (l 80)
          , tInfix  "-"  TF TCSub     (l 80)
          , tInfix  "*"  TF TCMul     (l 90)
          , tInfix  "/"  TF TCDiv     (l 90)
          , tInfix  "%"  TF TCMod     (l 90)
          , tInfix  "^^" TF TCExp     (r 95)
          , tInfix  "/^" TF TCCeilDiv (l 90)
          , tInfix  "%^" TF TCCeilMod (l 90)
          ]

  r x = Fixity { fAssoc = RightAssoc, fLevel = x }
  l x = Fixity { fAssoc = LeftAssoc,  fLevel = x }
  n x = Fixity { fAssoc = NonAssoc,   fLevel = x }

  tInfix x mk tc f = (mk tc, (packIdent x, f))


builtInType :: M.Name -> Maybe TCon
builtInType nm =
  case M.nameInfo nm of
    M.GlobalName _ OrigName { ogModule = m }
      | m == M.TopModule preludeName -> Map.lookup (M.nameIdent nm) builtInTypes
    _ -> Nothing

  where
  x ~> y = (packIdent x, y)

  -- Built-in types from Cryptol.cry
  builtInTypes = Map.fromList
    [ -- Types
      "Bit"               ~> TC TCBit
    , "Integer"           ~> TC TCInteger

      -- Predicate contstructors
    , "=="                ~> PC PEqual
    , "!="                ~> PC PNeq
    , ">="                ~> PC PGeq
    , "Zero"              ~> PC PZero
    , "Logic"             ~> PC PLogic
    , "Ring"              ~> PC PRing
    , "Integral"          ~> PC PIntegral
    , "Eq"                ~> PC PEq
    , "Cmp"               ~> PC PCmp
    , "SignedCmp"         ~> PC PSignedCmp
    , "Literal"           ~> PC PLiteral
    , "LiteralLessThan"   ~> PC PLiteralLessThan

    -- Type functions
    , "+"                ~> TF TCAdd
    , "-"                ~> TF TCSub
    , "*"                ~> TF TCMul
    , "/"                ~> TF TCDiv
    , "%"                ~> TF TCMod
    , "^^"               ~> TF TCExp
    , "width"            ~> TF TCWidth
    , "min"              ~> TF TCMin
    , "max"              ~> TF TCMax
    , "/^"               ~> TF TCCeilDiv
    , "%^"               ~> TF TCCeilMod
    , "lengthFromThenTo" ~> TF TCLenFromThenTo
    ]




--------------------------------------------------------------------------------

infixr 5 :->

-- | Kinds, classify types.
data Kind   = KType
            | KNum
            | KProp
            | Kind :-> Kind
              deriving (Eq, Ord, Show, Generic, NFData)

class HasKind t where
  kindOf :: t -> Kind

instance HasKind TCon where
  kindOf (TC tc)      = kindOf tc
  kindOf (PC pc)      = kindOf pc
  kindOf (TF tf)      = kindOf tf
  kindOf (TError k)   = k

instance HasKind TC where
  kindOf tcon =
    case tcon of
      TCNum _   -> KNum
      TCBit     -> KType
      TCInteger -> KType
      TCSeq     -> KNum :-> KType :-> KType
      TCFun     -> KType :-> KType :-> KType
      TCTuple n -> foldr (:->) KType (replicate n KType)

instance HasKind PC where
  kindOf pc =
    case pc of
      PEqual     -> KNum :-> KNum :-> KProp
      PNeq       -> KNum :-> KNum :-> KProp
      PGeq       -> KNum :-> KNum :-> KProp
      PHas _     -> KType :-> KType :-> KProp
      PZero      -> KType :-> KProp
      PLogic     -> KType :-> KProp
      PRing      -> KType :-> KProp
      PIntegral  -> KType :-> KProp
      PEq        -> KType :-> KProp
      PCmp       -> KType :-> KProp
      PSignedCmp -> KType :-> KProp
      PLiteral   -> KNum :-> KType :-> KProp
      PLiteralLessThan -> KNum :-> KType :-> KProp
      PAnd       -> KProp :-> KProp :-> KProp
      PTrue      -> KProp

instance HasKind TFun where
  kindOf tfun =
    case tfun of
      TCWidth   -> KNum :-> KNum

      TCAdd     -> KNum :-> KNum :-> KNum
      TCSub     -> KNum :-> KNum :-> KNum
      TCMul     -> KNum :-> KNum :-> KNum
      TCDiv     -> KNum :-> KNum :-> KNum
      TCMod     -> KNum :-> KNum :-> KNum
      TCExp     -> KNum :-> KNum :-> KNum
      TCMin     -> KNum :-> KNum :-> KNum
      TCMax     -> KNum :-> KNum :-> KNum
      TCCeilDiv -> KNum :-> KNum :-> KNum
      TCCeilMod -> KNum :-> KNum :-> KNum

      TCLenFromThenTo -> KNum :-> KNum :-> KNum :-> KNum



-- | Type constants.
data TCon   = TC TC | PC PC | TF TFun | TError Kind
              deriving (Show, Eq, Ord, Generic, NFData)


-- | Predicate symbols.
-- If you add additional user-visible constructors, please update 'primTys'.
data PC     = PEqual        -- ^ @_ == _@
            | PNeq          -- ^ @_ /= _@
            | PGeq          -- ^ @_ >= _@

            -- classes
            | PHas Selector -- ^ @Has sel type field@ does not appear in schemas
            | PZero         -- ^ @Zero _@
            | PLogic        -- ^ @Logic _@
            | PRing         -- ^ @Ring _@
            | PIntegral     -- ^ @Integral _@
            | PEq           -- ^ @Eq _@
            | PCmp          -- ^ @Cmp _@
            | PSignedCmp    -- ^ @SignedCmp _@
            | PLiteral      -- ^ @Literal _ _@
            | PLiteralLessThan -- ^ @LiteralLessThan _ _@
            | PAnd          -- ^ This is useful when simplifying things in place
            | PTrue         -- ^ Ditto
              deriving (Show, Eq, Ord, Generic, NFData)

-- | 1-1 constants.
-- If you add additional user-visible constructors, please update 'primTys'.
data TC     = TCNum Integer            -- ^ Numbers
            | TCBit                    -- ^ Bit
            | TCInteger                -- ^ Integer
            | TCSeq                    -- ^ @[_] _@
            | TCFun                    -- ^ @_ -> _@
            | TCTuple Int              -- ^ @(_, _, _)@
              deriving (Show, Eq, Ord, Generic, NFData)




-- | Built-in type functions.
-- If you add additional user-visible constructors,
-- please update 'primTys' in "Cryptol.Prims.Types".
data TFun

  = TCAdd                 -- ^ @ : Num -> Num -> Num @
  | TCSub                 -- ^ @ : Num -> Num -> Num @
  | TCMul                 -- ^ @ : Num -> Num -> Num @
  | TCDiv                 -- ^ @ : Num -> Num -> Num @
  | TCMod                 -- ^ @ : Num -> Num -> Num @
  | TCExp                 -- ^ @ : Num -> Num -> Num @
  | TCWidth               -- ^ @ : Num -> Num @
  | TCMin                 -- ^ @ : Num -> Num -> Num @
  | TCMax                 -- ^ @ : Num -> Num -> Num @
  | TCCeilDiv             -- ^ @ : Num -> Num -> Num @
  | TCCeilMod             -- ^ @ : Num -> Num -> Num @

  -- Computing the lengths of explicit enumerations
  | TCLenFromThenTo       -- ^ @ : Num -> Num -> Num -> Num@
    -- Example: @[ 1, 5 .. 9 ] :: [lengthFromThenTo 1 5 9][b]@

    deriving (Show, Eq, Ord, Bounded, Enum, Generic, NFData)



--------------------------------------------------------------------------------
-- Pretty printing

instance PP Kind where
  ppPrec p k = case k of
    KType   -> char '*'
    KNum    -> char '#'
    KProp   -> text "Prop"
    l :-> r -> optParens (p >= 1) (sep [ppPrec 1 l, text "->", ppPrec 0 r])

instance PP TCon where
  ppPrec _ (TC tc)        = pp tc
  ppPrec _ (PC tc)        = pp tc
  ppPrec _ (TF tc)        = pp tc
  ppPrec _ (TError _)     = "Error"


instance PP PC where
  ppPrec _ x =
    case x of
      PEqual     -> text "(==)"
      PNeq       -> text "(/=)"
      PGeq       -> text "(>=)"
      PHas sel   -> parens (ppSelector sel)
      PZero      -> text "Zero"
      PLogic     -> text "Logic"
      PRing      -> text "Ring"
      PIntegral  -> text "Integral"
      PEq        -> text "Eq"
      PCmp       -> text "Cmp"
      PSignedCmp -> text "SignedCmp"
      PLiteral   -> text "Literal"
      PLiteralLessThan -> text "LiteralLessThan"
      PTrue      -> text "True"
      PAnd       -> text "(&&)"

instance PP TC where
  ppPrec _ x =
    case x of
      TCNum n   -> integer n
      TCBit     -> text "Bit"
      TCInteger -> text "Integer"
      TCSeq     -> text "[]"
      TCFun     -> text "(->)"
      TCTuple 0 -> text "()"
      TCTuple 1 -> text "(one tuple?)"
      TCTuple n -> parens $ hcat $ replicate (n-1) comma

instance PP TFun where
  ppPrec _ tcon =
    case tcon of
      TCAdd             -> text "+"
      TCSub             -> text "-"
      TCMul             -> text "*"
      TCDiv             -> text "/"
      TCMod             -> text "%"
      TCExp             -> text "^^"
      TCWidth           -> text "width"
      TCMin             -> text "min"
      TCMax             -> text "max"
      TCCeilDiv         -> text "/^"
      TCCeilMod         -> text "%^"
      TCLenFromThenTo   -> text "lengthFromThenTo"
