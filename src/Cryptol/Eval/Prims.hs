{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
module Cryptol.Eval.Prims where

import Cryptol.Backend
import Cryptol.Eval.Type
import Cryptol.Eval.Value
import Cryptol.ModuleSystem.Name
import Cryptol.TypeCheck.Solver.InfNat(Nat'(..))
import Cryptol.Utils.Panic

-- | This type provides a lightweight syntactic framework for defining
--   Cryptol primitives.  The main purpose of this type is to provide
--   an abstraction barrier that insulates the definitions of primitives
--   from possible changes in the representation of values.
data Prim sym
  = PFun (SEval sym (GenValue sym) -> Prim sym)
  | PStrict (GenValue sym -> Prim sym)
  | PWordFun (SWord sym -> Prim sym)
  | PTyPoly (TValue -> Prim sym)
  | PNumPoly (Nat' -> Prim sym)
  | PFinPoly (Integer -> Prim sym)
  | PPrim (SEval sym (GenValue sym))
  | PVal (GenValue sym)

-- | Evaluate a primitive into a value computation
evalPrim :: Backend sym => sym -> Name -> Prim sym -> SEval sym (GenValue sym)
evalPrim sym nm p = case p of
  PFun f      -> lam sym (evalPrim sym nm . f)
  PStrict f   -> lam sym (\x -> evalPrim sym nm . f =<< x)
  PWordFun f  -> lam sym (\x -> evalPrim sym nm . f =<< (fromVWord sym (show nm) =<< x))
  PTyPoly f   -> tlam sym (evalPrim sym nm . f)
  PNumPoly f  -> nlam sym (evalPrim sym nm . f)
  PFinPoly f  -> nlam sym (\case Nat n -> evalPrim sym nm (f n))
  PPrim m     -> m
  PVal v      -> pure v
