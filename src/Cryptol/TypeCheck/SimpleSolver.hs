{-# LANGUAGE PatternGuards, Trustworthy #-}
module Cryptol.TypeCheck.SimpleSolver ( simplify , simplifyStep) where

import Cryptol.TypeCheck.Type hiding
  ( tSub, tMul, tDiv, tMod, tExp, tMin, tLenFromThenTo)
import Cryptol.TypeCheck.Solver.Types
import Cryptol.TypeCheck.Solver.Numeric(cryIsEqual, cryIsNotEqual, cryIsGeq)
import Cryptol.TypeCheck.Solver.Class
  ( solveZeroInst, solveLogicInst, solveRingInst
  , solveIntegralInst
  , solveEqInst, solveCmpInst, solveSignedCmpInst
  , solveLiteralInst
  , solveLiteralLessThanInst
  )

import Cryptol.Utils.Debug(ppTrace)
import Cryptol.TypeCheck.PP


simplify :: Ctxt -> Prop -> Prop
simplify ctxt p =
  case simplifyStep ctxt p of
    Unsolvable  -> case tIsError p of
                     Nothing -> tError p
                     _       -> p
    Unsolved    -> dbg msg p
      where msg = text "unsolved:" <+> pp p
    SolvedIf ps -> dbg msg $ pAnd (map (simplify ctxt) ps)
     where msg = case ps of
                    [] -> text "solved:" <+> pp p
                    _  -> pp p <+> text "~~~>" <+> commaSep (map pp ps)

  where
  dbg msg x
      -- Change `False` to `True` below to enable extra tracing. Note that
      -- this is written with an extraneous `id` expression to suppress
      -- pattern-match coverage checking warnings in this one case.
    | id False  = ppTrace msg x
    | otherwise = x


simplifyStep :: Ctxt -> Prop -> Solved
simplifyStep ctxt prop =
  case tNoUser prop of
    TCon (PC PTrue)  []        -> SolvedIf []
    TCon (PC PAnd)   [l,r]     -> SolvedIf [l,r]

    TCon (PC PZero)  [ty]      -> solveZeroInst ty
    TCon (PC PLogic) [ty]      -> solveLogicInst ty
    TCon (PC PRing)  [ty]      -> solveRingInst ty
    TCon (PC PIntegral) [ty]   -> solveIntegralInst ty

    TCon (PC PEq)    [ty]      -> solveEqInst ty
    TCon (PC PCmp)   [ty]      -> solveCmpInst ty
    TCon (PC PSignedCmp) [ty]  -> solveSignedCmpInst ty
    TCon (PC PLiteral) [t1,t2] -> solveLiteralInst t1 t2
    TCon (PC PLiteralLessThan) [t1,t2] -> solveLiteralLessThanInst t1 t2

    TCon (PC PEqual) [t1,t2]   -> cryIsEqual ctxt t1 t2
    TCon (PC PNeq)  [t1,t2]    -> cryIsNotEqual ctxt t1 t2
    TCon (PC PGeq)  [t1,t2]    -> cryIsGeq ctxt t1 t2

    _                          -> Unsolved


