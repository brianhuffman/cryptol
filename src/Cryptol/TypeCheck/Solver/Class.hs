-- |
-- Module      :  Cryptol.TypeCheck.Solver.Class
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Solving class constraints.
-- If you make changes to this file, please update the documenation in RefMan.md

{-# LANGUAGE PatternGuards #-}
module Cryptol.TypeCheck.Solver.Class
  ( solveZeroInst
  , solveLogicInst
  , solveRingInst
  , solveIntegralInst
  , solveEqInst
  , solveCmpInst
  , solveLiteralInst
  , solveLiteralLessThanInst
  ) where

import Cryptol.TypeCheck.Type hiding (tSub)
import Cryptol.TypeCheck.SimpType (tSub,tWidth,tMax)
import Cryptol.TypeCheck.Solver.Types
import Cryptol.Utils.RecordMap

-- | Solve a Zero constraint by instance, if possible.
solveZeroInst :: Type -> Solved
solveZeroInst ty = case tNoUser ty of

  -- Zero Error -> fails
  TCon (TError {}) _ -> Unsolvable

  -- Zero Bit
  TCon (TC TCBit) [] -> SolvedIf []

  -- Zero Integer
  TCon (TC TCInteger) [] -> SolvedIf []

  -- Zero Real

  -- Zero a => Zero [n]a
  TCon (TC TCSeq) [_, a] -> SolvedIf [ pZero a ]

  -- Zero b => Zero (a -> b)
  TCon (TC TCFun) [_, b] -> SolvedIf [ pZero b ]

  -- (Zero a, Zero b) => Zero (a,b)
  TCon (TC (TCTuple _)) es -> SolvedIf [ pZero e | e <- es ]

  -- (Zero a, Zero b) => Zero { x1 : a, x2 : b }
  TRec fs -> SolvedIf [ pZero ety | ety <- recordElements fs ]

  -- Zero <nominal> -> fails
  TNominal {} -> Unsolvable

  _ -> Unsolved

-- | Solve a Logic constraint by instance, if possible.
solveLogicInst :: Type -> Solved
solveLogicInst ty = case tNoUser ty of

  -- Logic Error -> fails
  TCon (TError {}) _ -> Unsolvable

  -- Logic Bit
  TCon (TC TCBit) [] -> SolvedIf []

  -- Logic Integer fails
  TCon (TC TCInteger) [] -> Unsolvable

  -- Logic a => Logic [n]a
  TCon (TC TCSeq) [_, a] -> SolvedIf [ pLogic a ]

  -- Logic b => Logic (a -> b)
  TCon (TC TCFun) [_, b] -> SolvedIf [ pLogic b ]

  -- (Logic a, Logic b) => Logic (a,b)
  TCon (TC (TCTuple _)) es -> SolvedIf [ pLogic e | e <- es ]

  -- (Logic a, Logic b) => Logic { x1 : a, x2 : b }
  TRec fs -> SolvedIf [ pLogic ety | ety <- recordElements fs ]

  -- Logic <nominal> -> fails
  TNominal {} -> Unsolvable

  _ -> Unsolved


-- | Solve a Ring constraint by instance, if possible.
solveRingInst :: Type -> Solved
solveRingInst ty = case tNoUser ty of

  -- Ring Error -> fails
  TCon (TError {}) _ -> Unsolvable

  -- Ring [n]e
  TCon (TC TCSeq) [n, e] -> solveRingSeq n e

  -- Ring b => Ring (a -> b)
  TCon (TC TCFun) [_,b] -> SolvedIf [ pRing b ]

  -- (Ring a, Ring b) => Arith (a,b)
  TCon (TC (TCTuple _)) es -> SolvedIf [ pRing e | e <- es ]

  -- Ring Bit fails
  TCon (TC TCBit) [] -> Unsolvable

  -- Ring Integer
  TCon (TC TCInteger) [] -> SolvedIf []

  -- (Ring a, Ring b) => Ring { x1 : a, x2 : b }
  TRec fs -> SolvedIf [ pRing ety | ety <- recordElements fs ]

  -- Ring <nominal> -> fails
  TNominal {} -> Unsolvable

  _ -> Unsolved


-- | Solve a Ring constraint for a sequence.  The type passed here is the
-- element type of the sequence.
solveRingSeq :: Type -> Type -> Solved
solveRingSeq n ty = case tNoUser ty of

  -- fin n => Ring [n]Bit
  TCon (TC TCBit) [] -> SolvedIf []

  -- variables are not solvable.
  TVar {} -> case tNoUser n of
                {- We are sure that the lenght is not `fin`, so the
                special case for `Bit` does not apply.
                Arith ty => Arith [n]ty -}
                _                  -> Unsolved

  -- Ring ty => Ring [n]ty
  _ -> SolvedIf [ pRing ty ]


-- | Solve an Integral constraint by instance, if possible.
solveIntegralInst :: Type -> Solved
solveIntegralInst ty = case tNoUser ty of

  -- Integral Error -> fails
  TCon (TError {}) _ -> Unsolvable

  -- Integral Bit fails
  TCon (TC TCBit) [] -> Unsolvable

  -- Integral Integer
  TCon (TC TCInteger) [] -> SolvedIf []

  -- Integral [n]
  TCon (TC TCSeq) [_n, elTy] ->
    case tNoUser elTy of
      TCon (TC TCBit) [] -> SolvedIf []
      TVar _ -> Unsolved
      _ -> Unsolvable

  TVar _ -> Unsolved

  _ -> Unsolvable


-- | Solve Eq constraints.
solveEqInst :: Type -> Solved
solveEqInst ty = case tNoUser ty of

  -- Eq Error -> fails
  TCon (TError {}) _ -> Unsolvable

  -- eq Bit
  TCon (TC TCBit) [] -> SolvedIf []

  -- Eq Integer
  TCon (TC TCInteger) [] -> SolvedIf []

  -- (Eq a) => Eq [n]a
  TCon (TC TCSeq) [_,a] -> SolvedIf [ pEq a ]

  -- (Eq a, Eq b) => Eq (a,b)
  TCon (TC (TCTuple _)) es -> SolvedIf (map pEq es)

  -- Eq (a -> b) fails
  TCon (TC TCFun) [_,_] -> Unsolvable

  -- (Eq a, Eq b) => Eq { x:a, y:b }
  TRec fs -> SolvedIf [ pEq e | e <- recordElements fs ]

  -- Eq <nominal> -> fails
  TNominal {} -> Unsolvable

  _ -> Unsolved


-- | Solve Cmp constraints.
solveCmpInst :: Type -> Solved
solveCmpInst ty = case tNoUser ty of

  -- Cmp Error -> fails
  TCon (TError {}) _ -> Unsolvable

  -- Cmp Bit
  TCon (TC TCBit) [] -> SolvedIf []

  -- Cmp Integer
  TCon (TC TCInteger) [] -> SolvedIf []

  -- (Cmp a) => Cmp [n]a
  TCon (TC TCSeq) [_,a] -> SolvedIf [ pCmp a ]

  -- (Cmp a, Cmp b) => Cmp (a,b)
  TCon (TC (TCTuple _)) es -> SolvedIf (map pCmp es)

  -- Cmp (a -> b) fails
  TCon (TC TCFun) [_,_] -> Unsolvable

  -- (Cmp a, Cmp b) => Cmp { x:a, y:b }
  TRec fs -> SolvedIf [ pCmp e | e <- recordElements fs ]

  -- Cmp <nominal> -> fails
  TNominal{} -> Unsolvable

  _ -> Unsolved


-- | Solve Literal constraints.
solveLiteralInst :: Type -> Type -> Solved
solveLiteralInst val ty
  | TCon (TError {}) _ <- tNoUser val = Unsolvable
  | otherwise =
    case tNoUser ty of

      -- Literal n Error -> fails
      TCon (TError {}) _ -> Unsolvable

      -- (1 >= val) => Literal val Bit
      TCon (TC TCBit) [] -> SolvedIf [ tOne >== val ]

      -- (fin val) => Literal val Integer
      TCon (TC TCInteger) [] -> SolvedIf []

      -- (fin bits, bits >= width n) => Literal n [bits]
      TCon (TC TCSeq) [bits, elTy]
        | TCon (TC TCBit) [] <- ety ->
            SolvedIf [ bits >== tWidth val ]
        | TVar _ <- ety -> Unsolved
        where ety = tNoUser elTy

      TVar _ -> Unsolved

      _ -> Unsolvable


-- | Solve Literal constraints.
solveLiteralLessThanInst :: Type -> Type -> Solved
solveLiteralLessThanInst val ty
  | TCon (TError {}) _ <- tNoUser val = Unsolvable
  | otherwise =
    case tNoUser ty of

      -- Literal n Error -> fails
      TCon (TError {}) _ -> Unsolvable

      -- (2 >= val) => LiteralLessThan val Bit
      TCon (TC TCBit) [] -> SolvedIf [ tTwo >== val ]

      -- LiteralLessThan val Integer
      TCon (TC TCInteger) [] -> SolvedIf [ ]

      -- (fin bits, bits >= lg2 n) => LiteralLessThan n [bits]
      TCon (TC TCSeq) [bits, elTy]
        | TCon (TC TCBit) [] <- ety ->
            SolvedIf [ bits >== tWidth val' ]
        | TVar _ <- ety -> Unsolved
        where ety  = tNoUser elTy
              val' = tSub (tMax val tOne) tOne

      TVar _ -> Unsolved

      _ -> Unsolvable
