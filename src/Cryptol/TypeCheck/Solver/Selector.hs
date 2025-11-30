-- |
-- Module      :  Cryptol.TypeCheck.Solver.Selector
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
{-# LANGUAGE PatternGuards #-}
module Cryptol.TypeCheck.Solver.Selector (tryHasGoal) where

import Cryptol.Parser.Position(Range)
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.InferTypes
import Cryptol.TypeCheck.Monad( InferM, unify, newGoals
                              , newType, applySubst, solveHasGoal
                              )
import Cryptol.TypeCheck.Subst (listParamSubst, apSubst)
import Cryptol.Utils.Ident (Ident)
import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.RecordMap

import Control.Monad(forM,guard)


recordType :: [Ident] -> InferM Type
recordType labels =
  do fields <- forM labels $ \l ->
        do t <- newType (TypeOfRecordField l) KType
           return (l,t)
     return (TRec (recordFromFields fields))

tupleType :: Int -> InferM Type
tupleType n =
  do fields <- mapM (\x -> newType (TypeOfTupleField x) KType)
                    [ 0 .. (n-1) ]
     return (tTuple fields)

listType :: Int -> InferM Type
listType n =
  do elems <- newType TypeOfSeqElement KType
     return (tSeq (tNum n) elems)


improveSelector :: Maybe Range -> Selector -> Type -> InferM Bool
improveSelector rng sel outerT =
  case sel of
    RecordSel _ mb -> cvt recordType mb
    TupleSel  _ mb -> cvt tupleType  mb
    ListSel   _ mb -> cvt listType   mb
  where
  cvt _ Nothing   = return False
  cvt f (Just a)  = do ty <- f a
                       ps <- unify (WithSource outerT (selSrc sel) rng) ty
                       newGoals CtExactType ps
                       newT <- applySubst outerT
                       return (newT /= outerT)


{- | Compute the type of a field based on the selector.
The given type should be "zonked" (i.e., substitution was applied to it),
and (outermost) type synonyms have been expanded.
-}
solveSelector :: Selector -> Type -> InferM (Maybe Type)
solveSelector sel outerT =
  case (sel, outerT) of

    (RecordSel l _, ty) ->
      case ty of
        TRec fs -> return (lookupField l fs)
        TNominal nt ts ->
          case ntDef nt of
            Struct c ->
              case lookupField l (ntFields c) of
                Nothing -> return Nothing
                Just t ->
                  do let su = listParamSubst (zip (ntParams nt) ts)
                     newGoals (CtPartialTypeFun (ntName nt))
                       $ apSubst su $ ntConstraints nt
                     return $ Just $ apSubst su t
            Enum {} -> pure Nothing
            Abstract -> pure Nothing

        _ -> return Nothing

    (TupleSel n _, ty) ->
      case ty of

        TCon (TC (TCTuple m)) ts ->
          return $ do guard (0 <= n && n < m)
                      return $ ts !! n

        _ -> return Nothing


    (ListSel n _, TCon (TC TCSeq) [l,t])
      | n < 2 -> return (Just t)
      | otherwise ->
       do newGoals CtSelector [ l >== tNum (n - 1) ]
          return (Just t)

    _ -> return Nothing

-- | Solve has-constraints.
tryHasGoal :: HasGoal -> InferM (Bool, Bool) -- ^ changes, solved
tryHasGoal has
  | TCon (PC (PHas sel)) [ th, ft ] <- goal (hasGoal has) =
    do let rng = Just (goalRange (hasGoal has))
       imped     <- improveSelector rng sel th
       outerT    <- tNoUser `fmap` applySubst th
       mbInnerT  <- solveSelector sel outerT
       case mbInnerT of
         Nothing -> return (imped, False)
         Just innerT ->
           do newGoals CtExactType =<<
                                  unify (WithSource innerT (selSrc sel) rng) ft
              oT <- applySubst outerT
              iT <- applySubst innerT
              sln <- mkSelSln sel oT iT
              solveHasGoal (hasName has) sln
              return (True, True)

  | otherwise = panic "hasGoalSolved"
                  [ "Unexpected selector proposition:"
                  , show (hasGoal has)
                  ]



{- | Generator an appropriate selector, once the "Has" constraint
has been discharged.  The resulting selectors should always work
on their corresponding types (i.e., tuple selectros only select from tuples).
This function generates the code for lifting tuple/record selectors to sequences
and functions.

Assumes types are zonked. -}
mkSelSln :: Selector -> Type -> Type -> InferM HasGoalSln
mkSelSln s outerT _innerT =
  return HasGoalSln { hasDoSelect = \e -> ESel e s
                    , hasDoSet    = \e v -> ESet outerT e s v }
