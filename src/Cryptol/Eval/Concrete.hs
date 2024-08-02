-- |
-- Module      :  Cryptol.Eval.Concrete
-- Copyright   :  (c) 2013-2020 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
module Cryptol.Eval.Concrete
  ( module Cryptol.Backend.Concrete
  , Value
  , primTable
  , toExpr
  ) where

import Control.Monad (guard, zipWithM, mzero)
import Data.Foldable (foldl')
import Data.List (find)
import MonadLib( ChoiceT, findOne, lift )
import qualified Cryptol.F2 as F2

import qualified Data.Map.Strict as Map
import Data.Map(Map)
import qualified Data.Vector as Vector
import qualified Data.IntMap.Strict as IMap

import Cryptol.TypeCheck.Solver.InfNat (Nat'(..))

import Cryptol.Backend
import Cryptol.Backend.Concrete
import Cryptol.Backend.Monad
import Cryptol.Backend.SeqMap
import Cryptol.Backend.WordValue

import Cryptol.Eval.Generic
import Cryptol.Eval.Prims
import Cryptol.Eval.Type
import Cryptol.Eval.Value
import Cryptol.ModuleSystem.Name
import Cryptol.TypeCheck.AST as AST
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.Ident (PrimIdent,prelPrim)
import Cryptol.Utils.PP
import Cryptol.Utils.RecordMap

type Value = GenValue Concrete

-- Value to Expression conversion ----------------------------------------------

-- | Given an expected type, returns an expression that evaluates to
-- this value, if we can determine it.
toExpr :: PrimMap -> TValue -> Value -> Eval (Maybe AST.Expr)
toExpr prims t0 v0 = findOne (go t0 v0)
  where

  prim n = ePrim prims (prelPrim n)


  go :: TValue -> Value -> ChoiceT Eval Expr
  go ty val =
    case (ty,val) of
      (TVRec tfs, VRecord vfs) ->
        do -- NB, vfs first argument to keep their display order
           res <- zipRecordsM (\_lbl v t -> go t =<< lift v) vfs tfs
           case res of
             Left _ -> mismatch -- different fields
             Right efs -> pure (ERec efs)

      (TVNominal nt ts (TVStruct tfs), VRecord vfs) ->
        do -- NB, vfs first argument to keep their display order
           res <- zipRecordsM (\_lbl v t -> go t =<< lift v) vfs tfs
           case res of
             Left _ -> mismatch -- different fields
             Right efs ->
               let c = case ntDef nt of
                         Struct co -> ntConName co
                         Enum {} -> panic "toExpr" ["Enum vs Record"]
                         Abstract -> panic "toExp" ["Asbtract vs Record"]
                   f = foldl (\x t -> ETApp x (tNumValTy t)) (EVar c) ts
                in pure (EApp f (ERec efs))
      (TVNominal nt ts (TVEnum tfss), VEnum i' vf_map) ->
        let i = fromInteger i'
        in
        case tfss Vector.!? i of
          Nothing -> mismatch -- enum constructor not found
          Just conT ->
            do let tfs = conFields conT
               vfs <- case IMap.lookup i vf_map of
                        Just con -> pure (conFields con)
                        Nothing  -> panic "toExpr" ["Missing constructor"]
               guard (Vector.length tfs == Vector.length vfs)
               c <- case ntDef nt of
                      Struct {} -> panic "toExpr" ["Enum vs Record"]
                      Abstract {} -> panic "toExpr" ["Enum vs Abstract"]
                      Enum cons ->
                        case find (\con -> ecNumber con == i) cons of
                          Just con -> pure (ecName con)
                          Nothing -> mismatch
               let f = foldl' (\x t -> ETApp x (tNumValTy t)) (EVar c) ts
               foldl' EApp f <$>
                  (zipWithM go (Vector.toList tfs) =<<
                              lift (sequence (Vector.toList vfs)))

      (TVTuple ts, VTuple tvs) ->
        do guard (length ts == length tvs)
           ETuple <$> (zipWithM go ts =<< lift (sequence tvs))
      (TVBit, VBit b) ->
        pure (prim (if b then "True" else "False"))
      (TVInteger, VInteger i) ->
        pure $ ETApp (ETApp (prim "number") (tNum i)) tInteger

      (TVSeq _ b, VSeq n svs) ->
        do ses <- traverse (go b) =<< lift (sequence (enumerateSeqMap n svs))
           pure $ EList ses (tValTy b)
      (TVSeq n TVBit, VWord _ wval) ->
        do BV _ v <- lift (asWordVal Concrete wval)
           pure $ ETApp (ETApp (prim "number") (tNum v)) (tWord (tNum n))

      (_,VFun{})     -> mzero
      (_,VPoly{})    -> mzero
      (_,VNumPoly{}) -> mzero
      _ -> mismatch
    where
      mismatch :: forall a. ChoiceT Eval a
      mismatch =
        do doc <- lift (ppValue Concrete defaultPPOpts val)
           panic "Cryptol.Eval.Concrete.toExpr"
             ["type mismatch:"
             , pretty (tValTy ty)
             , show doc
             ]

-- Primitives ------------------------------------------------------------------

primTable :: IO EvalOpts -> Map PrimIdent (Prim Concrete)
primTable getEOpts = let sym = Concrete in
  Map.union (genericPrimTable sym getEOpts) $

  Map.fromList $ map (\(n, v) -> (prelPrim n, v))

  [ -- Indexing and updates
    ("@"          , {-# SCC "Prelude::(@)" #-}
                    indexPrim sym IndexForward indexFront_int indexFront_segs)
  , ("!"          , {-# SCC "Prelude::(!)" #-}
                    indexPrim sym IndexBackward indexFront_int indexFront_segs)

  , ("update"     , {-# SCC "Prelude::update" #-}
                    updatePrim sym updateFront_word updateFront)

  , ("updateEnd"  , {-# SCC "Prelude::updateEnd" #-}
                    updatePrim sym updateBack_word updateBack)

   , ("pmult",
        PFinPoly \u ->
        PFinPoly \v ->
        PWordFun \(BV _ x) ->
        PWordFun \(BV _ y) ->
        PPrim
            let z = if u <= v then
                      F2.pmult (fromInteger (u+1)) x y
                    else
                      F2.pmult (fromInteger (v+1)) y x
             in return . VWord (1+u+v) . wordVal . mkBv (1+u+v) $! z)

   , ("pmod",
        PFinPoly \_u ->
        PFinPoly \v ->
        PWordFun \(BV w x) ->
        PWordFun \(BV _ m) ->
        PPrim
          do assertSideCondition sym (m /= 0) DivideByZero
             return . VWord v . wordVal . mkBv v $! F2.pmod (fromInteger w) x m)

  , ("pdiv",
        PFinPoly \_u ->
        PFinPoly \_v ->
        PWordFun \(BV w x) ->
        PWordFun \(BV _ m) ->
        PPrim
          do assertSideCondition sym (m /= 0) DivideByZero
             return . VWord w . wordVal . mkBv w $! F2.pdiv (fromInteger w) x m)
  ]


-- Sequence Primitives ---------------------------------------------------------

indexFront_int :: Nat' -> TValue -> SeqMap Concrete (GenValue Concrete) -> TValue -> Integer -> Eval Value
indexFront_int _mblen _a vs _ix idx = lookupSeqMap vs idx

indexFront_segs :: Nat' -> TValue -> SeqMap Concrete (GenValue Concrete) -> TValue -> Integer -> [IndexSegment Concrete] -> Eval Value
indexFront_segs _mblen _a vs _ix idx_bits segs = lookupSeqMap vs $! packSegments idx_bits segs

packSegments :: Integer -> [IndexSegment Concrete] -> Integer
packSegments = loop 0
  where
  loop !val !n segs =
    case segs of
      [] -> val
      [WordIndexSegment (BV _ x)] -> val + x
      WordIndexSegment (BV xlen x) : bs ->
        let n' = n - xlen
         in loop (val + (x*2^n')) n' bs
      BitIndexSegment True : bs ->
        let n' = n - 1
         in loop (val + 2^n') n' bs
      BitIndexSegment False : bs ->
        let n' = n - 1
         in loop val n' bs

updateFront ::
  Nat'               {- ^ length of the sequence -} ->
  TValue             {- ^ type of values in the sequence -} ->
  SeqMap Concrete (GenValue Concrete) {- ^ sequence to update -} ->
  Either Integer (WordValue Concrete) {- ^ index -} ->
  Eval Value         {- ^ new value at index -} ->
  Eval (SeqMap Concrete (GenValue Concrete))
updateFront _len _eltTy vs (Left idx) val = do
  return $ updateSeqMap vs idx val

updateFront _len _eltTy vs (Right w) val = do
  idx <- bvVal <$> asWordVal Concrete w
  return $ updateSeqMap vs idx val

updateFront_word ::
  Nat'               {- ^ length of the sequence -} ->
  TValue             {- ^ type of values in the sequence -} ->
  WordValue Concrete {- ^ bit sequence to update -} ->
  Either Integer (WordValue Concrete) {- ^ index -} ->
  Eval Value         {- ^ new value at index -} ->
  Eval (WordValue Concrete)
updateFront_word _len _eltTy bs (Left idx) val = do
  updateWordValue Concrete bs idx (fromVBit <$> val)

updateFront_word _len _eltTy bs (Right w) val = do
  idx <- bvVal <$> asWordVal Concrete w
  updateWordValue Concrete bs idx (fromVBit <$> val)

updateBack ::
  Nat'               {- ^ length of the sequence -} ->
  TValue             {- ^ type of values in the sequence -} ->
  SeqMap Concrete (GenValue Concrete) {- ^ sequence to update -} ->
  Either Integer (WordValue Concrete) {- ^ index -} ->
  Eval Value         {- ^ new value at index -} ->
  Eval (SeqMap Concrete (GenValue Concrete))
updateBack (Nat n) _eltTy vs (Left idx) val = do
  return $ updateSeqMap vs (n - idx - 1) val
updateBack (Nat n) _eltTy vs (Right w) val = do
  idx <- bvVal <$> asWordVal Concrete w
  return $ updateSeqMap vs (n - idx - 1) val

updateBack_word ::
  Nat'               {- ^ length of the sequence -} ->
  TValue             {- ^ type of values in the sequence -} ->
  WordValue Concrete {- ^ bit sequence to update -} ->
  Either Integer (WordValue Concrete) {- ^ index -} ->
  Eval Value         {- ^ new value at index -} ->
  Eval (WordValue Concrete)
updateBack_word (Nat n) _eltTy bs (Left idx) val = do
  updateWordValue Concrete bs (n - idx - 1) (fromVBit <$> val)
updateBack_word (Nat n) _eltTy bs (Right w) val = do
  idx <- bvVal <$> asWordVal Concrete w
  updateWordValue Concrete bs (n - idx - 1) (fromVBit <$> val)
