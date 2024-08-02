-- |
-- Module      :  Cryptol.Eval.What4
-- Copyright   :  (c) 2020 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com

{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
module Cryptol.Eval.What4
  ( Value
  , primTable
  ) where

import qualified Control.Exception as X
import           Control.Monad.IO.Class

import qualified Data.Map as Map

import qualified What4.Interface as W4
import qualified What4.SWord as SW
import qualified What4.Utils.AbstractDomains as W4

import Cryptol.Backend
import Cryptol.Backend.Monad ( EvalError(..), Unsupported(..) )
import Cryptol.Backend.SeqMap
import Cryptol.Backend.WordValue
import Cryptol.Backend.What4

import Cryptol.Eval.Generic
import Cryptol.Eval.Prims
import Cryptol.Eval.Type (TValue(..))
import Cryptol.Eval.Value

import Cryptol.TypeCheck.Solver.InfNat( Nat'(..) )

import Cryptol.Utils.Ident

type Value sym = GenValue (What4 sym)

-- See also Cryptol.Prims.Eval.primTable
primTable :: W4.IsSymExprBuilder sym => What4 sym -> IO EvalOpts -> Map.Map PrimIdent (Prim (What4 sym))
primTable sym getEOpts =
  Map.union (genericPrimTable sym getEOpts) $

  Map.fromList $ map (\(n, v) -> (prelPrim n, v))

  [ -- Indexing and updates
    ("@"           , indexPrim sym IndexForward  (indexFront_int sym) (indexFront_segs sym))
  , ("!"           , indexPrim sym IndexBackward (indexFront_int sym) (indexFront_segs sym))

  , ("update"      , updatePrim sym (updateFrontSym_word sym) (updateFrontSym sym))
  , ("updateEnd"   , updatePrim sym (updateBackSym_word sym)  (updateBackSym sym))

  ]


indexFront_int ::
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) (GenValue (What4 sym)) ->
  TValue ->
  SInteger (What4 sym) ->
  SEval (What4 sym) (Value sym)
indexFront_int sym mblen _a xs _ix idx
  | Just i <- W4.asInteger idx
  = lookupSeqMap xs i

  | (lo, Just hi) <- bounds
  = case foldr f Nothing [lo .. hi] of
      Nothing -> raiseError sym (InvalidIndex Nothing)
      Just m  -> m

  | otherwise
  = liftIO (X.throw (UnsupportedSymbolicOp "unbounded integer indexing"))

 where
    w4sym = w4 sym

    f n (Just y) = Just $
       do p <- liftIO (W4.intEq w4sym idx =<< W4.intLit w4sym n)
          iteValue sym p (lookupSeqMap xs n) y
    f n Nothing = Just $ lookupSeqMap xs n

    bounds =
      (case W4.rangeLowBound (W4.integerBounds idx) of
        W4.Inclusive l -> max l 0
        _ -> 0
      , case (maxIdx, W4.rangeHiBound (W4.integerBounds idx)) of
          (Just n, W4.Inclusive h) -> Just (min n h)
          (Just n, _)              -> Just n
          _                        -> Nothing
      )

    -- Maximum possible in-bounds index given the length
    -- of the sequence. If the sequence is infinite, there
    -- isn't much we can do.
    maxIdx =
      case mblen of
        Nat n -> Just (n - 1)
indexFront_segs ::
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) (GenValue (What4 sym)) ->
  TValue ->
  Integer ->
  [IndexSegment (What4 sym)] ->
  SEval (What4 sym) (Value sym)
indexFront_segs sym mblen _a xs _ix _idx_bits [WordIndexSegment idx]
  | Just i <- SW.bvAsUnsignedInteger idx
  = lookupSeqMap xs i

  | otherwise
  = case foldr f Nothing idxs of
      Nothing -> raiseError sym (InvalidIndex Nothing)
      Just m  -> m

 where
    w4sym = w4 sym

    w = SW.bvWidth idx

    f n (Just y) = Just $
       do p <- liftIO (SW.bvEq w4sym idx =<< SW.bvLit w4sym w n)
          iteValue sym p (lookupSeqMap xs n) y
    f n Nothing = Just $ lookupSeqMap xs n

    -- maximum possible in-bounds index given the bitwidth
    -- of the index value and the length of the sequence
    maxIdx =
      case mblen of
        Nat n | n < 2^w -> n-1
        _ -> 2^w - 1

    -- concrete indices to consider, intersection of the
    -- range of values the index value might take with
    -- the legal values
    idxs =
      case SW.unsignedBVBounds idx of
        Just (lo, hi) -> [lo .. min hi maxIdx]
        _ -> [0 .. maxIdx]

indexFront_segs sym mblen _a xs _ix idx_bits segs =
  do xs' <- barrelShifter sym (mergeValue sym) shiftOp mblen xs idx_bits segs
     lookupSeqMap xs' 0
  where
    shiftOp vs amt = pure (indexSeqMap (\i -> lookupSeqMap vs $! amt+i))


updateFrontSym ::
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) (GenValue (What4 sym)) ->
  Either (SInteger (What4 sym)) (WordValue (What4 sym)) ->
  SEval (What4 sym) (Value sym) ->
  SEval (What4 sym) (SeqMap (What4 sym) (GenValue (What4 sym)))
updateFrontSym sym _len _eltTy vs (Left idx) val =
  case W4.asInteger idx of
    Just i -> return $ updateSeqMap vs i val
    Nothing -> return $ indexSeqMap $ \i ->
      do b <- intEq sym idx =<< integerLit sym i
         iteValue sym b val (lookupSeqMap vs i)

updateFrontSym sym len _eltTy vs (Right wv) val =
  wordValAsLit sym wv >>= \case
    Just j -> return $ updateSeqMap vs j val
    Nothing ->
      memoMap sym len $ indexSeqMap $ \i ->
      do b <- wordValueEqualsInteger sym wv i
         iteValue sym b val (lookupSeqMap vs i)

updateBackSym ::
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) (GenValue (What4 sym)) ->
  Either (SInteger (What4 sym)) (WordValue (What4 sym)) ->
  SEval (What4 sym) (Value sym) ->
  SEval (What4 sym) (SeqMap (What4 sym) (GenValue (What4 sym)))

updateBackSym sym (Nat n) _eltTy vs (Left idx) val =
  case W4.asInteger idx of
    Just i -> return $ updateSeqMap vs (n - 1 - i) val
    Nothing -> return $ indexSeqMap $ \i ->
      do b <- intEq sym idx =<< integerLit sym (n - 1 - i)
         iteValue sym b val (lookupSeqMap vs i)

updateBackSym sym (Nat n) _eltTy vs (Right wv) val =
  wordValAsLit sym wv >>= \case
    Just j ->
      return $ updateSeqMap vs (n - 1 - j) val
    Nothing ->
      memoMap sym (Nat n) $ indexSeqMap $ \i ->
      do b <- wordValueEqualsInteger sym wv (n - 1 - i)
         iteValue sym b val (lookupSeqMap vs i)


updateFrontSym_word ::
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  WordValue (What4 sym) ->
  Either (SInteger (What4 sym)) (WordValue (What4 sym)) ->
  SEval (What4 sym) (GenValue (What4 sym)) ->
  SEval (What4 sym) (WordValue (What4 sym))

updateFrontSym_word sym (Nat n) _eltTy w (Left idx) val =
  do idx' <- wordFromInt sym n idx
     updateWordByWord sym IndexForward w (wordVal idx') (fromVBit <$> val)
updateFrontSym_word sym (Nat _n) _eltTy w (Right idx) val =
  updateWordByWord sym IndexForward w idx (fromVBit <$> val)


updateBackSym_word ::
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  WordValue (What4 sym) ->
  Either (SInteger (What4 sym)) (WordValue (What4 sym)) ->
  SEval (What4 sym) (GenValue (What4 sym)) ->
  SEval (What4 sym) (WordValue (What4 sym))

updateBackSym_word sym (Nat n) _eltTy w (Left idx) val =
  do idx' <- wordFromInt sym n idx
     updateWordByWord sym IndexBackward w (wordVal idx') (fromVBit <$> val)
updateBackSym_word sym (Nat _n) _eltTy w (Right idx) val =
  updateWordByWord sym IndexBackward w idx (fromVBit <$> val)
