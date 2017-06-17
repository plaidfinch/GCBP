{-# LANGUAGE GADTs #-}

module Memo
  ( Memo, memo, apply )
  where

import           Control.Category
import           Data.Array
import           Data.MemoTrie    (HasTrie)
import qualified Data.MemoTrie    as MT
import           Prelude          hiding (id, (.))

data Memo a b where
  Id :: Memo a a
  Memo :: HasTrie a => (a -> b) -> Memo a b

memo :: (HasTrie a) => (a -> b) -> Memo a b
memo f = Memo (MT.memo f)

instance Category Memo where
  id = Id
  Id . m = m
  m . Id = m
  Memo f . Memo g = memo (f . g)

apply :: Memo a b -> a -> b
apply Id       = id
apply (Memo f) = f
