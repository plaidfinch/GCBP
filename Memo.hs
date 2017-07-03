{-# LANGUAGE GADTs #-}

module Memo
  ( Memo, memo, apply
  , MemoM, memoM, applyM)
  where

import           Control.Category
import           Control.Monad
import           Data.Array
import           Data.Functor.Identity
import           Data.MemoTrie    (HasTrie)
import qualified Data.MemoTrie    as MT
import           Prelude          hiding (id, (.))

data MemoM m a b where
  Id :: MemoM m a a
  Memo :: HasTrie a => (a -> m b) -> MemoM m a b

instance Monad m => Category (MemoM m) where
  id = Id
  Id . m = m
  m . Id = m
  Memo f . Memo g = memoM (f <=< g)

memoM :: HasTrie a => (a -> m b) -> MemoM m a b
memoM f = Memo (MT.memo f)

applyM :: Applicative m => MemoM m a b -> a -> m b
applyM Id       = pure
applyM (Memo f) = f

type Memo = MemoM Identity

memo :: (HasTrie a) => (a -> b) -> Memo a b
memo f = memoM (return . f)

apply :: Memo a b -> a -> b
apply f = runIdentity . applyM f

