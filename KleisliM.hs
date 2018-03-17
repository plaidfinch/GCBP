{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module KleisliM where

import            Data.MemoTrie    (HasTrie)
import qualified  Data.MemoTrie    as MT

import Prelude hiding (id, (.))
import Control.Category
import Control.Monad
import Data.Functor.Identity

data KleisliM m a b where
  Id    :: KleisliM m a a
  Memo  :: HasTrie a => (a -> m b) -> KleisliM m a b

kleisliM :: HasTrie a => (a -> m b) -> KleisliM m a b
kleisliM f = Memo (MT.memo f)

instance Monad m => Category (KleisliM m) where
  id = Id
  Id  . m   = m
  m   . Id  = m
  Memo f . Memo g = kleisliM (f <=< g)

runKleisliM :: Applicative m => KleisliM m a b -> (a -> m b)
runKleisliM Id        = pure
runKleisliM (Memo f)  = f

------------------------------------------------------------

data Bij m a b = B
  { fwd  :: KleisliM m a b
  , bwd  :: KleisliM m b a
  }

pattern (:<->:) :: (HasTrie a, HasTrie b, Applicative m) => (a -> m b) -> (b -> m a) -> Bij m a b
pattern (:<->:) f g <- B (runKleisliM -> f) (runKleisliM -> g)
  where
    f :<->: g = B (kleisliM f) (kleisliM g)

pattern (:<=>:) :: (HasTrie a, HasTrie b) => (a -> b) -> (b -> a) -> Bij Identity a b
pattern (:<=>:) f g <- B  (runKleisliM >>> (>>> runIdentity) -> f)
                          (runKleisliM >>> (>>> runIdentity) -> g)
  where
    f :<=>: g = B  (kleisliM (f >>> Identity))
                   (kleisliM (g >>> Identity))
