{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module GCBP where

import Prelude hiding ((.), id, Either(..), either)
import Control.Category
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Control.Applicative
import Data.Maybe
import Data.Functor.Identity
import Data.Proxy
import Data.Tuple
import Debug.Trace

data a + b = InL a | InR b deriving (Eq, Show, Ord)

either :: (a -> c) -> (b -> c) -> a + b -> c
either f g = \case
  InL a -> f a
  InR b -> g b

hoistMaybe :: Monad m => Maybe a -> MaybeT m a
hoistMaybe = MaybeT . return

-- TODO: Can we generalize away the specificity of MaybeT?
-- All we use is its Alternative-y-ness... (as Brent says)
maybeLeft :: Monad m => a + b -> MaybeT m a
maybeLeft = either return (const empty)

maybeRight :: Monad m => a + b -> MaybeT m b
maybeRight = either (const empty) return

swapEither :: a + b -> b + a
swapEither = either InR InL

commute :: Monad m => J m (a + b) (b + a)
commute = return . swapEither :<~>: return . swapEither

assoc :: Monad m => J m (a + (b + c)) ((a + b) + c)
assoc = return . either (InL . InL) (either (InL . InR) InR) :<~>:
        return . either (either InL (InR . InL)) (InR . InR)

reassocL :: Monad m
         => J m (a + (b + c)) (a' + (b' + c'))
         -> J m ((a + b) + c) ((a' + b') + c')
reassocL bij = assoc . bij . inverse assoc

reassocR :: Monad m
         => J m ((a + b) + c) ((a' + b') + c')
         -> J m (a + (b + c)) (a' + (b' + c'))
reassocR bij = inverse assoc . bij . assoc

class Category c => Groupoid c where
  inverse :: c a b -> c b a

data J m a b = (a -> m b) :<~>: (b -> m a)
infixr 8 :<~>:

type (<=>) = J Identity
infixr 8 <=>

instance Monad m => Groupoid (J m) where
  inverse (f :<~>: g) = g :<~>: f

instance Monad m => Category (J m) where
  id = return :<~>: return
  (f1 :<~>: g1) . (f2 :<~>: g2) =
    (f1 <=< f2) :<~>: (g2 <=< g1)

apply :: J m a b -> a -> m b
apply (f :<~>: _) = f

type (<->) = J (MaybeT Identity)
infixr 8 <->

hoistJ :: (forall x. m x -> n x) -> J m a b -> J n a b
hoistJ nat (f :<~>: g) = nat . f :<~>: nat . g

liftJ :: (Monad m, MonadTrans t) => J m a b -> J (t m) a b
liftJ = hoistJ lift

partial :: Monad m => J m a b -> J (MaybeT m) a b
partial = liftJ

unsafeTotal :: Functor m => J (MaybeT m) a b -> J m a b
unsafeTotal = hoistJ (fmap fromJust . runMaybeT)

leftPartial :: Monad m
            => J (MaybeT m) (a + c) (b + d)
            -> J (MaybeT m) a b
leftPartial (f :<~>: g) =
  (maybeLeft <=< f . InL) :<~>:
  (maybeLeft <=< g . InL)

rightPartial :: Monad m
             => J (MaybeT m) (a + c) (b + d)
             -> J (MaybeT m) c d
rightPartial (f :<~>: g) =
  (maybeRight <=< f . InR) :<~>:
  (maybeRight <=< g . InR)

(|||) :: Functor m => J m a c -> J m b d -> J m (a + b) (c + d)
(f :<~>: g) ||| (h :<~>: i) =
  either (fmap InL . f) (fmap InR . h) :<~>:
  either (fmap InL . g) (fmap InR . i)

--------------------------------------------------

gcbpExact :: Monad m
          => Integer
          -> J m (a + c) (b + d)
          -> J m c d
          -> J m a b
gcbpExact i minuend subtrahend =
  unsafeTotal . leftPartial $
    composeN i
      (step minuend subtrahend)
      (partial minuend)
  where
    composeN 0 _ = id
    composeN n f = f . composeN (n - 1) f

--------------------------------------------------

-- TODO: Think about how to use Cayley encoding to make both directions
-- use monadic right-recursion
step :: Monad m
     => J m (a + c) (b + d)
     -> J m c d
     -> J (MaybeT m) (a + c) (b + d)
     -> J (MaybeT m) (a + c) (b + d)
step minuend subtrahend current =
  current
  >>>
  inverse (leftPartial current ||| partial subtrahend)
  >>>
  partial minuend

(<||>) :: Alternative f => (a -> f b) -> (a -> f b) -> (a -> f b)
(f <||> g) a = f a <|> g a

instance Alternative m => Monoid (J m a b) where
  mempty =
    const empty :<~>: const empty
  mappend (f :<~>: g) ~(h :<~>: i) =
    f <||> h :<~>: g <||> i

gcbp :: Monad m => J m (a + c) (b + d) -> J m c d -> J m a b
gcbp minuend subtrahend =
  unsafeTotal . foldMap leftPartial $
    iterate (step minuend subtrahend) (partial minuend)

gmip :: Monad m
     => J m a a'
     -> J m b b'
     -> J m a' b'
     -> J m (fa + a) (fb + b)
     -> J m fa fb
gmip involA involB f' f =
  gcbp (reassocR $ f ||| f') ((involA >>> f' >>> inverse involB) ||| f')

gcbp' :: Monad m
      => J m (a + c) (b + d)
      -> J m c d
      -> J m a b
gcbp' minuend subtrahend =
  gmip id id subtrahend minuend

-- TODO: gmip all by itself (is this worth it?)

--------------------------------------------------

data Three = One | Two | Three deriving (Eq, Show, Ord, Enum)

test :: Three + Bool <=> Three + Bool
test = unsafeBuildBijection
  [ (InL One,   InL Two  )
  , (InL Two,   InL Three)
  , (InL Three, InR False)
  , (InR False, InR True )
  , (InR True,  InL One  ) ]

unsafeBuildBijection :: (Eq a, Eq b) => [(a,b)] -> (a <=> b)
unsafeBuildBijection pairs =
  unsafeTotal (f :<~>: g)
  where
    f = hoistMaybe . flip lookup pairs
    g = hoistMaybe . flip lookup (map swap pairs)

--------------------------------------------------

instrument :: String -> [a] -> [a]
instrument s =
  foldr cons nil
  where
    cons a as = trace (s ++ " :")  (a : as)
    nil       = trace (s ++ " []") []
