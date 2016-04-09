{-# LANGUAGE TypeOperators, TypeFamilies, LambdaCase, ScopedTypeVariables #-}

module GCBP where

import Prelude hiding ((.), id, Either(..), either)
import Control.Category
import Control.Monad
import Data.Maybe
import Data.List
import Data.Tuple
import Data.Proxy

-- gcbc :: (Either a c -> Either b c) -> a -> b
-- gcbc iso a = case iso (Left a) of
--   Left b -> b
--   Right c -> fixEither (iso . Right) c

-- fixEither :: (a -> Either b a) -> a -> b
-- fixEither f a0 =
--   case f a0 of
--     Left b -> b
--     Right a -> fixEither f a

-- swapEither :: Either a b -> Either b a
-- swapEither = either Right Left

-------------------------------------------------------------

data a + b = InL a | InR b deriving (Eq, Show)

class Category c => Groupoid c where
  invert :: c a b -> c b a

data a <=> b = (a -> b) :<=>: (b -> a)
infixr 8 <=>
infixr 8 :<=>:

-- Maybe later try modality-parameterized ___-jections?

instance Groupoid (<=>) where
  invert (f :<=>: g) = g :<=>: f

instance Category (<=>) where
  id = id :<=>: id
  (f1 :<=>: g1) . (f2 :<=>: g2) =
    (f1 . f2) :<=>: (g2 . g1)

applyIso :: (a <=> b) -> a -> b
applyIso (f :<=>: _) = f

data a <-> b = (a -> Maybe b) :<->: (b -> Maybe a)
infixr 8 <->
infixr 8 :<->:

partial :: (a <=> b) -> (a <-> b)
partial (f :<=>: g) = Just . f :<->: Just . g

unsafeTotal :: (a <-> b) -> (a <=> b)
unsafeTotal (f :<->: g) = fromJust . f :<=>: fromJust . g

instance Category (<->) where
  id = Just :<->: Just
  (f1 :<->: g1) . (f2 :<->: g2) =
    (f1 <=< f2) :<->: (g2 <=< g1)

instance Groupoid (<->) where
  invert (f :<->: g) = g :<->: f

applyPartial :: (a <-> b) -> a -> Maybe b
applyPartial (f :<->: _) = f

leftPartial :: (a + c <-> b + d) -> (a <-> b)
leftPartial (f :<->: g) =
  (either Just (const Nothing) <=< f . InL) :<->:
  (either Just (const Nothing) <=< g . InL)

either :: (a -> c) -> (b -> c) -> a + b -> c
either f g = \case
  InL a -> f a
  InR b -> g b

parallel :: (a <-> c) -> (b <-> d) -> (a + b <-> c + d)
parallel (f :<->: g) (h :<->: i) =
  either (fmap InL . f) (fmap InR . h) :<->:
  either (fmap InL . g) (fmap InR . i)

step :: (a + c <=> b + d)
     -> (c <=> d)
     -> (a + c <-> b + d)
     -> (a + c <-> b + d)
step minuend subtrahend current =
  current
  >>>
  invert (leftPartial current
          `parallel`
          partial subtrahend)
  >>>
  partial minuend

composeN :: Integer -> (a -> a) -> (a -> a)
composeN 0 _ = id
composeN n f = f . composeN (n - 1) f

class Finite c where
  size :: proxy c -> Integer

instance Finite Bool where
  size _ = 8

gcbp :: forall a b c d. Finite c
     => (a + c <=> b + d)
     -> (c <=> d)
     -> (a <=> b)
gcbp minuend subtrahend =
  unsafeTotal . leftPartial $
    composeN (size (Proxy :: Proxy c))
             (step minuend subtrahend)
             (partial minuend)

data Three = One | Two | Three deriving (Eq, Show)

test :: Three + Bool <=> Three + Bool
test = unsafeBuildBijection
  [ (InL One,   InL Two)
  , (InL Two,   InL Three)
  , (InL Three, InR False)
  , (InR False, InR True)
  , (InR True,  InL One) ]

unsafeBuildBijection :: (Eq a, Eq b) => [(a,b)] -> (a <=> b)
unsafeBuildBijection pairs =
  unsafeTotal (f :<->: g)
  where
    f = flip lookup pairs
    g = flip lookup (map swap pairs)
