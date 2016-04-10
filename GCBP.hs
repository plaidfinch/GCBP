{-# LANGUAGE TypeOperators, TypeFamilies, LambdaCase, ScopedTypeVariables #-}

module GCBP where

import Prelude hiding ((.), id, Either(..), either)
import Control.Category
import Control.Monad
import Control.Applicative
import Data.Maybe
import Data.Monoid
import Data.Tuple
import Debug.Trace

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

data a + b = InL a | InR b deriving (Eq, Show, Ord)

either :: (a -> c) -> (b -> c) -> a + b -> c
either f g = \case
  InL a -> f a
  InR b -> g b

maybeLeft :: a + b -> Maybe a
maybeLeft = either Just (const Nothing)

maybeRight :: a + b -> Maybe b
maybeRight = either (const Nothing) Just

swapEither :: a + b -> b + a
swapEither = either InR InL

commute :: a + b <=> b + a
commute = swapEither :<=>: swapEither

assoc :: a + (b + c) <=> (a + b) + c
assoc = either (InL . InL) (either (InL . InR) InR) :<=>:
        either (either InL (InR . InL)) (InR . InR)

reassocL :: (a + (b + c)) <=> (a' + (b' + c'))
         -> ((a + b) + c) <=> ((a' + b') + c')
reassocL bij = assoc . bij . inverse assoc

reassocR :: ((a + b) + c) <=> ((a' + b') + c')
         -> (a + (b + c)) <=> (a' + (b' + c'))
reassocR bij = inverse assoc . bij . assoc

class Category c => Groupoid c where
  inverse :: c a b -> c b a

data a <=> b = (a -> b) :<=>: (b -> a)
infixr 8 <=>
infixr 8 :<=>:

-- Maybe later try modality-parameterized ___-jections?

instance Groupoid (<=>) where
  inverse (f :<=>: g) = g :<=>: f

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
  inverse (f :<->: g) = g :<->: f

applyPartial :: (a <-> b) -> a -> Maybe b
applyPartial (f :<->: _) = f

leftPartial :: (a + c <-> b + d) -> (a <-> b)
leftPartial (f :<->: g) =
  (maybeLeft <=< f . InL) :<->:
  (maybeLeft <=< g . InL)

rightPartial :: (a + c <-> b + d) -> (c <-> d)
rightPartial (f :<->: g) =
  (maybeRight <=< f . InR) :<->:
  (maybeRight <=< g . InR)

class Category arr => Parallel arr where
  (|||) :: arr a c -> arr b d -> arr (a + b) (c + d)

instance Parallel (<=>) where
  (f :<=>: g) ||| (h :<=>: i) =
    either (InL . f) (InR . h) :<=>:
    either (InL . g) (InR . i)

instance Parallel (<->) where
  (f :<->: g) ||| (h :<->: i) =
    either (fmap InL . f) (fmap InR . h) :<->:
    either (fmap InL . g) (fmap InR . i)

-- TODO: Think about how to use Cayley encoding to make both directions
-- use monadic right-recursion
step :: (a + c <=> b + d)
     -> (c <=> d)
     -> (a + c <-> b + d)
     -> (a + c <-> b + d)
step minuend subtrahend current =
  current
  >>>
  inverse (leftPartial current ||| partial subtrahend)
  >>>
  partial minuend

composeN :: Integer -> (a -> a) -> (a -> a)
composeN 0 _ = id
composeN n f = f . composeN (n - 1) f

gcbpExact :: Integer -> (a + c <=> b + d) -> (c <=> d) -> (a <=> b)
gcbpExact i minuend subtrahend =
  unsafeTotal . leftPartial $
    composeN i
      (step minuend subtrahend)
      (partial minuend)

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
  unsafeTotal (f :<->: g)
  where
    f = flip lookup pairs
    g = flip lookup (map swap pairs)

--------------------------------------------------

(<||>) :: Alternative f => (a -> f b) -> (a -> f b) -> (a -> f b)
(f <||> g) a = f a <|> g a

instance Monoid (a <-> b) where
  mempty =
    const Nothing :<->: const Nothing
  mappend (f :<->: g) ~(h :<->: i) =
    f <||> h :<->: g <||> i

gcbp :: (a + c <=> b + d) -> (c <=> d) -> (a <=> b)
gcbp minuend subtrahend =
  unsafeTotal . foldMap leftPartial $
    iterate (step minuend subtrahend) (partial minuend)

gmip :: (a <=> a')
     -> (b <=> b')
     -> (a' <=> b')
     -> (fa + a <=> fb + b)
     -> (fa <=> fb)
gmip involA involB f' f =
  gcbp (reassocR $ f ||| f') ((involA >>> f' >>> inverse involB) ||| f')

-- gcbp' :: (a + c <=> b + d) -> (c <=> d) -> (a <=> b)
-- gcbp' 

instrument :: String -> [a] -> [a]
instrument s =
  foldr cons nil
  where
    cons a as = trace (s ++ " :")  (a : as)
    nil       = trace (s ++ " []") []
