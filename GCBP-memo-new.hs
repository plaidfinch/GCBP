{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns         #-}

module GCBP where

import           Control.Applicative
import           Control.Arrow (Kleisli(..), arr)
import           Control.Category
import           Control.Monad
import           Data.Bifunctor
import           Data.Functor.Identity
import           Data.Maybe
import           Data.Tuple
import           Debug.Trace
import           Prelude                 hiding (id, (.))

import            Data.MemoTrie    (HasTrie)
import qualified  Data.MemoTrie    as MT

import           System.Random.Shuffle
import           Test.QuickCheck
import           Test.QuickCheck.Monadic

------------------------------------------------------------
-- Sum type & utilities

type (+) = Either

maybeLeft :: a + b -> Maybe a
maybeLeft = either Just (const Nothing)

maybeRight :: a + b -> Maybe b
maybeRight = either (const Nothing) Just

------------------------------------------------------------
-- Classes

class Category arr => Parallel arr where
  (|||) :: (HasTrie a, HasTrie b, HasTrie c, HasTrie d) => arr a c -> arr b d -> arr (a + b) (c + d)

class Category c => Groupoid c where
  inverse :: c a b -> c b a

class Category arr => Mergeable arr where
  undef  :: (HasTrie a, HasTrie b) => arr a b
  (<||>) :: (HasTrie a, HasTrie b) => arr a b -> arr a b -> arr a b

merge :: (Mergeable arr, HasTrie a, HasTrie b) => [arr a b] -> arr a b
merge = foldr (<||>) undef

------------------------------------------------------------
-- Partial functions

factor :: Functor m => m a + m b -> m (a + b)
factor = either (fmap Left) (fmap Right)

instance Parallel (->) where
  (|||) = bimap

-- instance Monad m => Parallel (Kleisli m) where
--   Kleisli f ||| Kleisli g = Kleisli $ (f ||| g) >>> factor



instance Monad m => Parallel (KleisliM m) where
  (runKleisliM -> f) ||| (runKleisliM -> g) = kleisliM $ (bimap f g) >>> factor

instance (Monad m, Alternative m) => Mergeable (Kleisli m) where
  undef = Kleisli $ const empty
  Kleisli f <||> Kleisli g = Kleisli $ \a -> f a <|> g a

instance (Monad m, Alternative m) => Mergeable (KleisliM m) where
  undef = kleisliM $ const empty
  (runKleisliM -> f) <||> (runKleisliM -> g) = kleisliM $ \a -> f a <|> g a

------------------------------------------------------------

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


infixr 8 <=>, <->, :<=>:, :<->:

type (<=>) = Bij Identity
type (<->) = Bij Maybe

instance Monad m => Category (Bij m) where
  id = B id id
  (B f1 g1) . (B f2 g2) = B (f1 . f2) (g2 . g1)

instance Monad m => Groupoid (Bij m) where
  inverse (B f g) = B g f

-- (<~>) :: Monad m => (a -> b) -> (b -> a) -> Bij m a b
-- f <~> g = B (arr f) (arr g)

------------------------------------------------------------

-- assoc :: Monad m => Bij m (a + (b + c)) ((a + b) + c)
-- assoc = either (Left >>> Left) (either (Right >>> Left) Right) <~>
--         either (either Left (Left >>> Right)) (Right >>> Right)

-- reassocL
--   :: Monad m
--   => Bij m (a + (b + c)) (a' + (b' + c'))
--   -> Bij m ((a + b) + c) ((a' + b') + c')
-- reassocL bij = inverse assoc >>> bij >>> assoc

-- reassocR
--   :: Monad m
--   => Bij m ((a + b) + c) ((a' + b') + c')
--   -> Bij m (a + (b + c)) (a' + (b' + c'))
-- reassocR bij = assoc >>> bij >>> inverse assoc

applyTotal :: (HasTrie a, HasTrie b) => (a <=> b) -> a -> b
applyTotal (f :<=>: _) = f

partial :: (HasTrie a, HasTrie b) => (a <=> b) -> (a <-> b)
partial (f :<=>: g) = (f >>> Just) :<->: (g >>> Just)

unsafeTotal :: (HasTrie a, HasTrie b) => (a <-> b) -> (a <=> b)
unsafeTotal (f :<->: g) = (f >>> fromJust) :<=>: (g >>> fromJust)

applyPartial :: (HasTrie a, HasTrie b) => (a <-> b) -> a -> Maybe b
applyPartial (f :<->: _) = f

left :: (HasTrie a, HasTrie b) => a <-> a + b
left = (Left >>> Just) :<->: either Just (const Nothing)

leftPartial :: (HasTrie a, HasTrie b, HasTrie c, HasTrie d) => (a + c <-> b + d) -> (a <-> b)
leftPartial f = left >>> f >>> inverse left

-- NOTE: This is *not* the same as arrows, since bijections do not admit `arr`

instance Monad m => Parallel (Bij m) where
  (B f g) ||| (B h i) = B (f ||| h) (g ||| i)

--------------------------------------------------

gcbpReference :: (HasTrie a0, HasTrie a1, HasTrie b0, HasTrie b1) => (a0 + a1 <=> b0 + b1) -> (a1 <=> b1) -> (a0 <=> b0)
gcbpReference a0a1__b0b1 a1__b1 =
    (iter (applyTotal a0a1__b0b1) (applyTotal $ inverse a1__b1) . Left)
    :<=>:
    (iter (applyTotal $ inverse a0a1__b0b1) (applyTotal $ a1__b1) . Left)
  where
    iter a0a1_b0b1 b1_a1 a0a1 =
      case a0a1_b0b1 a0a1 of
        Left  b0 -> b0
        Right b1 -> iter a0a1_b0b1 b1_a1 (Right (b1_a1 b1))

gcbpExact :: (HasTrie a, HasTrie b, HasTrie c, HasTrie d) => Integer -> (a + c <=> b + d) -> (c <=> d) -> (a <=> b)
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
step :: (HasTrie a, HasTrie b, HasTrie c, HasTrie d)
     => (a + c <=> b + d)
     -> (c <=> d)
     -> (a + c <-> b + d)
     -> (a + c <-> b + d)
step minuend subtrahend current =
  current
  >>>
  inverse (leftPartial current ||| partial subtrahend)
  >>>
  partial minuend

-- NOTE: We can omit the call to `leftPartial current` in gcbp, but not in gcbpExact,
-- because it is never needed, since the merge operation "locks in" a value, so we
-- never loop back around to use that chunk. Thus, we could replace it with the
-- partial bijection defined nowhere, and gcbp would behave identically.

-- Merge operation. In theory, should only merge compatible partial bijections.
instance Mergeable (<->) where
  undef = B undef undef
  (B f g) <||> ~(B h i) =  -- NOTE: this irrefutable match is Very Important
    B (f <||> h) (g <||> i)     --       this is because of the infinite merge in gcbp

gcbp :: (HasTrie a, HasTrie b, HasTrie c, HasTrie d) => (a + c <=> b + d) -> (c <=> d) -> (a <=> b)
gcbp minuend subtrahend = unsafeTotal . merge $ gcbpIterates minuend subtrahend

gcbpIterates :: (HasTrie a, HasTrie b, HasTrie c, HasTrie d) => (a + c <=> b + d) -> (c <=> d) -> [a <-> b]
gcbpIterates minuend subtrahend = map leftPartial $
  iterate (step minuend subtrahend) (partial minuend)

-- NOTE: How to fix the slowness of gcbp:
--       1. *All* bijections should be automatically memoized on construction
--       2. Composition during gcbp should be the "wrong way", which is okay because everything's a palindrome

gmip :: (HasTrie a, HasTrie b, HasTrie fa, HasTrie fb)
     => (a <=> a')
     -> (b <=> b')
     -> (fa + a <=> fb + b)
     -> (a' <=> b')
     -> (fa <=> fb)
gmip involA involB h g =
  gcbp h (involA >>> g >>> inverse involB)

gcbp' :: (HasTrie a, HasTrie b, HasTrie c, HasTrie d) => (a + c <=> b + d) -> (c <=> d) -> (a <=> b)
gcbp' = gmip id id

-- TODO: gmip all by itself (is this worth it?)

--------------------------------------------------

data Three = One | Two | Three deriving (Eq, Show, Ord, Enum)

instance HasTrie Three where
  

test :: Three + Bool <=> Three + Bool
test = unsafeBuildBijection
  [ (Left One,   Left Two  )
  , (Left Two,   Left Three)
  , (Left Three, Right False)
  , (Right False, Right True )
  , (Right True,  Left One  ) ]

-- NOTE: Invariant: input list must be the graph of a bijection
unsafeBuildBijection :: (Eq a, Eq b, HasTrie a, HasTrie b) => [(a,b)] -> (a <=> b)
unsafeBuildBijection pairs =
  unsafeTotal (f :<->: g)
  where
    f = flip lookup pairs
    g = flip lookup (map swap pairs)

-- generateTestCase m n generates random endobijections on [m]+[n] and
-- [n] (which can be subtracted to compute an endobijection on [m] for
-- testing/demonstration purposes).
generateTestCase :: Integer -> Integer
  -> IO (Integer + Integer <=> Integer + Integer, Integer <=> Integer)
generateTestCase m n = do
  let a = [0..m-1]
      c = [0..n-1]
      ac = (map Left a ++ map Right c)
  bd <- shuffleM ac
  d  <- shuffleM c
  return $ (unsafeBuildBijection $ zip ac bd, unsafeBuildBijection $ zip c d)

-- BAY 6/13: the crazy thing is, gcbp is not actually all that slow!
-- It's hard to get reliable timings with ghci since I think some of
-- the computation to actually produce the test bijections is being
-- shared, but it is fairly comparable to gcbpReference, even up to
-- values of m and n in the thousands.
--
-- To test it I have been doing things like
--
-- > (f,g) <- generateTestCase 1000 1000
-- > let h = gcbp f g
-- > map (applyTotal h) [0..999] -- see how long this takes
--
-- The inverse of the bijection produced by gcbp seems a bit slower
-- but not by much.
--
-- I wonder if it's because things are quadratic *in the maximum path
-- length* which is not all that long for random bijections.  But
-- perhaps we could construct pessimal examples where the difference
-- is more pronounced.
--
-- Indeed, check this out:
--
-- >>> (f,g) <- generateTestCase 1000 1000
-- (0.00 secs, 3,511,040 bytes)
-- >>> take 20 . map (numDefined 1000) . scanl (<>) undef $ gcbpIterates f g
-- [0,488,752,882,938,969,986,993,997,998,999,999,999,1000,1000,1000,1000,1000,1000,1000]
--
-- f is a randomly constructed bijection between two sets of size
-- 2000, and g is between sets of size 1000. If we iterate the gcbp
-- procedure, the resulting bijection *very quickly* gets close to
-- being totally defined.  There are just a few stubborn elements that
-- take more than 10 iterations to reach their destination.  This
-- makes sense if you think about it: the *sum* of the lengths of
-- *all* the paths can't be more than m+n (the total size of both
-- sets) (otherwise there would be Too Many Pigeons).  So the average
-- cycle is going to be very short, on average something like (m+n)/m.
--
-- We can intentionally construct a pessimal case, for example where f
-- sends each element to the "next" element down, except the very last
-- element in the bottom set which it sends back to the top; g is the
-- identity.  Then all elements but 1 will immediately reach their
-- destination after 1 iteration, but that one last element requires n
-- iterations.



-- gcbp is the same as the reference implementation
prop_gcbp_reference :: Positive Integer -> Positive Integer -> Property
prop_gcbp_reference (Positive m) (Positive n) = monadicIO $ do
  (f,g) <- run $ generateTestCase m n
  let h1 = gcbp f g
      h2 = gcbpReference f g
  assert $ map (applyTotal h1) [0..m-1] == map (applyTotal h2) [0..m-1]

-- gcbp is the same as converting to gmip and back
prop_gcbp_gcbp' :: Positive Integer -> Positive Integer -> Property
prop_gcbp_gcbp' (Positive m) (Positive n) = monadicIO $ do
  (f,g) <- run $ generateTestCase m n
  let h1 = gcbp f g
      h2 = gcbp' f g
  assert $ map (applyTotal h1) [0..m-1] == map (applyTotal h2) [0..m-1]

--------------------------------------------------

instrument :: String -> [a] -> [a]
instrument s =
  foldr cons nil
  where
    cons a as = trace (s ++ " :")  (a : as)
    nil       = trace (s ++ " []") []

------------------------------------------------------------

numDefined :: Integer -> (Integer <-> Integer) -> Int
numDefined n f = length . catMaybes . map (applyPartial f) $ [0..n-1]

------------------------------------------------------------

-- Construct a pessimal test case.  pessimal m n generates the
-- bijection on [m]+[n] which sends each element to the "next element"
-- (in particular sending the last element of [m] to the first of [n],
-- and vice versa), and the identity bijection on [n].  This should be
-- a worst case for gcbp.
pessimal :: Integer -> Integer -> (Integer + Integer <=> Integer + Integer, Integer <=> Integer)
pessimal m n = (add >>> cyc >>> inverse add, id)
  where

    -- add :: [m] + [n] <=> [m+n]
    add = fromSum :<=>: toSum
    fromSum (Left k)  = k
    fromSum (Right k) = m + k
    toSum k
      | k >= m    = Right (k - m)
      | otherwise = Left k

    cyc = mkCyc (+1) :<=>: mkCyc (subtract 1)
    mkCyc f k = f k `mod` (m+n)

-- It does seem to take a bit longer to compute the very last element
-- of the pessimal gcbp result than to compute the entire thing for a
-- random set of bijections.  e.g. after computing h = gcbp f g for (f,g)
-- from generateTestCase 5000 5000, it took ~6 seconds to print the
-- result applied to [0..4999].  For pessimal 5000 5000, it printed
-- the first 4999 elements almost instantly, and then took ~14 seconds
-- to compute the final one.
--
-- Performance of (inverse h) is about the same.
