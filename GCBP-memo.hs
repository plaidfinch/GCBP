{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

module GCBP where

import           Control.Applicative
import           Control.Arrow           (first)
import           Control.Category
import           Control.Monad
import           Data.Maybe
import           Data.Tuple
import           Debug.Trace
import           Prelude                 hiding (id, (.))

import           System.Random.Shuffle
import           Test.QuickCheck
import           Test.QuickCheck.Monadic

import           Data.MemoTrie           hiding (memo)
import           Memo

type (+) = Either

instance HasTrie a => HasTrie (Maybe a) where
  data (Maybe a) :->: x = MaybeTrie x (a :->: x)
  trie f = MaybeTrie (f Nothing) (trie (f . Just))
  untrie (MaybeTrie n j) = maybe n (untrie j)
  enumerate (MaybeTrie n j) = (Nothing,n) : ((map . first) Just $ enumerate j)

maybeLeft :: a + b -> Maybe a
maybeLeft = either Just (const Nothing)

maybeRight :: a + b -> Maybe b
maybeRight = either (const Nothing) Just

swapEither :: a + b -> b + a
swapEither = either Right Left

commute :: (HasTrie a, HasTrie b) => a + b <=> b + a
commute = swapEither <==> swapEither

assoc :: (HasTrie a, HasTrie b, HasTrie c) => a + (b + c) <=> (a + b) + c
assoc = either (Left . Left) (either (Left . Right) Right) <==>
        either (either Left (Right . Left)) (Right . Right)

reassocL :: (HasTrie a, HasTrie b, HasTrie c, HasTrie a', HasTrie b', HasTrie c')
         => (a + (b + c)) <=> (a' + (b' + c'))
         -> ((a + b) + c) <=> ((a' + b') + c')
reassocL bij = assoc . bij . inverse assoc

reassocR :: (HasTrie a, HasTrie b, HasTrie c, HasTrie a', HasTrie b', HasTrie c')
         => ((a + b) + c) <=> ((a' + b') + c')
         -> (a + (b + c)) <=> (a' + (b' + c'))
reassocR bij = inverse assoc . bij . assoc

-- TODO: Conjugate bijections by each other?

-- Ah, actually we can't write a general conjugate method to implement
-- reassocL and reassocR --- notice that we end up calling assoc
-- (which is polymorphic) at *two different* types!  So we wouldn't be
-- able to give a general enough type to the conjugation function.

class Category c => Groupoid c where
  inverse :: c a b -> c b a

data a <=> b = Memo a b :<=>: Memo b a
infixr 8 <=>
infixr 8 :<=>:
infixr 8 <==>

(<==>) :: (HasTrie a, HasTrie b) => (a -> b) -> (b -> a) -> (a <=> b)
f <==> g = memo f :<=>: memo g
-- satisfying laws not (yet) stated here

-- TODO: Maybe later try modality-parameterized ___-jections?

instance Groupoid (<=>) where
  inverse (f :<=>: g) = g :<=>: f

instance Category (<=>) where
  id = id :<=>: id
  (f1 :<=>: g1) . (f2 :<=>: g2) =
    (f1 . f2) :<=>: (g2 . g1)

applyIso :: (a <=> b) -> a -> b
applyIso (f :<=>: _) = apply f

data a <-> b = Memo a (Maybe b) :<->: Memo b (Maybe a)
infixr 8 <->
infixr 8 :<->:
infixr 8 <-->
-- satisfying laws not (yet) stated here

(<-->) :: (HasTrie a, HasTrie b) => (a -> Maybe b) -> (b -> Maybe a) -> (a <-> b)
(<-->) f g = memo f :<->: memo g

undef :: (HasTrie a, HasTrie b) => (a <-> b)
undef = const Nothing <--> const Nothing

partial :: (HasTrie a, HasTrie b) => (a <=> b) -> (a <-> b)
partial (f :<=>: g) = memo Just . f :<->: memo Just . g

unsafeTotal :: (HasTrie a, HasTrie b) => (a <-> b) -> (a <=> b)
unsafeTotal (f :<->: g) = memo fromJust . f :<=>: memo fromJust . g

instance Category (<->) where
  id = Just <--> Just
  (f1 :<->: g1) . (f2 :<->: g2) =
    (apply f1 <=< apply f2) <--> (apply g2 <=< apply g1)

instance Groupoid (<->) where
  inverse (f :<->: g) = g :<->: f

applyPartial :: (a <-> b) -> a -> Maybe b
applyPartial (f :<->: _) = apply f

leftPartial :: (HasTrie a, HasTrie b, HasTrie c, HasTrie d) => (a + c <-> b + d) -> (a <-> b)
leftPartial (f :<->: g) =
  (maybeLeft <=< apply f . Left) <-->
  (maybeLeft <=< apply g . Left)

rightPartial :: (HasTrie a, HasTrie b, HasTrie c, HasTrie d) => (a + c <-> b + d) -> (c <-> d)
rightPartial (f :<->: g) =
  (maybeRight <=< apply f . Right) <-->
  (maybeRight <=< apply g . Right)

class Category arr => Parallel arr where
  (|||) :: (HasTrie a, HasTrie b, HasTrie c, HasTrie d) => arr a c -> arr b d -> arr (a + b) (c + d)

-- NOTE: This is *not* the same as arrows, since bijections do not admit `arr`

instance Parallel (<=>) where
  (f :<=>: g) ||| (h :<=>: i) =
    either (Left . apply f) (Right . apply h) <==>
    either (Left . apply g) (Right . apply i)

instance Parallel (<->) where
  (f :<->: g) ||| (h :<->: i) =
    either (fmap Left . apply f) (fmap Right . apply h) <-->
    either (fmap Left . apply g) (fmap Right . apply i)

--------------------------------------------------

gcbpReference :: (HasTrie a0, HasTrie a1, HasTrie b0, HasTrie b1) => (a0 + a1 <=> b0 + b1) -> (a1 <=> b1) -> (a0 <=> b0)
gcbpReference a0a1__b0b1 a1__b1 =
    (iter (applyIso a0a1__b0b1) (applyIso $ inverse a1__b1) . Left)
    <==>
    (iter (applyIso $ inverse a0a1__b0b1) (applyIso $ a1__b1) . Left)
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

infixl 3 <||>
(<||>) :: Alternative f => (a -> f b) -> (a -> f b) -> (a -> f b)
(f <||> g) a = f a <|> g a

-- Merge operation. In theory, should only merge compatible partial bijections.
instance (HasTrie a, HasTrie b) => Monoid (a <-> b) where
  mempty =
    const Nothing <--> const Nothing
  mappend (f :<->: g) ~(h :<->: i) =  -- NOTE: this irrefutable match is Very Important
    (apply f <||> apply h) <--> (apply g <||> apply i)       --       this is because of the infinite merge in gcbp

gcbp :: (HasTrie a, HasTrie b, HasTrie c, HasTrie d) => (a + c <=> b + d) -> (c <=> d) -> (a <=> b)
gcbp minuend subtrahend = unsafeTotal . mconcat $ gcbpIterates minuend subtrahend

gcbpIterates :: (HasTrie a, HasTrie b, HasTrie c, HasTrie d) => (a + c <=> b + d) -> (c <=> d) -> [a <-> b]
gcbpIterates minuend subtrahend = map leftPartial $
  iterate (step minuend subtrahend) (partial minuend)

-- NOTE: How to fix the slowness of gcbp:
--       1. *All* bijections should be automatically memoized on construction
--       2. Composition during gcbp should be the "wrong way", which is okay because everything's a palindrome

gmip :: (HasTrie a, HasTrie a', HasTrie b, HasTrie b', HasTrie fa, HasTrie fb) =>
  (a <=> a')
     -> (b <=> b')
     -> (a' <=> b')
     -> (fa + a <=> fb + b)
     -> (fa <=> fb)
gmip involA involB f' f =
  gcbp (reassocR $ f ||| f') ((involA >>> f' >>> inverse involB) ||| f')

gcbp' :: (HasTrie a, HasTrie b, HasTrie c, HasTrie d) => (a + c <=> b + d) -> (c <=> d) -> (a <=> b)
gcbp' minuend subtrahend =
  gmip id id subtrahend minuend

-- TODO: gmip all by itself (is this worth it?)

--------------------------------------------------

data Three = One | Two | Three deriving (Eq, Show, Ord, Enum)

instance HasTrie Three where
  data Three :->: x = ThreeTree x x x
  trie f    = ThreeTree (f One) (f Two) (f Three)
  untrie (ThreeTree x y z) = \case {One -> x; Two -> y; Three -> z}
  enumerate (ThreeTree x y z) = [(One,x), (Two,y), (Three,z)]

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
  unsafeTotal (f <--> g)
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
-- > map (applyIso h) [0..999] -- see how long this takes
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
  assert $ map (applyIso h1) [0..m-1] == map (applyIso h2) [0..m-1]

-- gcbp is the same as converting to gmip and back
prop_gcbp_gcbp' :: Positive Integer -> Positive Integer -> Property
prop_gcbp_gcbp' (Positive m) (Positive n) = monadicIO $ do
  (f,g) <- run $ generateTestCase m n
  let h1 = gcbp f g
      h2 = gcbp' f g
  assert $ map (applyIso h1) [0..m-1] == map (applyIso h2) [0..m-1]

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
    add = fromSum <==> toSum
    fromSum (Left k)  = k
    fromSum (Right k) = m + k
    toSum k
      | k >= m    = Right (k - m)
      | otherwise = Left k

    cyc = mkCyc (+1) <==> mkCyc (subtract 1)
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
