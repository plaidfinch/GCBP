{-# LANGUAGE DefaultSignatures         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PartialTypeSignatures     #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE TypeFamilies              #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Bijections where

import           Control.Arrow       ((&&&))
import           Data.Default.Class
import           Data.Bifunctor
import           Data.List           (find, findIndex, isSuffixOf, partition)
import qualified Data.Map            as M
import           Data.Maybe          (catMaybes, fromMaybe)
import           Data.Tuple          (swap)
import           Data.Typeable

import           Diagrams.Core.Names
import           Diagrams.Prelude    hiding (dot, end, r2, start, set)

import Data.Colour.SRGB

------------------------------------------------------------
-- Diagram utilities

dot :: _ => Diagram b
dot = circle 0.25 # fc black # lw none

------------------------------------------------------------
-- Name utilities

disjointly :: Qualifiable q => ([q] -> q) -> [q] -> q
disjointly f = f . zipWith (.>>) ['a'..]

(|@) :: Char -> Int -> Name
c |@ i = c .>> toName i

(|@@) :: Char -> [Int] -> [Name]
c |@@ is = map (c |@) is

------------------------------------------------------------
-- Parallel composition

-- Parallel composition is not necessarily associative, nor is empty
-- an identity.
class Par p where
  empty :: p
  (+++) :: p -> p -> p
  x +++ y = pars [x,y]
  pars  :: [p] -> p
  pars = foldr (+++) empty

------------------------------------------------------------
-- Singletons

class Singleton s where
  type Single s :: *
  single :: Single s -> s

------------------------------------------------------------
-- Sets

data ASet b =
  ASet
  { _eltNames :: [Name]
  , _setColor :: Colour Double
  }
  deriving Show

$(makeLenses ''ASet)

instance Qualifiable (ASet b) where
  n .>> s = s & eltNames %~ (n .>>)

newtype Set b = Set { setParts :: [ASet b] }

collapse :: Set b -> ASet b
collapse (Set as) = ASet
  { _eltNames = concatMap (view eltNames) as
  , _setColor = head as ^. setColor
  }

instance Singleton (Set b) where
  type Single (Set b) = ASet b
  single s = Set [s]

instance Par (Set b) where
  empty = Set []
  pars  = Set . disjointly concat . map setParts

nset :: Int -> Colour Double -> Set b
nset n = set [0::Int .. (n-1)]

set :: IsName n => [n] -> Colour Double -> Set b
set ns c = single $ ASet (map toName ns) c

drawSet :: _ => Set b -> Diagram b
drawSet = centerY . vcat . map drawAtomic . annot . annot . setParts
  where
    annot = reverse . zip (False : repeat True)
    drawAtomic (bot, (top, ASet nms c))
      = mconcat
        [ vcat' (with & sep .~ 1 & catMethod .~ Distrib)
          (zipWith named nms (replicate (length nms) dot))
          # centerY
        , roundedRect' 1 (fromIntegral (length nms))
          (with & radiusTL .~ (if top then 0 else (1/2))
                & radiusTR .~ (if top then 0 else (1/2))
                & radiusBL .~ (if bot then 0 else (1/2))
                & radiusBR .~ (if bot then 0 else (1/2))
          )
          # fcA (c `withOpacity` 0.5)
        ]

------------------------------------------------------------
-- Bijections

data ABij b
  = ABij
    { _bijDomain :: [Name]
    , _bijRange  :: [Name]
    , _bijData   :: Name -> Maybe Name
    , _bijData'  :: Name -> Maybe Name
    , _bijStyle  :: Name -> Style V2 Double
    , _bijStyle' :: Name -> Style V2 Double
    }

makeLenses ''ABij

instance Qualifiable (ABij b) where
  n .>> bij = bij
            & bijData   %~ prefixF n
            & bijData'  %~ prefixF n
            & bijDomain %~ (n .>>)
            & bijRange  %~ (n .>>)
    where
      prefixF :: IsName a => a -> (Name -> Maybe Name) -> (Name -> Maybe Name)
      prefixF _ _ (Name [])     = Just $ Name []
      prefixF i f (Name (AName a : as)) =
        case cast a of
          Nothing -> Nothing
          Just a' -> if a' == i then (i .>>) <$> f (Name as) else Nothing

toNameI :: Int -> Name
toNameI = toName

toNamesI :: [Int] -> [Name]
toNamesI = map toName

bijFun :: [Int] -> (Int -> Maybe Int) -> ABij b
bijFun is f
  = def
  & bijDomain .~ toNamesI is
  & bijRange  .~ toNamesI (catMaybes $ map f is)
  & bijData   .~ fmap toName . f . extractInt 0
  & bijData'  .~ fmap toName . (\m -> find (\n -> f n == Just m) is) . extractInt 0

extractInt :: Int -> Name -> Int
extractInt i (Name []) = i
extractInt i (Name ns)
  = case last ns of
      AName a -> case cast a of
        Nothing -> i
        Just i' -> i'

bijTable :: [(Name, Name)] -> ABij b
bijTable tab = def
  & bijDomain .~ map fst tab
  & bijRange  .~ map snd tab
  & bijData   .~ tableToFun tab
  & bijData'  .~ tableToFun (map swap tab)

mkABij :: Set b -> Set b -> (Int -> Int) -> ABij b
mkABij s1 s2 f
  = def & bijDomain .~ (a1 ^. eltNames)
        & bijRange  .~ (a2 ^. eltNames)
        & bijData   .~ (\x -> do
            n <- findIndex (==x) (a1 ^. eltNames)
            (a2 ^. eltNames) !!! f n)
        & bijData'  .~ (\y -> do
            m <- findIndex (==y) (a2 ^. eltNames)
            n <- findIndex (\n -> f (extractInt 0 n) == m) (a1 ^. eltNames)
            (a1 ^. eltNames) !!! n)
  where
    a1 = collapse s1
    a2 = collapse s2

-- mkBij :: Set -> Set -> (Int -> Int) -> Bij
-- mkBij ss1 ss2 f = undefined

(!!!) :: [a] -> Int -> Maybe a
[] !!! _     = Nothing
(x:_) !!! 0  = Just x
(_:xs) !!! n = xs !!! (n-1)

tableToFun :: Eq a => [(a, b)] -> a -> Maybe b
tableToFun = flip lookup

instance Default (ABij b) where
  def = ABij
    { _bijDomain = []
    , _bijRange  = []
    , _bijData   = const Nothing
    , _bijData'  = const Nothing
    , _bijStyle  = defaultStyle
    , _bijStyle' = defaultStyle
    }
    where
      defaultStyle = const $ mempty # dashingL [0.2,0.1] 0 # lineCap LineCapButt

data Bij b = Bij { _bijParts :: [ABij b]
                 , _bijSep    :: Double
                 , _bijLabel  :: Maybe (Diagram b)
                 }

makeLenses ''Bij

instance Singleton (Bij b) where
  type Single (Bij b) = ABij b
  single b = Bij [b] 3 Nothing

instance Par (Bij b) where
  empty    = Bij [with & bijData .~ const Nothing] 3 Nothing
  pars  bs = Bij parts s Nothing
    where
      parts = disjointly concat . map (^.bijParts) $ bs
      s     = maximum . map (^. bijSep) $ bs

labelBij :: _ => String -> Bij b -> Bij b
labelBij s = bijLabel .~ Just (text s # fontSizeL 0.8 <> square 0.8 # lw 0)

------------------------------------------------------------
-- Reversible things

instance Reversing (ABij b) where
  reversing b =
    b & bijDomain .~ (b ^. bijRange)
      & bijRange  .~ (b ^. bijDomain)
      & bijData   .~ (b ^. bijData')
      & bijData'  .~ (b ^. bijData)
    -- bijStyle???

instance Reversing (Bij b) where
  reversing = bijParts . mapped %~ reversing

------------------------------------------------------------
-- Alternating lists

data AltList a b
  = Single a
  | Cons a b (AltList a b)

instance Singleton (AltList a b) where
  type Single (AltList a b) = a
  single = Single

infixr 5 .-, -., -.., +-

(.-) :: a -> (b, AltList a b) -> AltList a b
a .- (b,l) = Cons a b l

(-.) :: b -> AltList a b -> (b, AltList a b)
(-.) = (,)

(-..) :: b -> a -> (b,AltList a b)
b -.. a = (b, Single a)

(+-) :: AltList a b -> (b, AltList a b) -> AltList a b
(+-) l = uncurry (concatA l)

zipWithA :: (a1 -> a2 -> a3) -> (b1 -> b2 -> b3) -> AltList a1 b1 -> AltList a2 b2 -> AltList a3 b3
zipWithA f _ (Single x1) (Single x2)         = Single (f x1 x2)
zipWithA f _ (Single x1) (Cons x2 _ _)       = Single (f x1 x2)
zipWithA f _ (Cons x1 _ _) (Single x2)       = Single (f x1 x2)
zipWithA f g (Cons x1 y1 l1) (Cons x2 y2 l2) = Cons (f x1 x2) (g y1 y2) (zipWithA f g l1 l2)

concatA :: AltList a b -> b -> AltList a b -> AltList a b
concatA (Single a) b l     = Cons a b l
concatA (Cons a b l) b' l' = Cons a b (concatA l b' l')

flattenA :: AltList (AltList a b) b -> AltList a b
flattenA (Single l) = l
flattenA (Cons l b l') = concatA l b (flattenA l')

instance Bifunctor AltList where
  first f (Single a) = Single (f a)
  first f (Cons a b l) = Cons (f a) b (first f l)

  second _ (Single a) = Single a
  second g (Cons a b l) = Cons a (g b) (second g l)

zipWith2 :: (x -> b -> c) -> [x] -> AltList a b -> AltList a c
zipWith2 _ _  (Single a)       = Single a
zipWith2 _ [] (Cons a _ _)     = Single a
zipWith2 f (x:xs) (Cons a b l) = Cons a (f x b) (zipWith2 f xs l)

iterateA :: (a -> b) -> (b -> a) -> a -> AltList a b
iterateA f g a = Cons a b (iterateA f g (g b))
  where b = f a

takeWhileA :: (b -> Bool) -> AltList a b -> AltList a b
takeWhileA _ (Single a) = Single a
takeWhileA p (Cons a b l)
  | p b = Cons a b (takeWhileA p l)
  | otherwise = Single a

foldA :: (a -> r) -> (a -> b -> r -> r) -> AltList a b -> r
foldA f _ (Single a)   = f a
foldA f g (Cons a b l) = g a b (foldA f g l)

evens :: Traversal (AltList a b) (AltList a' b) a a'
evens g (Single a)   = Single <$> g a
evens g (Cons a b l) = Cons <$> g a <*> pure b <*> evens g l

odds :: Traversal (AltList a b) (AltList a b') b b'
odds _ (Single a)   = pure (Single a)
odds g (Cons a b l) = Cons <$> pure a <*> g b <*> odds g l

------------------------------------------------------------
-- Bijection complexes

type BComplex b = AltList (Set b) (Bij b)

labelBC :: _ => [String] -> BComplex b -> BComplex b
labelBC = zipWith2 labelBij

seqC :: BComplex b -> Bij b -> BComplex b -> BComplex b
seqC = concatA

instance Par (BComplex b) where
  empty = single empty
  (+++) = zipWithA (+++) (+++)

drawBComplex :: _ => BComplex b -> Diagram b
drawBComplex = centerX . drawBComplexR 0
  where
    drawBComplexR i (Single s) = i .>> drawSet s
    drawBComplexR i (Cons ss b c) =
        hcat
        [ i .>> s1
        , strutX (b ^. bijSep) <> label
        , drawBComplexR (succ i) c
        ]
        # applyAll (map (drawABij i (map fst $ names s1)) bs)
      where
        bs = b ^. bijParts
        s1 = drawSet ss
        label = (fromMaybe mempty (b ^. bijLabel))
                # (\d -> d # withEnvelope (strutY (height d) :: D V2 Double))
                # (\d -> translateY (-(height s1 + height d)/2) d)

drawABij :: _ => Int -> [Name] -> ABij b -> Diagram b -> Diagram b
drawABij i ns b = applyAll (map conn . catMaybes . map (_2 id . (id &&& (b ^. bijData))) $ ns)
  where
    -- conn :: (Name,Name) -> Diagram b -> Diagram b
    conn (n1,n2) = withNames [i .>> n1, (i+1) .>> n2] $ \[s1,s2] -> atop (drawLine s1 s2 # applyStyle (sty n1))
    sty = b ^. bijStyle
    drawLine sub1 sub2 = boundaryFrom sub1 v ~~ boundaryFrom sub2 (negated v)
      where
        v = location sub2 .-. location sub1

------------------------------------------------------------
-- Computing orbits/coloration

type Edge a = (a,a)

type Relator a = (a,[a],a)

mkRelator :: Edge a -> Relator a
mkRelator (n1,n2) = (n1,[],n2)

start :: Relator a -> a
start (n,_,_) = n

end :: Relator a -> a
end (_,_,n) = n

relatorToList :: Relator a -> [a]
relatorToList (a,bs,c) = a : bs ++ [c]

isTailOf :: Eq a => Relator a -> Relator a -> Bool
isTailOf r1 r2 = relatorToList r1 `isSuffixOf` relatorToList r2 && r1 /= r2

composeRelators :: Eq a => Relator a -> Relator a -> Maybe (Relator a)
composeRelators (s1,ns1,e1) (s2,ns2,e2)
  | e1 == s2  = Just (s1,ns1++[e1]++ns2,e2)
  | otherwise = Nothing

type Relation a = [Relator a]

mkRelation :: [Edge a] -> Relation a
mkRelation = map mkRelator

emptyR :: Relation a
emptyR = []

unionR :: Relation a -> Relation a -> Relation a
unionR = (++)

unionRs :: [Relation a] -> Relation a
unionRs = concat

composeR :: Eq a => Relation a -> Relation a -> Relation a
composeR rs1 rs2 = [ rel | rel1 <- rs1, rel2 <- rs2, Just rel <- [composeRelators rel1 rel2] ]

orbits :: Eq a => Relation a -> Relation a -> Relation a
orbits r1 r2 = removeTails $ orbits' r2 r1 r1
  where
    orbits' _  _  [] = []
    orbits' r1 r2 r  = done `unionR` orbits' r2 r1 (r' `composeR` r1)
      where
        (done, r') = partition finished r
        finished rel = (start rel == end rel) || all ((/= end rel) . start) r1
    removeTails rs = filter (\r -> not (any (r `isTailOf`) rs)) rs

bijToRel :: Bij b -> Relation Name
bijToRel = unionRs . map bijToRel1 . view bijParts
  where
    bijToRel1 bij = mkRelation . catMaybes . map (_2 id . (id &&& (bij^.bijData))) $ bij^.bijDomain

orbitsToColorMap :: Ord a => [Colour Double] -> Relation a -> M.Map a (Colour Double)
orbitsToColorMap colors orbs = M.fromList (concat $ zipWith (\rel c -> map (,c) rel) (map relatorToList orbs) (cycle colors))

colorBij :: M.Map Name (Colour Double) -> Bij b -> Bij b
colorBij colors = bijParts . mapped %~ colorBij'
  where
    colorBij' bij = bij & bijStyle .~ \n -> maybe id lc (M.lookup n colors) ((bij ^. bijStyle) n)

------------------------------------------------------------
-- Example sets and bijections

-- See http://mkweb.bcgsc.ca/colorblind/img/colorblindness.palettes.trivial.png
--
-- These colors should be perceptible as distinct by most people with
-- some form of colorblindness.
colors =
  [ sRGB24   0 114 178   -- blue
  , sRGB24  86 180 233   -- sky blue
  , sRGB24 213  94   0   -- vermillion
  , sRGB24 230 159   0   -- orange
  , sRGB24   0 158 115   -- bluish green
  , sRGB24 204 121 167   -- reddish purple
  ]

a0, b0, a1, b1 :: _ => Set b
a0 = nset 3 (colors !! 0)
b0 = nset 3 (colors !! 1)

a1 = nset 2 (colors !! 2)
b1 = nset 2 (colors !! 3)

bc0, bc1, bc01 :: _ => BComplex b
bc0 = a0 .- bij0 -.. b0
bc1 = a1 .- bij1 -.. b1
bc01 = bc0 +++ bc1

bc01' :: _ => BComplex b
bc01' = bc01 +- (reversing bij0 +++ empty) -.. (a0 +++ a1)

bij0, bij1 :: _ => Bij b
bij0 = single $ mkABij a0 b0 ((`mod` 3) . succ . succ)
bij1 = single $ mkABij a1 b1 id

colorEdge :: _ => Name -> Colour Double -> Bij b -> Bij b
colorEdge n c = bijParts . traverse . bijStyle
  %~ \sty n' -> if (n' == n) then (sty n' # lc c # lw thick) else sty n'

------------------------------------------------------------
-- Generalized bijection diagrams

type GenBij l = AltList (GSet l) (Link l, l)

data GSet l
  = SingleGSet l
  | GSum (GSet l) (GSet l)

data Link l
  = PrimLink
  | ManyLink [(l,l)]

drawGenBij :: _ => (l -> Diagram b) -> GenBij l -> Diagram b
drawGenBij drawLabel = go 0
  where
    go :: Int -> _ -> _
    go i (Single gset)       = i .>> drawGSet gset
    go i (Cons gset (lk,l) rest) = hcat
      [ i .>> gsetD
      , strutX 1 <> label
      , go (i+1) rest
      ]
      where
        gsetD = drawGSet gset
        label = drawLabel l
                -- # (\d -> d # withEnvelope (strutY (height d) :: D V2 Double))
                -- # (\d -> translateY (-(height s1 + height d)/2) d)

    drawGSet (SingleGSet l) = drawLabel l <> rect 1 1 # named l
    drawGSet (GSum s1 s2)   = drawGSet s1 === drawGSet s2
