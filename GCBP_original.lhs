% A tale of two bijection principles (part 1)

In my work on species I've recently been thinking about various ways
of constructing bijections.  Two particular constructions that have
come up are the *Gordon complementary bijection principle* (hereafter
GCBP) and the *Garsia-Milne involution principle* (hereafter GMIP),
which I will explain below.  As you will see, they have a very similar
feel---especially their proofs.  I learned about them both in the same
lecture (by [Jason
Bandlow](https://plus.google.com/106055648571508594246)) several years
ago, and GMIP was presented as a generalization of GCBP, though
without proof.  In fact, in the original presentation of his
complementary bijection principle, Gordon tantalizingly states that
the two principles are *equivalent* XXX cite---again without proof.
But though they "feel" similar, they are different enough on the
surface that it is not immediately apparent what the relationship is
between the two.  I looked but could not find any formal exposition of
their relationship (with the possible exception of Feldman and Propp
XXX cite., though XXX).  Finally, after staring at them for a couple
days, I figured out how to prove that they are, in fact, equivalent.
Perhaps this is obvious to combinatoricists, but I thought it worth
writing up, especially because it's an excuse to make some pretty
pictures.

Subtracting bijections
----------------------

Suppose we have sets $A_0, A_1, B_0, B_1$ with bijections $f_0 : A_0
\leftrightarrow B_0$ and $f_1 : A_1 \leftrightarrow B_1$.  Then it's
clear how to construct a bijection $f : A_0 + A_1 \leftrightarrow B_0
+ B_1$ (where $+$ denotes the coproduct, *i.e.* disjoint union, of
sets): we just take $f = f_0 + f_1$, like this:

```{.dia width='300'}
import Bijections

dia =
  (vcat' (with & sep .~ 1) . map centerX)
  [ hcat' (with & sep .~ 2)
    [ drawBComplex $ bc0 # labelBC "f₀"
    , plus
    , drawBComplex $ bc1 # labelBC "f₁"
    ]
  , equals
  , drawBComplex $ parC bc0 bc1 # labelBC "f = f₀ + f₁"
  ]
  # centerXY # pad 1.1
  # sized (Width 2)
```

So we can compute the sum of two bijections. What about the
*difference*?  That is, given $f : A_0 + A_1 \leftrightarrow B_0 +
B_1$ and $f_1 : A_1 \leftrightarrow B_1$, can we compute some $f_0 :
A_0 \leftrightarrow B_0$?

```{.dia width='300'}
import Bijections
import Control.Lens ((&), (.~))

dia =
  (vcat' (with & sep .~ 1) . map centerX)
  [ hcat' (with & sep .~ 2)
    [ drawBComplex $
      [a0,a1] .- bij01 # labelBij "f" -.. [b0,b1]
    , minus
    , drawBComplex $ bc1 # labelBC "f₁"
    ]
  , equals
  , mconcat
    [ text' 3 "?"
    , drawBComplex $ [a0] .- emptyBij # labelBij "f₀" -.. [b0]
    ]
  ]
  # centerXY # pad 1.1
  # sized (Width 2)
```

Though it is obvious that $|A_0| = |B_0|$, it is not *a priori*
obvious whether it is possible to construct an actual *bijection*
between them. (Of course, in a classical setting, we could say that
there must *exist* bijections between any two finite sets of the same
size---but we are doing *constructive* mathematics here.  We want a
real, honest-to-goodness bijection that we can compute with.)  The
problem, as can be seen in the above illustration, is that $f$ may mix
up elements among the $A_i$ and $B_i$---that is, we cannot just, say,
take the restriction of $f$ to $A_0$, since the image of $A_0$ under
$f$ may intersect both $B_0$ and $B_1$.

However, it turns out that this *is* possible, and the GCBP gives us an
explicit construction.  You might want to stop and think about it for
a while at this point.  If you know some Haskell, try filling in the
definition of `subtractIso`:

> {-# LANGUAGE TypeOperators #-}
>
> import Prelude hiding ((.), id)
> import Control.Category
>
> data a :<->: b = (a -> b) :<->: (b -> a)
>   -- Invariant: the two functions are inverse.
>
> applyIso :: (a :<->: b) -> (a -> b)
> applyIso (f :<->: _) = f
>
> invert :: (a :<->: b) -> (b :<->: a)
> invert (f :<->: g) = (g :<->: f)
>
> instance Category (:<->:) where
>   id = id :<->: id
>   (f1 :<->: g1) . (f2 :<->: g2) = (f1 . f2) :<->: (g2 . g1)
>
> subtractIso :: (Either a0 a1 :<->: Either b0 b1) -> (a1 :<->: b1) -> (a0 :<->: b0)
> subtractIso = undefined

The Gordon complementary bijection principle
--------------------------------------------

Instead of defining the GCBP via a bunch of symbols, or even by exhibiting
some code, I will begin by *drawing* it for you:

```{.dia width='450'}
import           Bijections
import           Control.Lens ((&), (.~))

gcbp = drawBComplex . flattenA $
    bc01' .- ebij1 -. bc01' .- ebij1 -.. bc01'
  where
    ebij1 = colorBij colorMap $
            emptyBij `parBij` (bij1 & labelBij "f₁⁻¹")
    bc01' = map2 (colorBij colorMap . labelBij "f") bc01
    colorMap = orbitsToColorMap
                 [red, green, blue, orange, purple]
                 (orbits
                   (bijToRel bij01)
                   (bijToRel ebij1)
                 )

gcbpEqn =
  (vcat' (with & sep .~ 1) . map centerX)
  [ hcat' (with & sep .~ 2)
    [ drawBComplex $
      [a0,a1] .- bij01 # labelBij "f" -.. [b0,b1]
    , minus
    , drawBComplex $ bc1 # labelBC "f₁"
    ]
  , equals
  , gcbp
  ]

-- XXX draw resulting bijection

dia = gcbpEqn
  # centerXY # pad 1.1
  # sized (Width 2)
```

Here's the idea in words: start with an element in $A_0$ (that's the
yellow set in the illustration above), and apply $f$.  If we get something in $B_0$ (blue),
great---we're done!  Otherwise, we have something in $B_1$ (red), so
we apply $f_1^{-1}$ to send us back over to $B_0$ (green), and from
there we apply $f$ again and repeat.  In the above example, you can
see that the first two elements of $A_0$ land in $B_0$ immediately;
for the third, we have to iterate three times (or perhaps we should
say "two and a half times").

Here's a more complicated example:

```{.dia width='450'}
import Bijections
import Control.Lens ((&), (.~))
import Data.Bits (xor)
import Data.Typeable (cast)
import Diagrams.Core.Names

a2 = nset 4 yellow
b2 = nset 4 blue
a3 = nset 5 green
b3 = nset 5 red

bc3 = [a3] .- bij3 -.. [b3]

bij3 = [bijFun [0..4] (Just . (\n -> if n == 4 then 4 else xor 1 n))]

bij23 = [with & bijData .~ tableToFun tab23]
tab23 = zip (('a' |> toNamesI [0..3]) ++ ('b' |> toNamesI [0..4]))
            [ 'b' |@ 0, 'a' |@ 0, 'b' |@ 1, 'a' |@ 1
            , 'b' |@ 2, 'a' |@ 2, 'b' |@ 3, 'b' |@ 4, 'a' |@ 3
            ]

bc23 = [a2,a3] .- bij23 -.. [b2,b3]

gcbp = drawBComplex . flattenA $
  bc23' .- ebij3 -. bc23' .- ebij3 -. bc23' .- ebij3 -.. bc23'
  where
    ebij3 = emptyBij `parBij` (bij3 & labelBij "f₁⁻¹")
    bc23' = map2 (labelBij "f") bc23

gcbpEqn =
  (vcat' (with & sep .~ 1) . map centerX)
  [ hcat' (with & sep .~ 2)
    [ drawBComplex $
      [a2,a3] .- bij23 # labelBij "f" -.. [b2,b3]
    , minus
    , drawBComplex $ bc3 # labelBC "f₁"
    ]
  , equals
  , gcbp
  ]

dia = gcbpEqn
  # centerXY # pad 1.1
  # sized (Width 2)

```

We need to show that this gives a well-defined bijection---that it
terminates, first of all, and that it gives us a mapping which really
is a bijection.

The "usual" proof goes something like this: XXX

However, we can apprehend the validity of the GCBP more directly and
intuitively.  Consider "extending to infinity" the iteration in both
directions.

XXX picture.

Since we have created this picture by simply copying the same
bijections over and over, it obviously has translational
symmetry---moving it one unit to the left or right doesn't change
anything.  Let's consider the different types of paths that show up in
this kind of picture.

First, can there be bi-infinite paths?  Sure, there can be, but any
such path must necessarily stay entirely within the bottom half of the
picture, since the top half of the picture only contains *ends* of
paths.  Since our goal is to construct a bijection between the top
sets we can therefore ignore bi-infinite paths.

Can there be *half*-infinite paths, *i.e.* paths which have a starting
point in the top half of the picture but then wander around in the
bottom half forever?  No, because XXX it will intersect its copies
(explain this better).  Therefore, every path that is not bi-infinite
must have two endpoints in the top half of the picture.

Finally, it's easy to see that every point belongs to a unique
path. (XXX why?)

The GCBP in Haskell
-------------------

Here's my implementation of `subtractIso`:

> subtractIso' :: (Either a0 a1 :<->: Either b0 b1) -> (a1 :<->: b1) -> (a0 :<->: b0)
> subtractIso' a0a1__b0b1 a1__b1 =
>     (iter (applyIso a0a1__b0b1) (applyIso $ invert a1__b1) . Left)
>     :<->:
>     (iter (applyIso $ invert a0a1__b0b1) (applyIso $ a1__b1) . Left)
>   where
>     iter a0a1_b0b1 b1_a1 a0a1 =
>       case a0a1_b0b1 a0a1 of
>         Left  b0 -> b0
>         Right b1 -> iter a0a1_b0b1 b1_a1 (Right (b1_a1 b1))

It feels sort of ugly---in fact, it is the exact computational
analogue of the usual proof of the GCBP (though it's missing quite a
bit, in particular a proof of termination and a proof that the output
really is a bijection).  Given that I don't like the usual proof, it's
no surprise that I find this code ugly.  I don't like the fact that it
projects functions out of the input bijections and uses them to
construct the two directions of the output bijection separately.  I'd
rather work entirely in terms of operations on bijections.  I don't
know whether that is possible.  I'd be very interested to see what
others come up with.

The Garsia-Milne involution principle
-------------------------------------

Further reading
---------------

XXX Cite Garsia-Milne paper(s).  Don't recommend actually reading
it/them.

Came out of trying to prove partition identities. XXX cite Wilf paper
tying a bunch of this together.
