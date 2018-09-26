% -*- mode: LaTeX; compile-command: "./build.sh" -*-

\documentclass[xcolor={usenames,dvipsnames,svgnames,table},12pt,aspectratio=169]{beamer}

%include polycode.fmt

%format Either = "\Tycon{Either}"

%format ...  = "\dots"

%format a    = "\SetA{a}"
%format a'   = "\SetAP{a^{\prime}}"
%format b    = "\SetB{b}"
%format b'   = "\SetBP{b^{\prime}}"

%format <$> = "\mathbin{\langle \$ \rangle}"

%format >=> = ">\!\!=\!\!\!>"
%format <=< = "<\!\!\!=\!\!<"
%format +++ = "+\!\!+\!\!+"
%format >>> = "\andthen"
%format ||| = "+"

%format <== = "\sqsubseteq"
%format ==> = "\sqsupseteq"

%format ^   = "^"

%format ^^  = "\;"

%format <=>   = "\leftrightarrow"
%format <==>  = "\leftrightarrow"
%format <->   = "\rightleftharpoons"
%format <-->  = "\rightleftharpoons"
%format :<=>: = "\mathbin{:\leftrightarrow:}"
%format :<->: = "\mathbin{:\rightleftharpoons:}"

%format ^.    = "\odot"

%format inv(a) = "\overline{" a "}"
%format inverse(a) = "\overline{" a "}"
%format leftPartial(f) = "\big\langle" f "\,\big|"
%format rightPartial(f) = "|" f "\rangle"

%format Kleisli(m)(a)(b) = a "\to_{" m "}" b
%format Bij(m)(a)(b) = a <~> "_{" m "}" b

%% XXX
%format <~>   = "\mathbin{\leftrightsquigarrow}"

%format undef = "\varnothing"
%format <||>  = "\mrg"

%%% TODO -- better notation?
%format <|>   = "\diamond"

\newcommand{\id}[1]{\textsf{\textsl{#1}}}
\renewcommand{\onelinecomment}{--- \itshape}
\renewcommand{\Varid}[1]{\id{#1}}
\renewcommand{\Conid}[1]{\textcolor{OliveGreen}{\id{#1}}}
\newcommand{\Tycon}[1]{\textcolor{Purple}{\id{#1}}}

\definecolor{SetABlue}{RGB}{0,114,255}
\definecolor{SetAPBlue}{RGB}{86,180,233}
\definecolor{SetBOrange}{RGB}{213,94,0}
\definecolor{SetBPOrange}{RGB}{230,159,0}

\newcommand{\SetA}[1]{\textcolor{SetABlue}{#1}}
\newcommand{\SetAP}[1]{\textcolor{SetAPBlue}{#1}}
\newcommand{\SetB}[1]{\textcolor{SetBOrange}{#1}}
\newcommand{\SetBP}[1]{\textcolor{SetBPOrange}{#1}}

\newcommand{\andthen}{\mathbin{;}}
\newcommand{\parsum}{+}

\mode<presentation>
{
  \usetheme{default}                          % use a default (plain) theme

  \setbeamertemplate{navigation symbols}{}    % don't show navigation
                                              % buttons along the
                                              % bottom
  \setbeamerfont{normal text}{family=\sffamily}

%  \setbeamertemplate{footline}[frame number]

  \AtBeginSection[]
  {
    \begin{frame}<beamer>
      \frametitle{}
      \begin{center}
        {\Huge \insertsectionhead}

        \vspace{0.25in}
        \includegraphics[width=2in]{\secimage}
      \end{center}
    \end{frame}
  }
}

\newcommand{\secimage}{yuk.jpg}

\newenvironment{xframe}[1][]
  {\begin{frame}[fragile,environment=xframe,#1]}
  {\end{frame}}

% uncomment me to get 4 slides per page for printing
% \usepackage{pgfpages}
% \pgfpagesuselayout{4 on 1}[uspaper, border shrink=5mm]

\setbeameroption{show only notes}

\usepackage[english]{babel}
\usepackage[T1]{fontenc}
\usepackage{graphicx}
\graphicspath{{images/}}

\usepackage{ulem}
\usepackage{url}
\usepackage{fancyvrb}

\usepackage{pgf}
\usepackage[outputdir=diagrams,backend=pgf,extension=pgf,input]{diagrams-latex}

\title{What's the Difference? \\ \small{A Functional Pearl on Subtracting Bijections}}
\date{ICFP 2018 St.\ Louis}
\author{Brent Yorgey, Hendrix College \\ Kenny Foner, University of Pennsylvania}

% XXX some kind of fun image of bijections etc. on first slide

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

  \begin{frame}{}
    \titlepage
   \begin{center}
     \includegraphics[height=0.4in]{Hendrix}
     \includegraphics[height=0.4in]{plclub}
   \end{center}
   % \hfill
   % \includegraphics[width=0.5in]{plclub.png}
  \end{frame}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=150]
        import Bijections
        dia = drawBComplex (bc0 & labelBC ["$f$"])
      \end{diagram}
    \end{center}

    \note{This is a bijection.  It matches up the elements of these
      two blue sets in such a way that each element is matched with
      exactly one element from the other set.
    }
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=150]
        import Bijections
        dia = drawBComplex (bc1 & labelBC ["$g$"])
      \end{diagram}
    \end{center}

    \note{And here is another bijection.}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
    \begin{diagram}[width=250]
      import Bijections

      dia = vsep 1 . map centerX $  -- $
        [ hsep 3
          [ drawBComplex (bc0 & labelBC ["$f$"])
          , text "$+$"
          , drawBComplex (bc1 & labelBC ["$g$"])
          ]
        , hsep 3
          [ text "$=$"
          , drawBComplex (bc01 & labelBC ["$f + g$"])
          ]
        ]
    \end{diagram}
    \end{center}

    \note{Given these two bijections, we can \emph{add} them by
      running them in parallel, so to speak.  That is, I take the
      disjoint union of the dark blue and dark orange sets, and the
      disjoint union of the light blue and light orange sets, and I
      get a new bijection between these disjoint unions, which does
      $f$ on one side and $g$ on the other.}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
    \begin{diagram}[width=100]
      import Bijections

      dia = vsep 1 . map centerX $  -- $
        [ hsep 3
          [ drawBComplex (bc0 & labelBC ["$f$"])
          , text "$+$"
          , drawBComplex (bc1 & labelBC ["$g$"])
          ]
        , hsep 3
          [ text "$=$"
          , drawBComplex (bc01 & labelBC ["$f + g$"])
          ]
        ]
    \end{diagram}
    \end{center}
    \begin{code}
      (+) :: (a -> a') -> (b -> b') -> (Either a b -> Either a' b')
      (f + g) (Left a)   = Left   (f a)
      (f + g) (Right b)  = Right  (g b)
    \end{code}
    \note{Just to be concrete, here's some Haskell code which
      expresses one direction of this operation on bijections.  Given
      a function from $a$ to $a'$---representing just the forward
      direction of the bijection $f$---and a function from $b$ to
      $b'$, the new bijection relates the disjoint union of $a$ and
      $b$ to the disjoint union of $a'$ and $b'$. In the forward
      direction, this bijection works by doing a case analysis on its
      input to see which ``side'' it comes from, |Left| or |Right|,
      and then running the appropriate function.}
  \end{xframe}

  {
    \renewcommand{\secimage}{grass}
    \section{Ground rules}
    \note{I need to stop at this point to establish some ground rules
      for the rest of my talk.}
  }

  \begin{xframe}{}
    \begin{center}
      \onslide<1->
      1. ``type'' = ``set'' \\[1em]
      \onslide<2>
      2. everything is finite
    \end{center}
    \note{Rule number 1: types and sets are the
      same thing. I am going to use these words interchangeably.  Rule
      number 2: everything is finite. OK? After my talk we can all go
      back to our comfortable world where things can be infinite, and
      types and sets are definitely not the same.}
  \end{xframe}

  {
    \renewcommand{\secimage}{apples}
    \section{Subtraction}
    \note{Now let's talk about subtraction.}
  }

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=150]
        import Bijections
        dia = drawBComplex (bc2 # labelBC ["$h$"])
      \end{diagram}
    \end{center}
    \note{OK. Now, suppose we \emph{start} with a bijection between
      two sum types.  So here is a bijection $h$ from, say, $a + b$,
      to $a' + b'$.  Notice that $h$ does not send every element in
      the top left to the top right, nor bottom left to bottom right.
      It can arbitrarily ``mix'' top and bottom.  Put another way, $h$
      is not the sum of two bijections on the blue and orange sets.}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=150]
        import Bijections
        dia = drawBComplex (bc1 # labelBC ["$g$"])
      \end{diagram}
    \end{center}
    \note{Now let's take our same $g$ again.}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=250]
        import Bijections

        dia = vsep 1 . map centerX $  -- $
          [ hsep 3
            [ drawBComplex (bc2 # labelBC ["$h$"])
            , text "$-$" # translateY (-2.5)
            , drawBComplex (bc1 # labelBC ["$g$"]) # translateY (-2.5)
            ]
          , hsep 3
            [ text "$=$"
            , drawBComplex ((a0 .- empty -.. b0))
              <>
              text "?"
            ]
          ]
        \end{diagram}
        \note{Since we can \emph{add} two bijections, the natural
          question is---can we \emph{subtract} them as well?  Now at
          this point it may not even be clear what this should mean,
          especially since we just said $h$ is not a sum of
          bijections. One thing we can say for sure is that the blue
          sets must have the same size, since $h$ shows that the
          disjoint unions have the same size, and $g$ shows that the
          orange sets have the same size. So there \emph{must exist}
          some bijection between the blue sets.  But this isn't good
          enough for me.  I don't just want to know they have the same
          size, I want a \emph{concrete matching} between the blue
          sets that I can actually compute.}
    \end{center}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=250]
        import Bijections

        dia = vsep 1 . map centerX $  -- $
          [ hsep 3
            [ drawBComplex (bc2 # labelBC ["$h$"])
            , text "$-$" # translateY (-2.5)
            , drawBComplex (bc1 # labelBC ["$g$"]) # translateY (-2.5)
            ]
          , hsep 3
            [ text "$=$"
            , drawBComplex ((a0 .- empty -.. b0))
              <>
              text "?"
            ]
          ]
        \end{diagram}
      \end{center}
      XXX if time --- tweak image a bit, e.g. show tiny arrows coming
      out of blue which don't know where to go

      \note{So the name of the game is to somehow use the information
        contained in $h$ and $g$ to find some canonical way to match
        up the elements of the blue sets.  Of course in this case we
        can just look at these sets and arbitrarily decide how to
        match them up, but our goal is to come up with a general
        principle that tells us which elements we should match by
        looking only at $h$ and $g$.

        OK, I want you to turn to your
        neighbor and see if you can figure out how to do this.  You
        have sixty seconds, starting\dots now!}
  \end{xframe}

  {
    \renewcommand{\secimage}{background}
    \section{Background}
    \note{Before I explain the answer, I want to stop to give a bit of
      context.}
  }

  \begin{xframe}{}
    \note{Why might one care about this problem?  Comes up in
      combinatorics, the mathematical study of counting things.  XXX}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      Garsia-Milne (1981), Gordon (1983)
    \end{center}
    \note{The problem was first solved by Garsia and Milne, and later
      in a different form by Gordon.  Both actually proved much more
      general things than what we will talk about here; ask me later
      if you're interested.}
  \end{xframe}

  {
    \renewcommand{\secimage}{Pong}
    \section{Ping-pong}
    \note{So now I want to explain the solution.}
  }

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=150]
        import Bijections

        dia :: Diagram B
        dia = drawBComplex (bc2 # labelBC ["$h$"])
      \end{diagram}
    \end{center}
    \note{Let's start by looking at $h$ again.}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=150]
        import Bijections

        dia :: Diagram B
        dia = drawBComplex (bc2 # labelBC ["$h$"])
          # select 0 0
      \end{diagram}
    \end{center}
    XXX if time highlight edges
    \note{If we start with this element and follow $h$ across\dots}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=150]
        import Bijections

        dia :: Diagram B
        dia = drawBComplex (bc2 # labelBC ["$h$"])
          # select 1 2
      \end{diagram}
    \end{center}
    \note{\dots we end up here.  This is where we want to
      be---remember, we're trying to match up the blue sets.}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=150]
        import Bijections

        dia :: Diagram B
        dia = drawBComplex (bc2 # labelBC ["$h$"])
          # select 0 0 # select 1 2
      \end{diagram}
    \end{center}
    \note{So we decide to match up these two elements.}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=150]
        import Bijections

        dia :: Diagram B
        dia = drawBComplex (bc2 # labelBC ["$h$"])
          # select 1 0 # select 2 1
      \end{diagram}
    \end{center}
    \note{Similarly, we can match these two as well.}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=150]
        import Bijections

        dia :: Diagram B
        dia = drawBComplex (bc2 # labelBC ["$h$"])
          # select 2 0
      \end{diagram}
    \end{center}
    \note{What about this one? Of course there's only one element
      left we can pair it with, but let's see if we can figure out a
      principled reason to choose it.}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=150]
        import Bijections

        dia :: Diagram B
        dia = drawBComplex (bc2 # labelBC ["$h$"])
          # select 0 3
      \end{diagram}
    \end{center}
    \note{When we follow $h$ across, we end up in the ``wrong''
      set. What do we do from here?}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=150]
        import Bijections

        dia :: Diagram B
        dia = drawBComplex (bc2 # labelBC ["$\\overline{g}$"])
          # select 0 3
          <>
          drawBComplex bc1 # translateY (-2.5) # lc purple # opacity 0.5
      \end{diagram}
    \end{center}
    \note{Well, remember that we have another bijection, $g$, which
      connects the orange sets.  Let's superimpose it here.  I've
      written $\overline{g}$, denoting the \emph{inverse} of $g$, to
      emphasize that (as you may have already figured out) we're going
      to follow it \emph{backwards}.}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=150]
        import Bijections

        dia :: Diagram B
        dia = drawBComplex (bc2 # labelBC ["$\\overline{g}$"])
          # select 0 1
          <>
          drawBComplex bc1 # translateY (-2.5) # lc purple # opacity 0.5
      \end{diagram}
    \end{center}
    \note{So we follow $g$ backwards and of course we end up in the
      dark orange set.}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=150]
        import Bijections

        dia :: Diagram B
        dia = drawBComplex (bc2 # labelBC ["$h$"])
          # select 1 3
          <>
          drawBComplex bc1 # translateY (-2.5) # lc purple # opacity 0.5
      \end{diagram}
    \end{center}
    \note{But now we can follow $h$ again, to over here.  This still
      isn't where we want to be\dots}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=150]
        import Bijections

        dia :: Diagram B
        dia = drawBComplex (bc2 # labelBC ["$\\overline{g}$"])
          # select 1 1
          <>
          drawBComplex bc1 # translateY (-2.5) # lc purple # opacity 0.5
      \end{diagram}
    \end{center}
    \note{\dots so we follow $g$ backwards again, to here\dots}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=150]
        import Bijections

        dia :: Diagram B
        dia = drawBComplex (bc2 # labelBC ["$h$"])
          # select 0 2
          <>
          drawBComplex bc1 # translateY (-2.5) # lc purple # opacity 0.5
      \end{diagram}
    \end{center}
    \note{Then we follow $h$ again, and finally we end up in the light
      blue set!}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=150]
        import Bijections

        dia :: Diagram B
        dia = drawBComplex (bc2 # labelBC ["$h$"])
          # select 2 0 # select 0 2
          <>
          drawBComplex bc1 # translateY (-2.5) # lc purple # opacity 0.5
      \end{diagram}
    \end{center}
    \note{So we do in fact match up these elements. And we got there
      by sort of ``ping-ponging'' back and forth between the two
      sides, alternately following $h$ and $\overline{g}$.}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=250]
        import Bijections

        dia = vsep 1 . map centerX $  -- $
          [ hsep 3
            [ drawBComplex (bc2 # labelBC ["$h$"])
            , text "$-$" # translateY (-2.5)
            , drawBComplex (bc1 # labelBC ["$g$"]) # translateY (-2.5)
            ]
          , hsep 3
            [ text "$=$"
            , subResult
            ]
          ]

        subResult =
          ( a0 .-
          ( mkABij a0 b0 ((`mod` 3) . succ)
            # single
          ) -..
          b0
          )
          # drawBComplex
      \end{diagram}
    \end{center}
    \note{Overall, then, this is the bijection we get when we subtract
      $g$ from $h$. Since everything is a bijection, and the sets are
      finite, we can't keep ping-ponging forever, we can't get stuck,
      and two different elements on the left can never end up mapping
      to the same element on the right.

      OK, so let's see some code!
    }
  \end{xframe}

  \begin{xframe}{}
    \onslide<1->
    \begin{code}
      pingpong :: (Either a b -> Either a' b') -> (b' -> b) -> (a -> a')
      pingpong h g' = untilLeft (h . Right . g') . h . Left

      untilLeft :: (b' -> a' + b') -> (a' + b' -> a')
      untilLeft step ab = case ab of
        Left   a'  -> a'
        Right  b'  -> untilLeft step (step b')
    \end{code}
    \onslide<2>
    \begin{center}
      \includegraphics[width=1in]{yuk}
    \end{center}
    \note{\dots yuck, right?  This is just about the prettiest I can
      make it.  There are a lot of problems here.  There's a lot of
      noise injecting into and projecting from sum types.  We're
      following individual elements rather than building bijections at
      a high level.  And this is only one direction of the bijection!
      We would need to basically duplicate this code to handle the
      other direction.
    }
  \end{xframe}

  \begin{xframe}{}
    \note{So let's get rid of that ugly code.  Ah, much better!  So,
      Kenny and I set out to see if we could find a way to construct
      this algorithm in a high-level, point-free way.  Why? Partly
      just as a fun challenge, and also to gain insight into the
      algorithm and the related combinatorics. We also hoped it could
      be a first step towards building a formal computer proof.}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      Gu{\dh}mundsson (2017)
    \end{center}
    \note{At the time we started
      working on this, there were no formal computer proofs that we
      knew of; last year Gu{\dh}mundsson completed a formal proof in
      Agda for his master's thesis, though it is pretty tedious, and
      low-level; turning our approach into a higher-level formal proof
      is future work.}
  \end{xframe}

  {
    \renewcommand{\secimage}{high-level}
    \section{High-level ping-pong}
    \note{So let's play some high-level ping-pong.}
  }

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=150]
        import Bijections

        dia :: Diagram B
        dia = drawBComplex (bc2 # labelBC ["$h, \\overline{g}$"])
          <>
          drawBComplex bc1 # translateY (-2.5) # lc purple # opacity 0.5
      \end{diagram}
    \end{center}
    \note{Our first step is to unfold the ping-ponging
      process. Instead of thinking of $h$ and $g$ being superimposed
      and watching elements bounce back and forth\dots}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=300]
        import Bijections
        dia = gcbp
                # labelBC (cycle ["$h$", "$\\overline{g}$"])
                # drawBComplex

        gcbp = (a0 +++ a1) .-
             (bij2 # colorEdge ('a' .> (0 :: Int)) (colors !! 4)
                   # colorEdge ('a' .> (1 :: Int)) (colors !! 4)
                   # colorEdge ('a' .> (2 :: Int)) (colors !! 5)
             ) -.
           (b0 +++ b1) .-
             ( (empty +++ reversing bij1)
               # colorEdge ('b' .> (0 :: Int)) (colors !! 5)
             ) -.
           (a0 +++ a1) .-
             (bij2 # colorEdge ('b' .> (0 :: Int)) (colors !! 5)
             ) -.
           (b0 +++ b1) .-
             ( (empty +++ reversing bij1)
               # colorEdge ('b' .> (1 :: Int)) (colors !! 5)
             ) -.
           (a0 +++ a1) .-
             (bij2 # colorEdge ('b' .> (1 :: Int)) (colors !! 5)
             ) -..
           (b0 +++ b1)

      \end{diagram}
    \end{center}
    \note{\dots we can visualize time using a spatial dimension, and
      unfold the process into a sort of ``trace'' through multiple
      copies of the sets.  I have highlighted the paths taken by each
      of the three elements.

      Not only is this a nicer way to visualize the process, but it
      gives us an idea.  This trace is built out of a bunch of
      bijections glued together.  Maybe we can build an entire trace
      in a high-level, compositional way, and then extract the
      bijection we want at the end.
    }
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=100]
        import Bijections
        dia = drawBComplex bc0
      \end{diagram}
    \end{center}
    \begin{spec}
      data a <=> b = (a -> b) :<=>: (b -> a)
    \end{spec}
    \note{So what is a bijection?  We can represent a bijection
      between types |a| and |b| simply as a pair of functions from |a
      -> b| and |b -> a|; of course we also require that the two
      functions compose to the identity.}
  \end{xframe}

  \begin{xframe}{}
    \begin{spec}
      instance Category (<=>) where
        id = id :<=>: id
        (f :<=>: inv(f)) . (g :<=>: inv(g)) = (f . g) :<=>: (inv(g) . inv(f))
    \end{spec}
    \onslide<2>
    \vspace{-0.25in}
    \begin{spec}
      instance Groupoid (<=>) where
        inv(f :<=>: g) = g :<=>: f
    \end{spec}
    \note{Bijections are an instance of the |Category| type class,
      which just says that there is an identity bijection and that
      bijections can be composed just like functions.  Bijections also
      form a |Groupoid|, which just says that we can always invert a
      bijection between |a| and |b| to get a bijection between |b| and
      |a|.}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=100]
        {-# LANGUAGE LambdaCase #-}
        import Bijections

        dia = drawBComplex (a .- pbij -.. b)
          where
            a = nset 4 (colors!!0)
            b = nset 4 (colors!!1)
        pbij = single $ bijFun [0..3] (\case { 1 -> Just 0; 3 -> Just 3; _ -> Nothing}) -- $
      \end{diagram}
    \end{center}
    \onslide<2>
    \vspace{-0.25in}
    \begin{spec}
      data a <-> b = (a -> Maybe b) :<->: (b -> Maybe a)
    \end{spec}
    \[ \text{If } |f :<->: g| \text{ then } (|f a = Just b| \Leftrightarrow |g b = Just a|) \]

    \note{It turns out that bijections aren't enough. We also need
      \emph{partial} bijections, which are like bijections except that
      they may be undefined in some places.

      Formally, we can define a partial bijection as a pair of
      partial functions in opposite directions.  You don't really have
      to understand this law, it just formally expresses the intuition
      that if a partial bijection \emph{is} defined somewhere in one
      direction, then }
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=250]
        {-# LANGUAGE LambdaCase #-}
        import Bijections

        dia = hsep 3
          [ drawBComplex (a .- bij1 -. b .- bij2 -.. c)
          , text "$=$"
          , drawBComplex (a .- bijC -.. c)
          ]
          where
            a = nset 4 (colors!!0)
            b = nset 5 (colors!!2)
            c = nset 3 (colors!!4)
            bij1 = single $ bijFun [0..3] (\case { 0 -> Just 1; 2 -> Just 3; 3 -> Just 2; _ -> Nothing}) -- $
            bij2 = single $ bijFun [0..4] (\case { 0 -> Just 0; 1 -> Just 2; 3 -> Just 1; _ -> Nothing}) -- $
            -- Manually compose bij1 >>> bij2
            bijC = single $ bijFun [0..3] (\case { 0 -> Just 2; 2 -> Just 1; _ -> Nothing})  -- $
      \end{diagram}
    \end{center}
    \onslide<2>
    \begin{spec}
      instance Category (<->) where
        id = Just :<->: Just
        (f :<->: inv(f)) . (g :<->: inv(g)) = (f <=< g) :<->: (inv(g) <=< inv(f))
    \end{spec}
    \note{Composing partial bijections works like you might expect.
      If you can follow a path all the way from one side to the other,
      the result will be defined there.  But in all other cases the
      result will be undefined.  In this example, two of the edges
      ``disappear'' because they get matched up with something
      undefiend.

      So these also form a |Category|.  We have to compose each
      direction using the monadic fish operator, which in this case is
      handling the potential failure introduced by the |Maybe|
      results.
    }
  \end{xframe}

  \begin{xframe}{}
    \begin{spec}
      undef :: a <-> b
      undef = Nothing :<->: Nothing
    \end{spec}
    \note{We need just a couple more things.}
  \end{xframe}

  \begin{xframe}{}
    XXX picture!
    \begin{spec}
      class Category c => Parallel c where
        (+) :: c a b -> c a' b' -> c (Either a a') (Either b b')

      instance Parallel (<=>) where
        (f :<=>: inv(f)) + (g :<=>: inv(g)) = ...

      instance Parallel (<->) where
        (f :<->: inv(f)) + (g :<->: inv(g)) = ...
    \end{spec}
    \note{Here's something else we need\dots}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=300]
        import Bijections
        dia = gcbp
                # labelBC (cycle ["$h$", "$\\varnothing + \\overline{g}$"])
                # drawBComplex

        gcbp = (a0 +++ a1) .-
             (bij2 # colorEdge ('a' .> (0 :: Int)) (colors !! 4)
                   # colorEdge ('a' .> (1 :: Int)) (colors !! 4)
                   # colorEdge ('a' .> (2 :: Int)) (colors !! 5)
             ) -.
           (b0 +++ b1) .-
             ( (empty +++ reversing bij1)
               # colorEdge ('b' .> (0 :: Int)) (colors !! 5)
             ) -.
           (a0 +++ a1) .-
             (bij2 # colorEdge ('b' .> (0 :: Int)) (colors !! 5)
             ) -.
           (b0 +++ b1) .-
             ( (empty +++ reversing bij1)
               # colorEdge ('b' .> (1 :: Int)) (colors !! 5)
             ) -.
           (a0 +++ a1) .-
             (bij2 # colorEdge ('b' .> (1 :: Int)) (colors !! 5)
             ) -..
           (b0 +++ b1)

      \end{diagram}
    \end{center}

    \begin{code}
      trace h g = h >>> (undef + inv(g)) >>> h >>> (undef + inv(g)) >>> h
    \end{code}
    \note{So now we can finally put the pieces together to construct a
      trace.  We compose the empty partial bijection in parallel with
      the inverse of $g$ for the intermediate steps; then we compose
      an alternating sequence of this with $h$.  Incidentally, I will
      use semicolon to indicate ``backwards'' composition, so values
      flow from left to right, in the same direction as the diagrams.}
  \end{xframe}

  \begin{xframe}{}
    \begin{code}
      trace h g = h >>> (undef + inv(g)) >>> h >>> (undef + inv(g)) >>> h >>> (undef + inv(g)) >>> h >>> (undef + inv(g)) >>> h >>> ... ?
    \end{code}
    \note{Unfortunately, this doesn't actually work!  First, how do we
      know how many times to iterate?}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=350]
        import Bijections
        dia = hsep 3
          [ gcbp
            # labelBC (cycle ["$h$", "$\\varnothing + \\overline{g}$"])
            # drawBComplex
          , text "$=$"
          , ( (a0 +++ a1) .-
              (mkABij (a0 +++ a1) (b0 +++ b1) ([5,5,0,5,5]!!)
                # single # colorEdge ('a' .> (2 :: Int)) (colors !! 5))
              -.. (b0 +++ b1)
            )
            # drawBComplex
          ]

        gcbp = (a0 +++ a1) .-
             (bij2 # colorEdge ('a' .> (0 :: Int)) (colors !! 4)
                   # colorEdge ('a' .> (1 :: Int)) (colors !! 4)
                   # colorEdge ('a' .> (2 :: Int)) (colors !! 5)
             ) -.
           (b0 +++ b1) .-
             ( (empty +++ reversing bij1)
               # colorEdge ('b' .> (0 :: Int)) (colors !! 5)
             ) -.
           (a0 +++ a1) .-
             (bij2 # colorEdge ('b' .> (0 :: Int)) (colors !! 5)
             ) -.
           (b0 +++ b1) .-
             ( (empty +++ reversing bij1)
               # colorEdge ('b' .> (1 :: Int)) (colors !! 5)
             ) -.
           (a0 +++ a1) .-
             (bij2 # colorEdge ('b' .> (1 :: Int)) (colors !! 5)
             ) -..
           (b0 +++ b1)

      \end{diagram}
    \end{center}
    \note{And even if we did know how many times to iterate, it still
      doesn't work: the actual result of composing this trace is a
      partial bijection containing only the purple path.  The problem
      is that the other paths stop too early, so they get
      lost. Remember that an edge will show up in the final composed
      output only if there is a complete, unbroken path all the way
      from one side to the other!}
  \end{xframe}

  {
    \renewcommand{\secimage}{merge}
    \section{Merging}
    \note{We need one more basic ingredient\dots}
  }

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=250]
        {-# LANGUAGE LambdaCase #-}
        import Bijections

        dia :: Diagram B
        dia = hsep 3 . map (vsep 0.5) $ -- $
          [ [ topSet, botSet1 ]
          , [ topSet, botSet2 ]
          ]

        a = nset 4 (colors!!0)
        b = nset 4 (colors!!1)

        topSet, botSet1, botSet2 :: Diagram B
        topSet = drawBComplex (a .- pbijTop -.. b)
        botSet1 = drawBComplex (a .- pbijBot1 -.. b)
        botSet2 = drawBComplex (a .- pbijBot2 -.. b)

        pbijTop = single $ bijFun [0..3] (\case { 0 -> Just 1; 1 -> Just 0; 2 -> Just 3; _ -> Nothing}) -- $
        pbijBot1 = single $ bijFun [0..3] (\case { 0 -> Just 1; 3 -> Just 2; _ -> Nothing }) -- $
        pbijBot2 = single $ bijFun [0..3] (\case { 0 -> Just 1; 3 -> Just 3; _ -> Nothing }) -- $
      \end{diagram}
    \end{center}
    \note{First, let's define what it means for two partial bijections
      to be \emph{compatible}. Essentially it means that they never
      conflict: their edges either coincide or are completely
      disjoint.  The two on the left here are compatible: they have
      one edge in common, and the other edges do not touch at all.  On
      the other hand, the ones on the right are not compatible, since
      they disagree on the very lower right element.}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=250]
        {-# LANGUAGE LambdaCase #-}
        import Bijections

        dia :: Diagram B
        dia = hsep 2 . map centerY $ -- $
          [ vcat
            [ topSet
            , text "$\\sqcup$"
            , strutY 1
            , botSet1
            ]
          , text "$=$"
          , merged
          ]

        a = nset 4 (colors!!0)
        b = nset 4 (colors!!1)

        topSet, botSet1, merged :: Diagram B
        topSet = drawBComplex (a .- pbijTop -.. b)
        botSet1 = drawBComplex (a .- pbijBot1 -.. b)
        merged = drawBComplex (a .- pbijM -.. b)

        pbijTop = single $ bijFun [0..3] (\case { 0 -> Just 1; 1 -> Just 0; 2 -> Just 3; _ -> Nothing}) -- $
        pbijBot1 = single $ bijFun [0..3] (\case { 0 -> Just 1; 3 -> Just 2; _ -> Nothing }) -- $
        pbijM = single $ bijFun [0..3] (\case { 0 -> Just 1; 1 -> Just 0; 2 -> Just 3; 3 -> Just 2 }) -- $
      \end{diagram}
    \end{center}
    \note{The point is that we can \emph{merge} compatible partial bijections
      to produce one that is ``more informative'' than either one.}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[height=75]
        import Bijections
        dia = ( (a0 +++ a1)
                .- single h -..
                (b0 +++ b1)
              )
              # labelBC ["$h$"]
              # drawBComplex
          where
            h = mkABij (a0 +++ a1) (b0 +++ b1) ((`mod` 5) . succ)
      \end{diagram}
    \end{center}
    \note{Now recall iterating this process of composing with copies
      of $g$ inverse and $h$.  At each step of the process some of the
      elements in the dark blue set may ``finish'' and reach the light
      blue set, in which case their path will be completely connected
      and they will be defined in the final composed bijection.  For
      example, \dots}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[height=75]
        import Bijections
        dia = ( (a0 +++ a1)
                .- single h -.
                (b0 +++ b1)
                .- (empty +++ reversing bij1) -.
                (a0 +++ a1)
                .- single h -..
                (b0 +++ b1)
              )
              # labelBC ["$h$", "$\\varnothing \\parsum \\overline{g}$", "$h$"]
              # drawBComplex
          where
            h = mkABij (a0 +++ a1) (b0 +++ b1) ((`mod` 5) . succ)
      \end{diagram}
    \end{center}
    \note{Iterate\dots}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[height=75]
        import Bijections
        dia = ( (a0 +++ a1)
                .- single h -.
                (b0 +++ b1)
                .- (empty +++ reversing bij1) -.
                (a0 +++ a1)
                .- single h -.
                (b0 +++ b1)
                .- (empty +++ reversing bij1) -.
                (a0 +++ a1)
                .- single h -..
                (b0 +++ b1)
              )
              # labelBC ["$h$", "$\\varnothing \\parsum \\overline{g}$", "$h$", "$\\varnothing \\parsum \\overline{g}$", "$h$"]
              # drawBComplex
          where
            h = mkABij (a0 +++ a1) (b0 +++ b1) ((`mod` 5) . succ)
      \end{diagram}
    \end{center}
    \note{Iterate\dots}
  \end{xframe}

  \begin{xframe}{}
    \note{These are all compatible (see paper), so if we take the
      infinite merge (as long as it is lazy enough), we get exactly
      what we wanted!}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \includegraphics[width=2in]{GCBP-page-1}
    \end{center}
    \note{There's a bunch more in the paper.  For example, this
      infinite merge solution works but suffers from quadratic
      performance for two different reasons, and we show how to make
      the performance linear again without too much modification to
      the code.}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=200]
        import Bijections

        dia = vsep 1 . map centerX $  -- $
          [ hsep 3
            [ drawBComplex (bc2 # labelBC ["$h$"])
            , text "$-$" # translateY (-2.5)
            , drawBComplex (bc1 # labelBC ["$g$"]) # translateY (-2.5)
            ]
          , hsep 3
            [ text "$=$"
            , subResult
            ]
          ]

        subResult =
          ( a0 .-
          ( mkABij a0 b0 ((`mod` 3) . succ)
            # single
          ) -..
          b0
          )
          # drawBComplex
      \end{diagram}
    \end{center}

    % \begin{center}
    %   \begin{diagram}[width=300]
    %     {-# LANGUAGE LambdaCase #-}

    %     import Bijections
    %     import Grid

    %     dia = grid' (with & colsep .~ 2 & rowsep .~ 2) $  -- $

    %       map (map alignL)
    %       [ [ text "$h$" <> strutX 2
    %         , text "$=$"
    %         , ( (a0 +++ a1)
    %             .- single h -..
    %             (b0 +++ b1)
    %           )
    %           # labelBC ["$h$"]
    %           # drawBComplex
    %           # alignL
    %         , text "$=$"
    %         ,
    %           ( (a0 +++ a1)
    %             .- single h -..
    %             (b0 +++ b1)
    %           )
    %           # drawBComplex
    %         , text "$\\implies$"
    %         ,
    %           ( a0 .- single (mkABij a0 b0 ([1,2,100]!!)) -.. b0 )
    %           # drawBComplex
    %         , text "$=$"
    %         , text "$\\langle h ||$" <> strutX 2
    %         ]
    %       , [ text "$\\mathit{ext}_{g,h} h$"
    %         , text "$=$"
    %         , ( (a0 +++ a1)
    %             .- single h -.
    %             (b0 +++ b1)
    %             .- (empty +++ reversing bij1) -.
    %             (a0 +++ a1)
    %             .- single h -..
    %             (b0 +++ b1)
    %           )
    %           # labelBC ["$h$", "$\\varnothing \\parsum \\overline{g}$", "$h$"]
    %           # drawBComplex
    %           # alignL
    %         , text "$=$"
    %         ,
    %           ( (a0 +++ a1)
    %             .- single (mkABij (a0 +++ a1) (b0 +++ b1) (\case { 2 -> 4; 3 -> 0; _ -> 100 })) -..
    %             (b0 +++ b1)
    %           )
    %           # drawBComplex
    %         , text "$\\implies$"
    %         ,
    %           ( a0 .- single (mkABij a0 b0 (const 100)) -.. b0 )
    %           # drawBComplex
    %         , text "$=$"
    %         , text "$\\langle \\mathit{ext}_{g,h} h ||$" <> strutX 2
    %         ]
    %       , [ text "$\\mathit{ext}_{g,h}^2 h$"
    %         , text "$=$"
    %         , ( (a0 +++ a1)
    %             .- single h -.
    %             (b0 +++ b1)
    %             .- (empty +++ reversing bij1) -.
    %             (a0 +++ a1)
    %             .- single h -.
    %             (b0 +++ b1)
    %             .- (empty +++ reversing bij1) -.
    %             (a0 +++ a1)
    %             .- single h -..
    %             (b0 +++ b1)
    %           )
    %           # labelBC ["$h$", "$\\varnothing \\parsum \\overline{g}$", "$h$", "$\\varnothing \\parsum \\overline{g}$", "$h$"]
    %           # drawBComplex
    %           # alignL
    %         , text "$=$"
    %         ,
    %           ( (a0 +++ a1)
    %             .- single (mkABij (a0 +++ a1) (b0 +++ b1) (\case { 2 -> 0; _ -> 100 })) -..
    %             (b0 +++ b1)
    %           )
    %           # drawBComplex
    %         , text "$\\implies$"
    %         ,
    %           ( a0 .- single (mkABij a0 b0 ([100,100,0]!!)) -.. b0 )
    %           # drawBComplex
    %         , text "$=$"
    %         , text "$\\langle \\mathit{ext}_{g,h}^2 h ||$" <> strutX 2
    %         ]
    %       ]
    %       where
    %         h = mkABij (a0 +++ a1) (b0 +++ b1) ((`mod` 5) . succ)
    %   \end{diagram}
    % \end{center}
    \note{So, thanks very much for listening, and go read the paper!}
  \end{xframe}
\end{document}
