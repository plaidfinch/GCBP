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
      \end{center}
    \end{frame}
  }
}

\newenvironment{xframe}[1][]
  {\begin{frame}[fragile,environment=xframe,#1]}
  {\end{frame}}

% uncomment me to get 4 slides per page for printing
% \usepackage{pgfpages}
% \pgfpagesuselayout{4 on 1}[uspaper, border shrink=5mm]

\setbeameroption{show notes}

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
\date{ICFP \\ St.\ Louis 2018}
\author{Brent Yorgey, Hendrix College \\ Kenny Foner, University of Pennsylvania}

% XXX some kind of fun image of bijections etc. on first slide

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

  \begin{frame}{}
    \titlepage
%    \begin{center}
%      \includegraphics[width=0.8in]{haskell-logo.pdf}
%    \end{center}
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

    \note{This is a bijection.}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=150]
        import Bijections
        dia = drawBComplex (bc1 & labelBC ["$g$"])
      \end{diagram}
    \end{center}

    \note{This is also a bijection.}
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

    \note{Given these two bijections, or any two bijections, we can
      \emph{add} them by running them in parallel.  The result is a
      another bijection, which is between the disjoint unions of the
      original sets.}
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
    \note{To illustrate this, here's some Haskell code which expresses
      one direction of this operation on bijections.  Given a function
      from $a$ to $a'$---which represents one direction of a
      bijection---and a function from $b$ to $b'$, the new function
      maps the sum of $a$ and $b$ to the sum of $a'$ and $b'$. It just
      examines its input to see which side it comes from and then runs
      the appropriate function.}
  \end{xframe}

  \begin{xframe}{DON'T TRY THIS AT HOME}
    \begin{center}
      ``set'' = ``type'' \\[1em]
      Everything is finite
    \end{center}
    \note{By the way, in this talk I am going to use the words ``set''
      and ``type'' interchangeably, and assume that everything is
      finite.}
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=150]
        import Bijections
        dia = drawBComplex (bc2 # labelBC ["$h$"])
      \end{diagram}
    \end{center}
    \note{OK. Now, suppose we \emph{start} with a bijection between
      two sum types.  Note that an arbitrary 1-1 mapping between
      $a + b$ and $a'+b'$ does not have to send left to left and right
      to right.  In other words, not every bijection of this type
      comes from taking the sum of two bijections.}
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
          this point it may not even be clear what this should
          mean. Well, first of all, if we start with a bijection
          between these two disjoint unions, and we subtract off a
          bijection between the orange sets, then I suppose we should
          get a bijection between the blue sets.  One thing we can say
          for sure is that the blue sets must have the same size,
          since $h$ shows that the disjoint unions have the same size,
          and $g$ shows that the orange sets have the same size. But
          this isn't good enough.  I don't just want to know they have
          the same size, I want a concrete matching between the blue
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
        have sixty seconds, starting\dots now!

        XXX get clock to count down on a keypress?}
  \end{xframe}

  \begin{xframe}{}
    XXX who cares?
  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      Garsia-Milne (1981), Gordon (1983)
    \end{center}

  \end{xframe}

  \begin{xframe}{}
    \begin{center}
      \begin{diagram}[width=150]
        import Bijections

        dia :: Diagram B
        dia = drawBComplex (bc2 # labelBC ["$h$"])
      \end{diagram}
    \end{center}
    \note{Let's look at $h$ again.}
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
    \note{So we do in fact match up these elements.}
  \end{xframe}

  \begin{xframe}
    \begin{center}
      \includegraphics[width=4.5in]{Pong.png}
    \end{center}
    \note{And we got there by sort of ``ping-ponging'' back and forth
      between the two sides, alternately following $h$ and
      $\overline{g}$.}
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
    \note{So we set out to see if we could find a way to think about
      and construct this algorithm in a high-level, point-free way: as
      a fun challenge, to gain insight into the algorithm and the
      related combinatorics, and possibly as a first step towards
      building a formal computer proof.}
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
    \note{Let's start by unfolding the ping-ponging process. Instead
      of thinking of $h$ and $g$ being superimposed and watching
      elements bounce back and forth\dots}
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
    \note{\dots we can use space to visualize time, and unfold the
      process into a sort of ``trace'' through multiple copies of the
      sets.  I have highlighted the paths taken by each of the three
      elements.

      Not only is this a nicer way to visualize the process, but it
      gives us an idea.  This trace is built out of a bunch of
      bijections glued together.  Maybe we can build an entire trace
      in a high-level, compositional way, and then extract the
      bijection we want at the end.
    }
  \end{xframe}

  \begin{xframe}{}
    \begin{spec}
      data a <=> b = (a -> b) :<=>: (b -> a)
    \end{spec}
    XXX picture
    \note{XXX define bijections like this.  Of course we require that
      |fwd . bwd| and |bwd . fwd| are the identity.}
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
  \end{xframe}

  \begin{xframe}{}
    \begin{spec}
      data a <-> b = (a -> Maybe b) :<->: (b -> Maybe a)
    \end{spec}
    XXX picture
    \note{XXX partial bijections.  Requirement: |pfwd a = Just b| iff
      |pbwd b = Just a|.  XXX need to explain partial bijection
      composition somewhere before showing code.}
  \end{xframe}

  \begin{xframe}{}
    \begin{spec}
      instance Category (<->) where
        id = Just :<->: Just
        (f :<->: inv(f)) . (g :<->: inv(g)) = (f <=< g) :<->: (inv(g) <=< inv(f))
    \end{spec}
    \onslide<2>
    \vspace{-0.25in}
    \begin{spec}
      instance Groupoid (<->) where
        inv(f :<=>: g) = g :<=>: f
    \end{spec}
  \end{xframe}

  \begin{xframe}{}
    \begin{spec}
      undef :: a <-> b
      undef = Nothing :<->: Nothing
    \end{spec}
    XXX picture
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
  \end{xframe}

  \begin{xframe}{}
    \begin{code}
      trace h g = h >>> (undef + inv(g)) >>> h >>> (undef + inv(g)) >>> h >>> (undef + inv(g)) >>> h >>> (undef + inv(g)) >>> h >>> ... ?
    \end{code}

  \end{xframe}
\end{document}
