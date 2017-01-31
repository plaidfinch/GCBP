% -*- mode: LaTeX; compile-command: "runhaskell Shake" -*-

\documentclass[natbib, preprint]{sigplanconf}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% lhs2TeX

%include polycode.fmt

%format >=> = ">\!=\!>"
%format <=< = "<\!=\!<"
%format +++ = "+\!\!+\!\!+"

%if false
\begin{code}
{-# LANGUAGE TypeOperators #-}
\end{code}
%endif

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Package imports

\usepackage{amsthm}
\usepackage{amsmath}
\usepackage{mathtools}
\usepackage{latexsym}
\usepackage{amssymb}
\usepackage{stmaryrd}
\usepackage{url}
\usepackage{xspace}
\usepackage{xcolor}
\usepackage[all]{xy}
\usepackage{breakurl}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Diagrams

\usepackage{pgf}
\usepackage{graphicx}
\usepackage[outputdir=diagrams,backend=pgf,extension=pgf,input]{diagrams-latex}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Prettyref

\usepackage{prettyref}

\newrefformat{fig}{Figure~\ref{#1}}
\newrefformat{sec}{\Sect\ref{#1}}
\newrefformat{eq}{equation~\eqref{#1}}
\newrefformat{prob}{Problem~\ref{#1}}
\newrefformat{tab}{Table~\ref{#1}}
\newrefformat{thm}{Theorem~\ref{#1}}
\newrefformat{lem}{Lemma~\ref{#1}}
\newrefformat{prop}{Proposition~\ref{#1}}
\newrefformat{defn}{Definition~\ref{#1}}
\newrefformat{cor}{Corollary~\ref{#1}}
\newcommand{\pref}[1]{\prettyref{#1}}

% \Pref is just like \pref but it uppercases the first letter; for use
% at the beginning of a sentence.
\newcommand{\Pref}[1]{%
  \expandafter\ifx\csname r@@#1\endcsname\relax {\scriptsize[ref]}
    \else
    \edef\reftext{\prettyref{#1}}\expandafter\MakeUppercase\reftext
    \fi
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Comments

\newif\ifcomments\commentstrue
%\newif\ifcomments\commentsfalse

\ifcomments
\newcommand{\authornote}[3]{\textcolor{#1}{[#3 ---#2]}}
\newcommand{\todo}[1]{\textcolor{red}{[TODO: #1]}}
\else
\newcommand{\authornote}[3]{}
\newcommand{\todo}[1]{}
\fi

\newcommand{\bay}[1]{\authornote{blue}{BAY}{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Semantic markup

\newcommand{\eg}{\latin{e.g.}\xspace}
\newcommand{\ie}{\latin{i.e.}\xspace}
\newcommand{\etal}{\latin{et al.}\xspace}
\newcommand{\etc}{\latin{etc.}\xspace}

\newcommand{\term}[1]{\emph{#1}}
\newcommand{\latin}[1]{\textit{#1}}
\newcommand{\foreign}[1]{\emph{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Math typesetting

\newcommand{\bij}{\leftrightarrow}
\newcommand{\comp}{\circ}
\newcommand{\id}{\mathit{id}}

\DeclareMathOperator{\cod}{cod}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

\special{papersize=8.5in,11in}
\setlength{\pdfpageheight}{\paperheight}
\setlength{\pdfpagewidth}{\paperwidth}

\conferenceinfo{CONF 'yy}{Month d--d, 20yy, City, ST, Country}
\copyrightyear{2016}
\copyrightdata{978-1-nnnn-nnnn-n/yy/mm}
\copyrightdoi{nnnnnnn.nnnnnnn}

% Uncomment the publication rights you want to use.
%\publicationrights{transferred}
%\publicationrights{licensed}     % this is the default
%\publicationrights{author-pays}

\titlebanner{DRAFT --- do not distribute}       % These are ignored unless
% \preprintfooter{short description of paper}   % 'preprint' option specified.

% I do not actually like this title or subtitle, just putting
% something here for now
\title{Subtracting Isos}
\subtitle{Computing with Bijection Principles}

% What's the Difference?
% Subtracting Isos for Fun and Profit

\authorinfo{Kenneth Foner}
           {University of Pennsylvania, USA}
           {kfoner@@seas.upenn.edu}
\authorinfo{Brent A. Yorgey}
           {Hendrix College, Conway, AR, USA}
           {yorgey@@hendrix.edu}

\maketitle

\begin{abstract}
  \todo{Write an abstract.}

  We recommend viewing this paper as a PDF or printing it on a color
  printer, though it should still be comprehensible in black and
  white.  The colors have been chosen to remain distinguishable to
  individuals with common forms of colorblindness.
\end{abstract}

\category{CR-number}{subcategory}{third-level}

% general terms are not compulsory anymore,
% you may leave them out
\terms
term1, term2

\keywords
keyword1, keyword2

\section{Introduction}

\bay{Do we need a more compelling/less technical introduction?}

Suppose we have four finite sets $A, B, A',$ and $B'$ with bijections
$f : A \bij A'$ and $g : B \bij B'$.  Then, as illustrated in
\pref{fig:adding-bijections}, we can easily ``add'' these bijections
to produce a new bijection
\[ h : A + B \bij A' + B' \]
(where $+$ denotes the disjoint union of sets).
\begin{figure}[htp]
  \centering
  \begin{diagram}[width=150]
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
  \caption{Adding bijections}
  \label{fig:adding-bijections}
\end{figure}
To construct $h$, we simply take $h = f + g$, that is, the function
which applies $f$ on elements of $A$, and $g$ on elements of $B$. In
Haskell:
\begin{code}
type (+) = Either

(+) :: (a -> a') -> (b -> b') -> (a + b -> a' + b')
(f + g) (Left x)   = Left   (f x)
(f + g) (Right y)  = Right  (g y)
\end{code}
(Note we are punning on |(+)| at the value and type levels.  This
function is included in the standard \verb|Control.Arrow| module with
the name |(+++)|, but for our purposes we find it clearer to just
define our own).  We can see that $(f + g)$ is a bijection as long as
$f$ and $g$ are.

So we can define the \emph{sum} of two bijections.  What about the
\emph{difference}?  That is, given bijections $h$ and $g$ with
\begin{align*}
  h   &: A + B \bij A' +B'  \\
  g &: \makebox[\widthof{$A+B$}][r]{$B$}
         \bij
         \makebox[\widthof{$A'+B'$}][r]{$B'$},
\end{align*} can we compute some
\[ f : \makebox[\widthof{$A+B$}][l]{$A$} \bij \makebox[\widthof{$A'+B'$}][l]{$A'$}? \]

Certainly $A$ and $A'$ must have the same size. The existence of the
bijections $h$ and $g$ tells us that $||A + B|| = ||A' + B'||$ and
$||B|| = ||B'||$; since $||A + B|| = ||A|| + ||B||$, and similarly for
$||A' + B'||$ (keeping in mind that $+$ is \emph{disjoint} union), we
can just subtract the second equation from the first to conclude that
$||A|| = ||A'||$.  Since $A$ and $A'$ are finite sets with the same
size, there \emph{must exist} some bijection $A \bij A'$.  But what if
we want to actually \emph{compute} a concrete bijection $A \bij A'$?
The fact that $A$ and $A'$ have the same size, in and of itself, does
not help us actually match up their elements.  The goal is to somehow
use the \emph{computational content} of the bijections $h$ and $g$ to
come up with a (suitably canonical) computational definition for $h - g$.

To see why this problem is not as trivial as it may first seem,
consider \pref{fig:subtracting-bijections}.
\begin{figure}[htp]
  \centering
  \begin{diagram}[width=150]
    import Bijections

    dia = vsep 1 . map centerX $  -- $
      [ hsep 3
        [ drawBComplex (bc2 # labelBC ["$h$"])
        , text "$-$"
        , drawBComplex (bc1 # labelBC ["$g$"])
        ]
      , hsep 3
        [ text "$=$"
        , drawBComplex ((a0 .- empty -.. b0) # labelBC ["$h - g$?"])
        ]
      ]
    bc2 = (a0 +++ a1) .- bij2 -.. (b0 +++ b1)
    bij2 = single $ mkABij (a0 +++ a1) (b0 +++ b1) ((`mod` 5) . succ) -- $
  \end{diagram}
  \caption{Subtracting bijections?}
  \label{fig:subtracting-bijections}
\end{figure}
The problem is that the bijection $h : A + B \bij A' + B'$ may not
look like a sum of bijections $f + g$.  A sum of bijections always
keeps $A$ and $B$ separate, mapping $A$ into $A'$ and $B$ into $B'$
(as in \pref{fig:adding-bijections}).  However, in general, a
bijection $h : A + B \bij A' + B'$ may arbitrarily mix elements
between the sets. In \pref{fig:subtracting-bijections}, notice how $h$
sends some elements from $A$ (dark blue) to $B'$ (light orange) and
likewise from $B$ (dark orange) to $A'$ (light blue). In general,
then, we cannot do anything so simple as just ``drop'' $B$ and $B'$.
We will somehow need to make use of $g$ as well.

\bay{Should we say this here? Or put it somewhere else?}
One slightly strange consequence to note is that if we do find a way
to define $h - g$, we can now see that it will \emph{not} satisfy the
identity $(h - g) + g = h$, because the left-hand side will be a sum
of bijections, which therefore looks like two separate bijections glued
together (as in \pref{fig:adding-bijections}), whereas $h$ itself may
not be.  This is not a problem in and of itself, but \todo{but what?
  We just need to be careful... we just need to be aware...}

So, why would anyone care?  This problem was first studied (and
solved) in the context of combinatorics, where proving merely that two
sets must have the same size is usually considered unsatisfactory: the
goal is to exhibit an explicit bijection that serves as a
(constructive) witness of the fact.  Subtracting bijections also comes
up in the context of defining \term{virtual species}, where it is
needed to prove that the sum of virtual species is
well-defined. \bay{double-check this, link to blog post?}  \bay{say
  something else about computational relevance?  I actually want this
  for my other project with Jacques but hard to explain here exactly
  where and why it comes up.}  To the extent that we want to use
results and techniques from combinatorics and related fields in the
context of a proof assistant based on constructive logic, a
constructive version of subtracting bijections is important.
\todo{Add citations to this paragraph.} \todo{``But, perhaps most
  saliently for this context, it's just interesting to understand how
  it works.  If you are a functional programmer who cares about computation...''}

As we will see, although there is a known algorithm for constructing
the difference of two bijections (the \emph{Gordon complementary
  bijection principle}, or GCBP), the usual proof of the algorithm's
correctness is itself non-constructive!  Moreover, the usual
presentation of the algorithm is low-level and element-based (\ie
``pointful'').  Our contributions are as follows:

\begin{itemize}
\item We present an algebra of partial bijections and their operations.
\item Using our algebra of partial bijections, we give a high-level,
  constructive proof of the GCBP.  To our knowledge, this is the first
  constructive \emph{proof} of the GCBP.  The high-level nature of the
  construction also gives additional insight into the workings of the
  principle.
\item We explain a related bijection principle, the \emph{Garsia-Milne
    involution principle} (GMIP), and prove that it is equivalent to
  the GCBP.  The equivalence of GCBP and GMIP seems to be a
  ``folklore'' result that is not explicitly recorded anywhere, and we
  are able to give a nice \emph{computational} explanation of their
  equivalence, by implementing each in terms of the other.
\item One downside of our high-level implementation of GCBP is that
  one direction of the computed bijection has quadratic performance,
  which is not a problem with the usual low-level
  implementation. However, we show how to optimize the implementation
  so that both directions run in linear time, while retaining its
  high-level character.
\end{itemize}

\section{The Gordon Complementary Bijection Principle}
\label{sec:GCBP}

Let us return to the problem of computing some $h - g : A \bij A'$
from $h : A + B \bij A' + B'$ and $g : B \bij B'$.  The key to
defining $h - g$ is to use $h$ and $g$ to ``ping-pong'' back and forth
between sets until landing in the right place.

Starting with an arbitrary element of $A$, our goal is to find an
element of $A'$ to match it with.  First, run it through
$h : A + B \bij A' + B'$.  If we land in $A'$, we are done.
Otherwise, we end up with an element of $B'$.  Run it through
$g : B \bij B'$ \emph{backwards}, yielding an element of $B$.  Now run
$h$ again, and so on.  Keep iterating this process until finally
landing in $A'$; we match the original element of $A$ to the element
of $A'$ so obtained.  \pref{fig:GCBP} illustrates this process.  The
top two elements of the (dark blue) set on the upper-left map immediately
into the two lower elements of the light blue set; the third element of the
dark blue set, however, requires two iterations before finally landing on
the uppermost element of the light blue set. \todo{Highlight paths through
  the diagram}
\begin{figure}[htp]
  \centering
  \begin{diagram}[width=200]
    import Bijections

    dia = vsep 1 . map centerX $ -- $
      [ gcbp
        # labelBC (cycle ["$h$", "$\\overline{g}$"])
        # drawBComplex
      , hsep 3
        [ text "$=$"
        , (a0 .- (single $ mkABij a0 b0 ((`mod` 3) . succ)) -.. b0) -- $
          # labelBC ["$f$"]
          # drawBComplex
        ]
      ]

    gcbp = (a0 +++ a1) .- bij2 -.
           (b0 +++ b1) .- (empty +++ reversing bij1) -.
           (a0 +++ a1) .- bij2 -.
           (b0 +++ b1) .- (empty +++ reversing bij1) -.
           (a0 +++ a1) .- bij2 -..
           (b0 +++ b1)
    bij2 = single $ mkABij (a0 +++ a1) (b0 +++ b1) ((`mod` 5) . succ) -- $
  \end{diagram}
  \caption{Ping-ponging}
  \label{fig:GCBP}
\end{figure}

A Haskell implementation is shown in \pref{fig:GCBP-uni-Haskell}.
This implementation is somewhat simplified, since it takes $B = B'$
with $g$ being the identity bijection between them, but it still
serves to illustrate the basic idea.
\begin{figure}[htp]
  \centering
\begin{code}
pingpong :: (a + c -> a' + c) -> (a -> a')
pingpong bij a = case bij (Left a) of
  Left b   -> b
  Right c  -> fixEither (bij . Right) c

fixEither :: (c -> a + c) -> (c -> a)
fixEither f a = case f a of
  Left b   -> b
  Right a' -> fixEither f a'
\end{code}
  \caption{Ping-ponging in Haskell}
  \label{fig:GCBP-uni-Haskell}
\end{figure}

This algorithm was introduced by \citet{gordon1983sieve}, who called it the
\term{complementary bijection principle} \todo{note that Gordon's
  principle is actually a bit more general?  What is computational
  content of Gordon's original paper?} \todo{See notes later below}

At this point, it's worth going through a careful, standard proof of
the bijection principle.  We must prove two things: first, that the
algorithm terminates; second, that it actually produces a bijection,
as claimed.  We denote the inverse of a bijection $f : X \bij Y$ by
$\overline{f} : Y \bij X$, and denote the composition of bijections by
juxtaposition, that is, $fg(a) = (f \comp g)(a) = f(g(a))$.

\begin{proof}
  We first prove that the algorithm terminates.  Let $a \in A$ and
  consider the sequence of values in $A' + B'$ generated by the
  algorithm: \[ h(a),\;\; h \overline g h(a),\;\; h \overline g
  h \overline g h(a),\;\; \dots, \] which we can write
  more compactly as
  \[ ((h \overline g)^n h)(a) \] for $n \geq 0$.  The claim is that
  $((h \overline g)^n h)(a) \in A'$ for some $n$, at which point the
  algorithm stops.  Suppose not, that is, suppose
  $((h \overline g)^n h)(a) \in B'$ for all $n \geq 0$.  Then since
  $B'$ is finite, by the pigeonhole principle there must exist
  $0 \leq j < k$ such that
  \[ ((h \overline g)^j h)(a) = ((h \overline g)^k h)(a). \] Since $h$
  and $g$ are bijections, so is $(h \overline g)^j$, and we may apply
  its inverse to both sides, obtaining
  \[ h(a) = ((h \overline g)^{k-j} h)(a) = (h (\overline g
    h)^{k-j})(a). \] Finally, applying $\overline h$ to both sides,
  \[ a = (\overline g h)^{k-j}(a). \] But $a \in A$, whereas the
  right-hand side is an element of the codomain of $\overline g$, that
  is, $B$.  This is a contradiction, so the algorithm must in fact
  terminate for any starting $a \in A$.

  It remains to show that the function $f$ so constructed is a
  bijection.  Note that given a particular $a \in A$, the algorithm
  visits a series of elements in $A, B', B, B', \dots, B, A'$,
  finally stopping when it reaches $A'$, and assigning the resulting
  element of $A'$ as the output of $f(a)$.  We can explicitly construct
  $\overline f$ by running the same algorithm with $\overline h$
  and $\overline g$ as input in place of $h$ and $g$.  That is,
  intuitively, we build build \pref{fig:GCBP} from right to left
  instead of left to right.  When run ``in reverse'' in this way on
  $f(a)$, we can see that the algorithm will visit exactly the same
  series of elements in reverse, stopping when it reaches the original
  $a$ since will be the first element not in $B$.
\end{proof}

This proof would convince any combinatorialist, but it has several
downsides:

\begin{itemize}
\item It makes heavy use of ``pointwise'' reasoning, messily following
  the fate of individual elements through an algorithm.  We would like
  a ``higher-level'' perspective on both the algorithm and proof.
  Note we cannot just trivially rewrite the above algorithm in terms
  of function composition and get rid of mentions of $a$, since the
  algorithm may iterate a different number of times for each
  particular $a \in A$.
\item Relatedly, the proof requires constructing the forward and
  backward directions separately, and then proving that the results
  are inverse.  It would be much more satisfying to construct both
  directions of the bijection simultaneously, so that the resulting
  bijection is ``correct by construction''.
\item Finally, as hinted earlier, the proof seems to make essential
  use of classical reasoning: the termination argument in particular
  is a proof by contradiction.  Having an algorithm at all is still
  better than nothing, but having a classical proof of correctness is
  irksome: intuitively, it doesn't seem like anything fundamentally
  non-constructive is going on, and the classical proof makes it
  problematic to implement GCBP in a proof assistant based on
  constructive logic.

  To give a constructive proof of termination, we need some sort of
  termination measure on which we can do well-founded induction, but
  it is not \emph{a priori} obvious what measure to use, especially
  when working at the level of individual elements.
\end{itemize}

\section{The Algebra of Partial Bijections}
\label{sec:algebra}

We solve all these problems at once by eschewing point-based reasoning
in favor of a high-level algebra of \emph{partial bijections}, which
we use to directly construct---and constructively verify---a bijection
which is the ``difference'' of two other bijections.

We need to work with \emph{partial} bijections---not just
bijections---since we can think of the algorithm as starting with a
completely undefined bijection and building up more and more
information, until finishing with a total bijection.  Intuitively, a
partial bijection between sets $A$ and $B$ is a bijection that may be
undefined on some elements, that is, a bijection between
\emph{subsets} of $A$ and $B$, illustrated in \pref{fig:partial-bij}.

\begin{figure}[htp]
  \centering
  \begin{diagram}[width=50]
    {-# LANGUAGE LambdaCase #-}
    import Bijections

    dia = drawBComplex (a .- pbij -.. b)
      where
        a = nset 4 (colors!!0)
        b = nset 4 (colors!!1)
    pbij = single $ bijFun [0..3] (\case { 1 -> Just 0; 3 -> Just 3; _ -> Nothing}) -- $
  \end{diagram}
  \caption{A partial bijection}
  \label{fig:partial-bij}
\end{figure}

We begin by formalizing an algebra of partial \emph{functions}, which
forms a foundation for our partial bijections.

\subsection{Partial functions}

Partial functions, in turn, are built atop the familiar |Maybe| monad,
with
\begin{spec}
data Maybe a = Nothing | Just a
\end{spec}
and \emph{Kleisli composition} defined by
\begin{spec}
(<=<) :: (b -> Maybe c) -> (a -> Maybe b) -> (a -> Maybe c)
f <=< g = \a -> g a >>= f
\end{spec}
We also define a partial order on |Maybe a| by setting $|Nothing|
\sqsubset x$ for all |x :: Maybe a|, and taking $\sqsubseteq$ as
the reflexive, transitive closure of $\sqsubset$ (though transitivity
admittedly does not add much).  Intuitively, $x \sqsubseteq y$ if $y$
is ``at least as defined as'' $x$.

\todo{Partial functions: Kleisli category.  Definedness partial order
  is pointwise.  Define sum, prove abides.  Define compatibility.
  Define subsets as pfun $\subseteq$ id (benefit: restriction is just
  composition).  Define dom operator.  Prove compatibility is the same
  as $f . dom g = g . dom f$. Prove lemma involving dom of a
  composition (with picture).  Finally, define merge of compatible
  partial functions: use symbol $\sqcup$ since it's a join in the
  partial order (should change Agda code to use this symbol too).}

\todo{Now define partial bijections as a pair of pfuns such that left,
  right dom laws hold.  Note equivalence to other possible set of
  laws.  Prove composition (using nicer equational proof).}

\todo{Continue...}

\todo{Then implement GCBP entirely at the level of partial
  bijections.  First develop version that has to iterate a specific
  number of times.  But observe that it's tricky to compute the right
  number of iterations (and it's not idempotent after doing the right
  number, so we can't just do ``enough'' and call it a day).
  Solution: iterated merge!}

\section{The Garsia-Milne Involution Principle}
\label{sec:gmip}

\todo{Make analogy with weak \& strong induction: one seems stronger,
  but actually they are equivalent.}

There is an alternative principle, the \term{Garsia-Milne involution
  principle} (GMIP), which allows subtracting bijections, and which
turns out to be equivalent to the GCBP.  At first sight, however, it
seems unmotivated and baroque.  To properly understand this principle,
we must first take a detour through the \term{Principle of
  Inclusion-Exclusion} (PIE).

\subsection{The Principle of Inclusion-Exclusion}
\label{sec:PIE}

In its most basic version, PIE is usually presented in terms of unions
and intersections of sets.  Given a finite collection of finite sets
$S_1, S_2, \dots, S_n$, we can compute the size of their union in
terms of the sizes of all possible intersections, adding intersections
of an odd number of sets and subtracting even ones.  For example, when
$n = 3$,
\begin{multline*}
||S_1 \cup S_2 \cup S_3|| = ||S_1|| + ||S_2|| + ||S_3|| \\ - ||S_1 \cap S_2|| -
||S_1 \cap S_3|| - ||S_2 \cap S_3|| + ||S_1 \cap S_2 \cap S_3||.
\end{multline*}
We can write the general case as
\[ \left|| \bigcup_{1 \leq i \leq n} S_i \right|| = \sum_{\substack{I
    \subseteq \{1, \dots, n\} \\ I \neq \varnothing}} (-1)^{||I||+1}
\left||\bigcap_{i \in I} S_i \right||, \]
where the sum is taken over all nonempty subsets of $\{1, \dots, n\}$.
Intuitively, adding the sizes of $S_1$ through $S_n$ overcounts
elements in their intersections; subtracting elements in any
intersection of two sets means elements in more than two sets are now
undercounted; and so on.  Although the need for some sort of
alternating sum seems intuitive, it is far from obvious that this is
the right one.

A proof can be given in terms of the binomial theorem, but we will not
consider that proof here.  Instead, we consider a more abstract
formulation of PIE, which leads to better notation and, more
importantly, a lovely proof that avoids the need for any algebra
whatsoever and paves the way for understanding GMIP.

Suppose we have a finite set of elements $A$, and a finite set of
properties $P$.  For each $p \in P$ and each $a \in A$, either $a$ has
property $p$ (written $p(a)$) or it does not.  (To make the connection
back to the previous formulation of PIE, we can identify each property
$p$ with the subset $A_p = \{ a \in A \mid p(a) \}$ of elements of $A$
having property $p$.)

\newcommand{\ANP}{A_{\mathrm{NP}}}

If $J \subseteq P$ is a subset of the set of properties, we write
$J(a)$ to denote the fact that $a$ has all the properties in $J$.
Likewise, we write $A_J = \{ a \in A \mid J(a) \}$ to denote the
subset of $A$ with all the properties in $J$; note that
$A_J = \bigcap_{p \in J} A_p$.  We have $A_\varnothing = A$, since
every $a \in A$ trivially satisfies all the properties in the empty
set of properties.  Finally, we write $\ANP$ to denote the set of
those $a \in A$ with \emph{no} properties in $P$; that is,
$\ANP = \{ a \in A \mid \forall p \in P.\, \neg p(a) \}$.

\todo{Note this kind of setup is common in combinatorics.
  Duality---same as looking for elements with \emph{all} properties;
  just negate all the properties.}

We may now express a generalized version of PIE as follows: \[
||\ANP|| = \sum_{J \subseteq P} (-1)^{||J||} ||A_J||. \] (The previous
formulation of PIE can be recovered by subtracting both sides from
$||A|| = ||A_\varnothing||$, and specializing from properties to
subsets.)

The following proof is due to \citet{zeilberger1984garsia}, and
indirectly to \citet{garsia1981rogers}:

\newcommand{\bigA}{\mathcal{A}}
\newcommand{\bigAe}{\bigA_{\mathrm{even}}}
\newcommand{\bigAo}{\bigA_{\mathrm{odd}}}
\newcommand{\bigANP}{\bigA_{\mathrm{NP}}}

\begin{proof}
  Let
  \[ \bigA = \{ (a, J) \mid a \in A, J \subseteq P, J(a) \} \]
  be the set of pairs $(a,J)$ where $a$ has all the properties in $J$.
  $\bigA$ is in general larger than $A$, since there may be multiple
  elements of $\bigA$ for each element of $A$: whenever
  $(a,J) \in \bigA$ and $J' \subseteq J$ then $(a,J') \in \bigA$ as
  well.  Define $\bigAe$ to be the set of $(a,J) \in \bigA$ where
  $||J||$ is even, and $\bigAo$ similarly.  Also let $\bigANP$ be the
  set of those $(a,J)$ where $a$ has no properties---note that in this
  case $J$ is necessarily empty, since $a$ must satisfy all the
  properties in $J$.  Hence $||\bigANP|| = ||\ANP||$.

  Pick an arbitrary ordering of the properties in $P$, and let $s(a)$
  denote the smallest property possessed by $a$ (if $a$ has any
  properties).  Then define $\alpha : \bigA \to \bigA$ by \[
  \alpha(a, J) = \begin{cases} (a, J \cup \{ s(a) \}) & s(a) \notin
    J \\ (a, J \setminus \{ s(a) \}) & s(a) \in J \\ (a,J) &
    \text{$a$ has no properties} \end{cases} \]  That is, $\alpha$
  toggles the presence of the smallest property possessed by $a$, or
  acts as the identity if $a$ has no properties.  We observe the
  following:
  \begin{itemize}
  \item $\alpha$ is an involution, that is, $\alpha^2 =
    \id$, and hence $\alpha$ is a permutation of $\bigA$.
  \item $\alpha$ always sends odd-size $J$ to even-size $J$, and vice
    versa---except when $a$ has no properties (in which case $J =
    \varnothing$ is even).
  \end{itemize}
  We conclude that $\alpha$ is a bijection bewteen $\bigAe \setminus
  \bigANP$ and $\bigAo$, so in particular $||\bigAe|| - ||\bigANP|| =
  ||\bigAo||$; rearranging, we have \[ ||\ANP|| = ||\bigANP|| = ||\bigAe|| -
  ||\bigAo||. \] It remains only to show that \[ ||\bigAe|| -
  ||\bigAo|| = \sum_{J \subseteq P} (-1)^{||J||} ||A_J||, \] which
  follows from the fact that pairs $(a,J) \in \bigA$ are in 1-1
  correspondence with elements of $A_J$.
\end{proof}

\todo{WHAT IS A COMPUTATIONAL INTERPRETATION OF PIE?}

\todo{OMG, now that I go back and reread the Gordon paper I actually
  understand what it is doing. It's constructing a bijection in
  exactly this sort of PIE situation---with two families of sets that
  are ``sieve-equivalent'', that is, we have bijections $f_J : A_J
  \bij B_J$ for each $J \subseteq P$.}

\todo{Note that Gordon himself claims GCBP is equivalent to GMIP, but
  gives no proof.}

\subsection{Signed involutions and GMIP}
\label{sec:signed-involutions}

\todo{Basic setup of a set $\bigA$ partitioned into a
  ``positive''/``even'' part and a ``negative''/``odd'' part, with an
  involution that fixes the set we are interested in and is otherwise
  sign/parity-reversing.  This situation comes up all the
  time---whenever PIE is involved.  GMIP builds on this situation,
  saying what we can do when we have two such partitioned sets that
  correspond.}

\todo{Why would the situation of two related partitioned sets come up?
  There is still some part of the story I'm missing\dots}

\todo{check out garsia1981method.}

\section{Efficiency}
\label{sec:efficiency}

\todo{PALINDROMES}

\todo{Notice that we're doing nested calls to |(>=>)| in both
  directions, so necessarily one direction is going to be
  left-associated and one will be right-associated, leading to
  quadratic behavior in one direction or the other.  Solution: compose
  partial bijections the ``naive'' (wrong) way, $f \comp g$ and
  $\overline f \comp \overline g$ (instead of $(\overline g \comp
  \overline f)$).  This
  works in this particular case because we're computing a PALINDROME
  so the order actually doesn't matter. (Enforcing this in the type
  system would be tricky but possible.)}

% \appendix
% \section{Appendix Title}

% This is the text of the appendix, if you need one.

\acks

Acknowledgments, if needed.

\bibliographystyle{abbrvnat}
\bibliography{GCBP-paper}

% The bibliography should be embedded for final submission.

% \begin{thebibliography}{}
% \softraggedright

% \bibitem[Smith et~al.(2009)Smith, Jones]{smith02}
% P. Q. Smith, and X. Y. Jones. ...reference text...

% \end{thebibliography}


\end{document}
