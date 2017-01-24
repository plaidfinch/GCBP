% -*- mode: LaTeX; compile-command: "runhaskell Shake" -*-

\documentclass[natbib, preprint]{sigplanconf}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% lhs2TeX

%include polycode.fmt

%format a0
%format a1
%format b0
%format b1
%format f0
%format f1

%format >=> = ">\!=\!>"
%format <=< = "<\!=\!<"

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
This is the text of the abstract.
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

Suppose we have four sets $A_0, A_1, B_0,$ and $B_1$ with bijections
$f_0 : A_0 \bij B_0$ and $f_1 : A_1 \bij B_1$.
Then, as illustrated in \pref{fig:adding-bijections}, we can easily
``add'' these bijections to produce a new bijection
\[ f : A_0 + A_1 \bij B_0 + B_1 \]
(where $+$ denotes the disjoint union of sets).
\begin{figure}[htp]
  \centering
  \begin{diagram}[width=150]
    import Bijections

    dia = vsep 1 . map centerX $  -- $
      [ hsep 3
        [ drawBComplex (bc0 & labelBC ["$f_0$"])
        , text "$+$"
        , drawBComplex (bc1 & labelBC ["$f_1$"])
        ]
      , hsep 3
        [ text "$=$"
        , drawBComplex (bc01 & labelBC ["$f_0 + f_1$"])
        ]
      ]
  \end{diagram}
  \caption{Adding bijections}
  \label{fig:adding-bijections}
\end{figure}
We simply take $f = f_0 + f_1$, that is, the function which applies
$f_0$ on elements of $A_0$, and $f_1$ on elements of $A_1$. In Haskell:
\begin{code}
type (+) = Either

(+) :: (a0 -> b0) -> (a1 -> b1) -> (a0 + a1 -> b0 + b1)
(f0 + f1) (Left x)   = Left   (f0 x)
(f0 + f1) (Right y)  = Right  (f1 y)
\end{code}
(Note we are punning on |(+)| at the value and type levels.)  We can
see that $(f + g)$ is a bijection as long as $f$ and $g$ are.

So we can define the \emph{sum} of two bijections.  What about the
\emph{difference}?  That is, given bijections $f$ and $f_1$ with
\begin{align*}
  f   &: A_0 + A_1 \bij B_0 +B_1  \\
  f_1 &: \makebox[\widthof{$A_0+A_1$}][r]{$A_1$}
         \bij
         \makebox[\widthof{$B_0+B_1$}][r]{$B_1$},
\end{align*} can we compute some
\[ f_0 : \makebox[\widthof{$A_0+A_1$}][l]{$A_0$} \bij \makebox[\widthof{$B_0+B_1$}][l]{$B_0$}? \]

Certainly $A_0$ and $B_0$ have the same size. The existence of the
bijections $f$ and $f_1$ tells us that $||A_0 + A_1|| = ||B_0 + B_1||$
and $||A_1|| = ||B_1||$; since, in general,
$||X + Y|| = ||X|| + ||Y||$, we can just subtract sizes to conclude
that $||A_0|| = ||B_0||$.  So, if we are willing to use the law of
excluded middle, we can say that there \emph{must exist} some
bijection $A_0 \bij B_0$.  But what if we want to actually
\emph{compute} a concrete bijection $A_0 \bij B_0$?  In that case, LEM
is too big a sledgehammer. We need something more subtle.
\todo{Say something about how LEM is not computational.}

To see why this problem is not as trivial as it may first seem,
consider \pref{fig:subtracting-bijections}.
\begin{figure}[htp]
  \centering
  \begin{diagram}[width=150]
    import Bijections

    dia = vsep 1 . map centerX $  -- $
      [ hsep 3
        [ drawBComplex (bc2 # labelBC ["$f$"])
        , text "$-$"
        , drawBComplex (bc1 # labelBC ["$f_1$"])
        ]
      , hsep 3
        [ text "$=$"
        , drawBComplex ((a0 .- empty -.. b0) # labelBC ["?"])
        ]
      ]
    bc2 = (a0 +++ a1) .- bij2 -.. (b0 +++ b1)
    bij2 = single $ mkABij (a0 +++ a1) (b0 +++ b1) ((`mod` 5) . succ) -- $
  \end{diagram}
  \caption{Subtracting bijections?}
  \label{fig:subtracting-bijections}
\end{figure}
The bijection $A_0 + A_1 \bij B_0 + B_1$ may arbitrarily mix elements
between the sets, so we cannot simply ``drop'' $A_1$ and $B_1$.  Some
of the elements in $A_0$ may map to elements in $B_1$, and vice versa.

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
the difference of two bijections (the \emph{Gordon complementary bijection
principle}, or GCBP), the usual proof of the algorithm's correctness is
itself non-constructive!  Moreover, the usual presentation of the
algorithm is low-level and element-based (\ie ``pointful'').  Our
contributions are as follows:

\begin{itemize}
\item We present an algebra of partial bijections and operations on
  them.
\item Using our algebra of partial bijections, we give a high-level,
  constructive proof of the GCBP.  To our knowledge, this is the first
  constructive \emph{proof} of the GCBP.
\item We explain a related bijection principle, the \emph{Garsia-Milne
    involution principle}, or GMIP, and prove that it is equivalent to
  the GCBP.  The equivalence of GCBP and GMIP seems to be a
  ``folklore'' result that is not explicitly recorded anywhere.
\item One downside of our high-level implementation of GCBP is that
  one direction of the computed bijection takes quadratic time; we
  show how to optimize the implementation so that both directions run
  in linear time, while retaining its high-level character.
\end{itemize}

\section{The Gordon Complementary Bijection Principle}
\label{sec:GCBP}

The key to subtraction is to use the input bijections to ``ping-pong''
back and forth between sets until landing in the right place.
Starting with an arbitrary element of $A_0$, our goal is to find an
element of $B_0$ to match it with.  First, run it through
$f : A_0 + A_1 \bij B_0 + B_1$.  If we land in $B_0$, we are done.
Otherwise, we end up with an element of $B_1$.  Run it through
$f_1 : A_1 \bij B_1$ \emph{backwards}, yielding an element of $A_1$.
Now run $f$ again, and so on.  Keep iterating this process until
finally landing in $B_0$; we match the original element of $A_0$ to
the element of $B_0$ so obtained.  \pref{fig:GCBP} illustrates this
process.  The top two elements of the (yellow) set on the upper-left
map immediately into the two lower elements of the blue set; the third
element of the yellow set, however, requires two iterations before
finally landing on the uppermost element of the blue
set. \todo{Highlight paths through the diagram}
\begin{figure}[htp]
  \centering
  \begin{diagram}[width=200]
    import Bijections

    dia = vsep 1 . map centerX $ -- $
      [ gcbp
        # labelBC (cycle ["$f$", "$f_1^{-1}$"])
        # drawBComplex
      , hsep 3
        [ text "$=$"
        , drawBComplex $  -- $
          a0 .- (single $ mkABij a0 b0 ((`mod` 3) . succ)) -.. b0  -- $
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
This implementation is somewhat simplified, since it takes $A_1 = B_1$
with $f_1$ being the identity bijection between them, but it still
serves to illustrate the basic idea.
\begin{figure}[htp]
  \centering
\begin{code}
pingpong :: (a0 + c -> b0 + c) -> (a0 -> b0)
pingpong bij a = case bij (Left a) of
  Left b   -> b
  Right c  -> fixEither (bij . Right) c

fixEither :: (c -> a0 + c) -> (c -> a0)
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

At this point, it's worth going through a careful proof of the
bijection principle.  We must prove two things: first, that the
algorithm terminates; second, that it actually produces a bijection,
as claimed.

\begin{proof}
  We first prove that the algorithm terminates.  Let $a \in A_0$ and
  consider the sequence of values in $B_0 + B_1$ generated by the
  algorithm: \[ f(a),\;\; (f \comp f_1^{-1} \comp f)(a),\;\; (f \comp f_1^{-1}
  \comp f \comp f_1^{-1} \comp f)(a),\;\; \dots, \] which we can write
  more compactly as
  \[ ((f \comp f_1^{-1})^n \comp f)(a) \]
  for $n \geq 0$.  The claim is that
  $((f \comp f_1^{-1})^n \comp f)(a) \in B_0$ for some $n$, at which
  point the algorithm stops.  Suppose not, that is, suppose
  $((f \comp f_1^{-1})^n \comp f)(a) \in B_1$ for all $n \geq 0$.
  Then since $B_1$ is finite, by the pigeonhole principle there must
  exist $0 \leq j < k$ such that \[ ((f \comp f_1^{-1})^j \comp f)(a)
  = ((f \comp f_1^{-1})^k \comp f)(a). \]  Since $f$ and $f_1$ are
  bijections, we may apply $(f \comp f_1^{-1})^{-j}$ to both sides,
  obtaining \[ f(a) = ((f \comp f_1^{-1})^{k-j} \comp f)(a) = (f \comp
  (f_1^{-1} \comp f)^{k-j})(a). \]  Finally, applying $f^{-1}$ to both
  sides, \[ a = (f_1^{-1} \comp f)^{k-j}(a). \] But $a \in A_0$,
  whereas the right-hand side is an element of $\cod(f_1^{-1}) = A_1$,
  a contradiction.

  It remains to show that the constructed $f_0$ is a bijection.  Note
  that given a particular $a \in A_0$, the algorithm visits a series
  of elements in $A_0, B_1, B_0, B_1, \dots, B_0, A_1$, finally
  stopping when it reaches $A_1$, and assigning the resulting element
  of $A_1$ as the output of $f_0(a)$.  We can explicitly construct the
  inverse of $f_0$ by running the same algorithm with $f^{-1}$ and
  $f_1^{-1}$ as input in place of $f$ and $f_1$.  That is,
  intuitively, we build build \pref{fig:GCBP} from right to left
  instead of left to right.  When run ``in reverse'' in this way on
  $f_0(a)$, we can see that the algorithm will visit exactly the same
  series of elements in reverse, stopping when it reaches the original
  $a$ since it is the first element not in $B_0$.
\end{proof}

This proof would convince any combinatorialist, but it has several
downsides:

\begin{itemize}
\item It makes heavy use of ``pointwise'' reasoning, messily following
  the fate of individual elements through an algorithm.  We would like
  a ``higher-level'' perspective on both the algorithm and proof.
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
  non-constructive is going on.

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
        a = nset 4 yellow
        b = nset 4 blue
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
  \item $\alpha$ is an involution, that is, $\alpha \comp \alpha =
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
  $f^{-1} \comp g^{-1}$ (instead of $(g^{-1} \comp f^{-1})$).  This
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
