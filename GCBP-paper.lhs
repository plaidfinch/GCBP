% -*- mode: LaTeX; compile-command: "./build.sh" -*-

\documentclass[acmsmall,authorversion=true]{acmart}\settopmatter{}

%% Journal information
%% Supplied to authors by publisher for camera-ready submission;
%% use defaults for review submission.
\acmJournal{PACMPL}
\acmVolume{1}
\acmNumber{ICFP} % CONF = POPL or ICFP or OOPSLA
\acmArticle{1}
\acmYear{2018}
\acmMonth{1}
\acmDOI{} % \acmDOI{10.1145/nnnnnnn.nnnnnnn}
\startPage{1}

%% Copyright information
%% Supplied to authors (based on authors' rights management selection;
%% see authors.acm.org) by publisher for camera-ready submission;
%% use 'none' for review submission.
\setcopyright{none}
%\setcopyright{acmcopyright}
%\setcopyright{acmlicensed}
%\setcopyright{rightsretained}
%\copyrightyear{2018}           %% If different from \acmYear

%% Bibliography style
\bibliographystyle{ACM-Reference-Format}
%% Citation style
%% Note: author/year citations are required for papers published as an
%% issue of PACMPL.
\citestyle{acmauthoryear}   %% For author/year citations

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% lhs2TeX

%include polycode.fmt

% Some keywords that lhs2TeX doesn't know about
%format qualified = "\mathbf{qualified}"
%format pattern   = "\mathbf{pattern}"
%format as        = "\mathbf{as}"

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

%format f1
%format f2
%format g1
%format g2

%format fi     = "f_i"
%format fip1   = "f_{i+1}"

%%format arr   = "(\longrightarrow)"
%%format `arr` = "\longrightarrow"

%format extend(g)(h) = "\mathit{ext}_{" g "," h "}"

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
\newcommand{\personalnote}[3]{\textcolor{#1}{[#3 ---#2]}}
\newcommand{\todo}[1]{\textcolor{red}{[TODO: #1]}}
\else
\newcommand{\personalnote}[3]{}
\newcommand{\todo}[1]{}
\fi

\newcommand{\bay}[1]{\personalnote{blue}{BAY}{#1}}

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

\newcommand{\pfun}{\rightharpoonup}
\newcommand{\compat}{\mathbin{||||}}
\newcommand{\mrg}{\sqcup}

\newcommand{\parsum}{+}

\newtheorem{thm}{Theorem}
\newtheorem{lem}[thm]{Lemma}

\DeclareMathOperator{\Fix}{Fix}

\newcommand{\andthen}{\mathbin{;}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

%% Title information
\title{What's the Difference?}         %% [Short Title] is optional;
                                        %% when present, will be used in
                                        %% header instead of Full Title.
% \titlenote{with title note}             %% \titlenote is optional;
%                                         %% can be repeated if necessary;
%                                         %% contents suppressed with 'anonymous'
\subtitle{A Functional Pearl on Subtracting Bijections}
% \subtitlenote{with subtitle note}       %% \subtitlenote is optional;
%                                         %% can be repeated if necessary;
%                                         %% contents suppressed with 'anonymous'


%% Author information
%% Contents and number of authors suppressed with 'anonymous'.
%% Each author should be introduced by \author, followed by
%% \authornote (optional), \orcid (optional), \affiliation, and
%% \email.
%% An author may have multiple affiliations and/or emails; repeat the
%% appropriate command.
%% Many elements are not rendered, but should be provided for metadata
%% extraction tools.

%% Author with single affiliation.
\author{Brent A. Yorgey}
% \authornote{with author1 note}          %% \authornote is optional;
%                                         %% can be repeated if necessary
% \orcid{nnnn-nnnn-nnnn-nnnn}             %% \orcid is optional
\affiliation{
  % \position{Position1}
  \department{Department of Mathematics and Computer Science}              %% \department is recommended
  \institution{Hendrix College}            %% \institution is required
  % \streetaddress{Street1 Address1}
  \city{Conway}
  \state{AR}
  % \postcode{Post-Code1}
  \country{USA}                    %% \country is recommended
}
\email{yorgey@@hendrix.edu}          %% \email is recommended

%% Author with single affiliation.
\author{Kenneth Foner}
% \authornote{with author1 note}          %% \authornote is optional;
%                                         %% can be repeated if necessary
% \orcid{nnnn-nnnn-nnnn-nnnn}             %% \orcid is optional
\affiliation{
  % \position{Position1}
  % \department{Department of Mathematics and Computer Science}              %% \department is recommended
  \institution{University of Pennsylvania}            %% \institution is required
  % \streetaddress{Street1 Address1}
  \city{Philadelphia}
  \state{PA}
  % \postcode{Post-Code1}
  \country{USA}                    %% \country is recommended
}
\email{kfoner@@seas.upenn.edu}          %% \email is recommended


% \authorinfo{Kenneth Foner}
%            {University of Pennsylvania, USA}
%            {kfoner@@seas.upenn.edu}

\begin{abstract}
  It is a straightforward exercise to write a program to ``add'' two
  bijections---resulting in a bijection between two sum types, which
  runs the first bijection on elements from the left summand and the
  second bijection on the right. It is much less obvious how to
  ``subtract'' one bijection from another.  This problem has been
  studied in the context of combinatorics, with several computational
  principles known for producing the ``difference'' of two bijections.
  We consider the problem from a computational and algebraic
  perspective, showing how to construct such bijections at a high
  level, avoiding pointwise reasoning or being forced to construct the
  forward and backward directions separately---without sacrificing
  performance.
\end{abstract}


%% 2012 ACM Computing Classification System (CSS) concepts
%% Generate at 'http://dl.acm.org/ccs/ccs.cfm'.
 \begin{CCSXML}
<ccs2012>
<concept>
<concept_id>10002950.10003624.10003625</concept_id>
<concept_desc>Mathematics of computing~Combinatorics</concept_desc>
<concept_significance>500</concept_significance>
</concept>
<concept>
<concept_id>10011007.10011006.10011008.10011009.10011012</concept_id>
<concept_desc>Software and its engineering~Functional languages</concept_desc>
<concept_significance>500</concept_significance>
</concept>
</ccs2012>
\end{CCSXML}

\ccsdesc[500]{Mathematics of computing~Combinatorics}
\ccsdesc[500]{Software and its engineering~Functional languages}
%% End of generated code


%% Keywords
%% comma separated list
\keywords{bijection, difference}  %% \keywords are mandatory in final camera-ready submission


%% \maketitle
%% Note: \maketitle command must come after title commands, author
%% commands, abstract environment, Computing Classification System
%% environment and commands, and keywords command.
\maketitle

\section{Introduction}

Suppose we have four finite types (sets) $A, B, A',$ and $B'$ with
bijections $f : A \bij A'$ and $g : B \bij B'$.  Then, as
illustrated\footnote{We recommend viewing this paper as a PDF or
  printing it on a color printer, though it should still be
  comprehensible in black and white.  The colors have been chosen to
  remain distinguishable to individuals with common forms of
  color blindness.}
in \pref{fig:adding-bijections}, we can ``add'' these bijections to
produce a new bijection
\[ h : A + B \bij A' + B', \]
where $+$ denotes a sum type (or a disjoint union of sets).
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
We take $h$ to be the function which applies $f$ on elements of $A$,
and $g$ on elements of $B$, which we denote as $h = f + g$. In
Haskell, we could encode this as follows:
\begin{code}
type (+) = Either

(+) :: (a -> a') -> (b -> b') -> (a + b -> a' + b')
(f + g) (Left x)   = Left   (f x)
(f + g) (Right y)  = Right  (g y)
\end{code}
(Note we are punning on |(+)| at the value and type levels.  This
function already lives in the standard \verb|Data.Bifunctor| module
with the name |bimap|---in the |Bifunctor Either| instance---but for
our purposes it is clearer to just define our own.)  We can see
that $(f + g)$ is a bijection as long as $f$ and $g$ are.

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
size, there \emph{must exist} some bijection $A \bij A'$.  But this is
not constructive: what if we want to actually \emph{compute} a
bijection $A \bij A'$?  The fact that $A$ and $A'$ have the same size,
in and of itself, does not help us actually match up their elements.
The goal is to somehow use the \emph{computational content} of the
bijections $h$ and $g$ to come up with a (suitably canonical)
definition for $h - g$.

To see why this problem is not as trivial as it may first seem,
consider \pref{fig:subtracting-bijections}.
\begin{figure}[htp]
  \centering
  \begin{diagram}[width=150]
    import Bijections

    dia = vsep 1 . map centerX $  -- $
      [ hsep 3
        [ drawBComplex (bc2 # labelBC ["$h$"])
        , text "$-$" # translateY (-2.5)
        , drawBComplex (bc1 # labelBC ["$g$"]) # translateY (-2.5)
        ]
      , hsep 3
        [ text "$=$"
        , drawBComplex ((a0 .- empty -.. b0) # labelBC ["$h - g$?"])
          <>
          text "?"
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

% \bay{Should we say this here? Or put it somewhere else?}
% One slightly strange consequence to note is that if we do find a way
% to define $h - g$, we can now see that it will \emph{not} satisfy the
% identity $(h - g) + g = h$, because the left-hand side will be a sum
% of bijections, which therefore looks like two separate bijections glued
% together (as in \pref{fig:adding-bijections}), whereas $h$ itself may
% not be.  This is not a problem in and of itself, but \todo{but what?
%   We just need to be careful... we just need to be aware...}

Before attacking this problem, it's worth taking a minute to consider
why it is worth studying.  This problem was first studied (and solved)
in the context of combinatorics, where proving merely that two sets
must have the same size is usually considered unsatisfactory: the goal
is to exhibit an explicit bijection that serves as a (constructive)
witness of the fact, and helps uncover additional structure or give
some intuition as to ``why'' the sets have the same size.
% Subtracting bijections also comes up in the
% context of defining \term{virtual species}, where it is
% needed to prove that the sum of virtual species is
% well-defined. \bay{double-check this, link to blog post?}  \bay{say
%   something else about computational relevance?  I actually want this
%   for my other project with Jacques but hard to explain here exactly
%   where and why it comes up.}
Relatedly, in order to use techniques from combinatorics in the context of a
proof assistant based on constructive logic, being able to subtract
bijections constructively is important.
% \todo{Add citations to this
%   paragraph.}
% \todo{``But, perhaps most saliently for this context,
%   it's just interesting to understand how it works.  If you are a
%   functional programmer who cares about computation...''}

In one sense, the problem has already been solved, first by
\citet{garsia1981method} and then, in a different form, by
\citet{gordon1983sieve}.  However, the usual presentation of their
techniques is low-level and element-based (\ie ``pointful''), which
obscures the high-level details; in addition, since the construction
is usually presented in one direction at a time, there is an extra
burden of proof to show that the two directions so constructed
actually form a bijection.

Using an algebra of \term{partial bijections}, we will give a
high-level construction of the Gordon complementary bijection
principle (GCBP), which computes the difference of two bijections.
One downside of our high-level implementation of GCBP is that one
direction of the computed bijection has quadratic performance, whereas
the usual low-level implementation takes linear time in both
directions. However, we will then show how to optimize the
implementation so that both directions run in linear time again, while
retaining its high-level character.

% \item We explain a related bijection principle, the \emph{Garsia-Milne
%     involution principle} (GMIP), and prove that it is equivalent to
%   GCBP.  The equivalence of GCBP and GMIP seems to be a ``folklore''
%   result that is not explicitly recorded anywhere, and we are able to
%   give a \emph{computational} explanation of their equivalence, by
%   implementing each in terms of the other, and proving that
%   translating back and forth is the identity in both directions.

\section{The Gordon Complementary Bijection Principle}
\label{sec:GCBP}

Let us return to the problem of computing some $h - g : A \bij A'$
from $h : A + B \bij A' + B'$ and $g : B \bij B'$ and describe the
solution of \citet{gordon1983sieve} as it is typically
presented.  The key to defining $h - g$ is to use $h$ and $g$ to
``ping-pong'' back and forth between sets until landing in the right
place.

Starting with an arbitrary element of $A$, our goal is to find an
element of $A'$ to match it with.  First, run it through
$h : A + B \bij A' + B'$.  If we land in $A'$, we are done.
Otherwise, we end up with an element of $B'$.  Run this backwards through
$g : B \bij B'$, yielding an element of $B$.  Now run
$h$ again. This may yield an element of $A'$, in which case we can
stop, or an element of $B'$; we continue iterating this process until
finally landing in $A'$. We then match the original element of $A$ to
the element of $A'$ so obtained.

\pref{fig:GCBP} illustrates this process.  The top two elements of the
(dark blue) set on the upper-left map immediately into the two lower
elements of the light blue set; the third element of the dark blue
set, however, requires two iterations back and forth before finally
landing on the uppermost element of the light blue set.
\begin{figure}[htp]
  \centering
  \begin{diagram}[width=200]
    import Bijections

    dia = vsep 1 . map centerX $ -- $
      [ gcbp
        # labelBC (cycle ["$h$", "$\\overline{g}$"])
        # drawBComplex
      , hsep 3
        [ arrowV (2 ^& 0)
        , ( a0 .-
              ( mkABij a0 b0 ((`mod` 3) . succ)
                # single
                # colorEdge (toNameI 0) (colors !! 4)
                # colorEdge (toNameI 1) (colors !! 4)
                # colorEdge (toNameI 2) (colors !! 5)
              ) -..
            b0
          )
          # labelBC ["$f$"]
          # drawBComplex
        ]
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
    bij2 = single $ mkABij (a0 +++ a1) (b0 +++ b1) ((`mod` 5) . succ) -- $
  \end{diagram}
  \caption{Ping-ponging}
  \label{fig:GCBP}
\end{figure}
Symbolically, for each $a \in A$ we find the smallest $n$ such that
$(h \overline{g})^n h$ applied to $a$ yields some $a' \in A'$. (We
denote the inverse of a bijection $f : X \bij Y$ by
$\overline{f} : Y \bij X$, and denote the composition of bijections by
juxtaposition, that is, $fg(a) = (f \comp g)(a) = f(g(a))$.)
\pref{fig:GCBP-uni-Haskell} contains a basic Haskell implementation of
this process.  It is worth pointing out that the Haskell
implementation is a bit noisier because of the need for |Left| and
|Right| constructors; typical mathematical presentations treat $A$ as
a subset (subtype) of $A + B$, so that an element $a \in A$ \emph{is also}
an element of $A + B$, without the need to explicitly inject it.
\begin{figure}[htp]
  \centering
\begin{code}
pingpong :: (a + b -> a' + b') -> (b' -> b) -> (a -> a')
pingpong h g' = untilLeft (h . Right . g') . h . Left

untilLeft :: (b' -> a' + b') -> (a' + b' -> a')
untilLeft step ab = case ab of
  Left   a'  -> a'
  Right  b'  -> untilLeft step (step b')
\end{code}
  \caption{Ping-ponging in Haskell}
  \label{fig:GCBP-uni-Haskell}
\end{figure}

\citet{gordon1983sieve} introduced this algorithm, and called it
the \term{complementary bijection principle}. (Actually, Gordon's
principle is quite a bit more general than this, involving a whole
tower of bijections on chains of nested subsets, but we do not
consider the principle in full generality here.)

At this point, it's worth going through a careful, standard proof of
the complementary bijection principle.  We must prove two things:
first, that the algorithm terminates; second, that it actually
produces a bijection, as claimed.

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
  intuitively, we build \pref{fig:GCBP} from right to left
  instead of left to right.  When run ``in reverse'' in this way on
  $f(a)$, we can see that the algorithm will visit exactly the same
  series of elements in reverse, stopping when it reaches the original
  $a$ since it will be the first element not in $B$.
\end{proof}

This construction and proof would convince any combinatorialist, but
they have several downsides:

\begin{itemize}
\item This presentation makes heavy use of ``pointwise'' reasoning,
  messily following the fate of individual elements through an
  algorithm.  We would like a ``higher-level'' perspective on both the
  algorithm and proof.  Note we cannot simply rewrite the above
  algorithm in terms of function composition and get rid of any
  mentions of $a$, since the algorithm may iterate a different number
  of times for each particular $a \in A$.
\item Relatedly, in this presentation we construct the forward and
  backward directions separately, and then prove that the results
  are inverse.  It would be better to construct both directions of the
  bijection simultaneously, so that the resulting bijection is
  ``correct by construction''.
\end{itemize}

We solve these problems by eschewing point-based reasoning in favor of
a high-level algebraic approach, which we use to directly construct a
bijection which is the ``difference'' of two other bijections.  We
also hope that a high-level construction may be easier to formally
prove correct.  \citet{gudmundsson2017formalizing} has recently given
the first mechanized formal proof of the complementary bijection
principle, in Agda, but it is long and relies heavily on low-level
pointwise reasoning.  We leave to future work the challenge of turning
our high-level construction into a corresponding high-level proof.

\section{Partial Bijections}
\label{sec:algebra}

Since the GCBP takes two bijections as input and yields a bijection as
output, one might think to begin by defining a type of bijections:
\begin{spec}
data Bijection a b = Bijection
  {  ^^ fwd  :: a -> b
  ,  ^^ bwd  :: b -> a
  }
\end{spec}
satisfying the invariants that |to . from = id| and |from . to =
id|. (In a dependently typed language, one might well include these
conditions as part of the definition. Although Haskell itself can
simulate dependent types, invariants such as these would make our
definitions much too heavyweight.) The idea would be to somehow piece
together the GCBP algorithm out of high-level operations on
bijections, so that the whole algorithm returns a valid bijection by
construction, eliminating duplication of code and the possibility for
the forward and backward directions to be out of sync.

This is the right idea, but it is not good enough.  The problem
is that when it comes to bijections, the algorithm is an
all-or-nothing sort of deal: we put two bijections in and get one out,
but it is hard to find intermediate bijections that arise during
execution of the algorithm, out of which we could build the ultimate
result.

Instead, we must generalize to \emph{partial} bijections, that
is, bijections which may be undefined on some parts of their domain
(\pref{fig:partial-bij}).  We can think of the algorithm as starting
with a totally undefined bijection and building up more and more
information, until finishing with a total bijection.

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

Whereas a (total) bijection consists of a pair of inverse functions |a
-> b| and |b -> a|, a partial bijection consists of a pair of
\emph{partial} functions |a -> Maybe b| and |b -> Maybe a| which are
``inverse'' in a suitable sense (to be precisely defined later).  We
can work uniformly with both by generalizing to an arbitrary
\emph{Kleisli} category,
\begin{spec}
newtype Kleisli m a b = K { runKleisli :: a -> m b }
\end{spec}
consisting of functions |a -> m b| for any monad |m|.  In one sense,
this generality is overkill: working concretely with total and partial
bijections instead of a common generalization would require a bit of
code duplication but would be quite a bit simpler.  However, in
addition to reducing code duplication, working in a more general
setting reveals some underlying algebraic structure, and hints at
potential extensions and generalizations to be discovered.

In any case, picking |m = Identity| in the definition of |Kleisli m a
b| yields normal total functions (up to some extra |newtype|
wrappers); picking |m = Maybe| yields partial functions.  The
|Category| instance for |Kleisli m| provides the identity |id ::
Kleisli m a a| along with a composition operator
\[ |(.) :: (Kleisli m b c) -> (Kleisli m a b) -> (Kleisli m a c)|. \]
\begin{spec}
class Category cat where
  id   :: cat a a
  (.)  :: cat b c -> cat a b -> cat a b

instance Monad m => Category (Kleisli m) where
  id         = K return
  K g . K f  = K (\a -> f a >>= g)
\end{spec}
In order to match up with the pictures, where we tend to draw
functions going from left to right, we will also make use of the
notation
\begin{spec}
  f >>> g = g . f
\end{spec}

We can now define a general type of |m|-bijections as
\begin{code}
data Bij m a b = B
  {  ^^ fwd  :: Kleisli m a b
  ,  ^^ bwd  :: Kleisli m b a
  }
\end{code}
These compose via a |Category| instance, and also have inverses:
\begin{code}
instance Monad m => Category (Bij m) where
  id = B id id
  (B f1 g1) . (B f2 g2) = B (f1 . f2) (g2 . g1)

class Category c => Groupoid c where
  (inverse(-)) :: c a b -> c b a

instance Monad m => Groupoid (Bij m) where
  inverse (B f g) = B g f
\end{code}

Composing two partial functions works the way we would expect: the
composite |f >>> g| is defined on $a$ if and only if $f$ is defined on
$a$ and $g$ is defined on $f(a)$.  Thinking pictorially, when we
compose two partial bijections, we keep only those paths which travel
continuously across the entire diagram, as shown in
\pref{fig:partial-compose}.

\begin{figure}
  \centering
  \begin{diagram}[width=200]
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
  \caption{Composing partial bijections}
  \label{fig:partial-compose}
\end{figure}

Not just any pair of Kleisli arrows qualifies as a generalized
bijection.  When |m = Identity|, a generalized bijection should
consist of two inverse functions, that is, functions whose composition
is |id|.  When |m = Maybe|, composing the two functions does not have
to yield the identity, since it may be undefined in some places---but
it should certainly be the identity when restricted to points on which
the functions are defined.  More formally, we should have |fwd a =
Just b| if and only if |bwd b = Just a|.  This justifies drawing
partial bijections by connecting two sets with some collection of
undirected (\ie bidirectional) line segments, as in
\pref{fig:partial-bij}.  (These laws can be generalized to any monad
|m| with some sort of ``information ordering'' relation; intuitively
the composition of the |fwd| and |bwd| morphisms should be the
identity ``up to any |m| effects''.)

% To express this formally, we introduce the function |dom| (short for
% \emph{domain}), which intuitively extracts just the ``effects'' of a
% morphism |f|: for each |a|, the effects generated by running |f a| are
% retained, but the output of type |b| is discarded and replaced by |a|
% itself.  This is illustrated in \pref{fig:dom}, and an implementation
% of |dom| is shown in \pref{fig:domcode}.
% \begin{figure}[htp]
%   \centering
%   \begin{diagram}[width=120]
%     {-# LANGUAGE LambdaCase #-}
%     import Bijections

%     dia = hsep 3
%       [ (a .- pbij -.. b)
%         # labelBC ["$f$"]
%         # drawBComplex
%       , (a .- pbijdom -.. a)
%         # labelBC ["$\\mathit{dom}\\; f$"]
%         # drawBComplex
%       ]
%       where
%         a = nset 4 (colors!!0)
%         b = nset 4 (colors!!2)
%     pbij = single $ bijFun [0..3] (\case { 1 -> Just 0; 3 -> Just 3; _ -> Nothing}) -- $
%     pbijdom = single $ bijFun [0..3] (\case { 1 -> Just 1; 3 -> Just 3; _ -> Nothing}) -- $
%   \end{diagram}
%   \caption{|dom| on a partial bijection |f : Kleisli Maybe a b|}
%   \label{fig:dom}
% \end{figure}
% \begin{figure}
% \begin{spec}
%   dom :: Functor m => (Kleisli m a b) -> (Kleisli m a a)
%   dom (K f) = K (\a -> const a <$> f a)
% \end{spec}%$
% \caption{The |dom| function} \label{fig:domcode}
% \end{figure}
% We also require that the monad |m| has some relation |<==| on
% values of type |m a|, which we can think of as an ``information
% ordering''.  For |m = Identity|, we have |a <== b| if and only
% if |a = b|; for |m = Maybe|, |Nothing <== Just a| and |Just a <== Just
% a|.  We can now impose the laws
% \begin{spec}
%   fwd >>> bwd ==> dom fwd
%   bwd >>> fwd ==> dom bwd
% \end{spec}
% which intuitively say that |fwd >>> bwd| and |bwd >>> fwd| must both
% act like |id|, except for some possible effects.
% When |m = Identity| there are no effects at all, and indeed, |dom f =
% id| since |const a
% <$> f a = Identity a|, so the laws reduce to the familiar |fwd >>> bwd
% = id| and |bwd >>> fwd = id|.  In the case |m = Maybe|, the laws
% essentially say that |fwd a = Just b| if and only if |bwd b = Just
% a|---that is, |fwd| and |bwd| must agree wherever they are both
% defined, and moreover, they must be defined and undefined in the same
% places. This justifies drawing partial bijections by connecting two
% sets with some collection of undirected (\ie bidirectional) line
% segments, as in \pref{fig:partial-bij}.
% %$

As an aside, we remark that choosing |m = Set| (which is a monad in
the mathematical sense, if not a |Monad| in Haskell) leads to
``multibijections'', where each element $a \in A$ may map to zero or
more elements in $B$, as long as each such element in the image of $a$
also maps back to $a$ (and possibly some other elements of $A$).  We
leave to future work the question of whether there is any interesting
analogue to the bijection principles discussed here for
multibijections.

Finally, we can recover specific types for total and partial bijections as
\begin{code}
type a <=> b = Bij Identity a b
type a <-> b = Bij Maybe a b
\end{code}

To make working with total and partial bijections more convenient, we
can define \emph{pattern synonyms} \citep{pickering2016pattern} which let us pretend as
if we had directly declared types like
\begin{spec}
data a <=> b = (a -> b)        :<=>:  (b -> a)
data a <-> b = (a -> Maybe b)  :<->:  (b -> Maybe a)
\end{spec}
automatically handling the required |newtype| wrapping and unwrapping.
The declarations for these pattern synonyms are shown in
\pref{fig:pat-syns} for completeness, though the syntax is somewhat
complex and the details are unimportant.

\begin{figure}
\begin{code}
pattern (:<->:) f g = B (K f) (K g)

pattern (:<=>:) f g <- B  (K ((>>> runIdentity) -> f))
                          (K ((>>> runIdentity) -> g))
  where
    f :<=>: g = B  (K (f >>> Identity))
                   (K (g >>> Identity))
\end{code}
\caption{Pattern synonyms for total and partial bijections} \label{fig:pat-syns}
\end{figure}

In what follows, we will sometimes use simple diagrams of labelled
boxes and lines to abstractly represent sets and generalized
bijections between them, since looking at the pictures gives a much
better intuitive idea of what is going on than looking at code.  For
example, we draw a generalized bijection $f$ between sets $A$ and $B$
as a thick line connecting two labelled boxes, as shown in
\pref{fig:gen-bij-dia}.
\begin{figure}
  \begin{center}
    \begin{diagram}[width=75]
      import Bijections

      dia = drawGenBij tex
        (sg "A" .- lk "f" -.. sg "B" :: GenBij String)
    \end{diagram}
  \end{center}
  \caption{A generalized bijection $f$ between $A$ and $B$} \label{fig:gen-bij-dia}
\end{figure}
Note that we don't draw the action of $f$ on individual elements of
$A$ and $B$, but simply summarize the relationship expressed by $f$
with a single thick line.

  % dia = drawGenBij tex
  %   ((sg "A_1" +++ sg "A_2") +++ sg "A_3")
  %     .- lk "f" -. (sg "B_1" +++ sg "B_2")
  %     .- lk "g" -.. sg "C"
  %   )

We now define some utility functions for working with total and
partial bijections (\pref{fig:partial-total}). First, |applyTotal| and
|applyPartial| let us run a bijection in the forward direction.  Next,
we define |undef| as the totally undefined partial bijection, which
we draw as two unconnected boxes, as in \pref{fig:undefined}.
\begin{figure}
\begin{center}
\begin{diagram}[width=75]
  import Bijections

  dia = drawGenBij tex (sg "A" .- emptyLk "\\varnothing" -.. sg "B")
\end{diagram}
\end{center}
\caption{The undefined partial bijection} \label{fig:undefined}
\end{figure}
Finally, the |partial| and |unsafeTotal| functions move back and forth
between total and partial bijections.  Treating a total bijection as a
partial one is always safe, and we will sometimes omit calls to
|partial| in informal discussion, thinking of total bijections as a
``subtype'' of partial bijections.  On the other hand, moving in the
other direction is only safe if we know that the ``partial'' bijection
is, in fact, defined everywhere. Evaluating |unsafeTotal f| at some
input for which |f| is undefined will result in a runtime error.  (With
a richer type system we could of course make a safe version of
|unsafeTotal| which requires a proof of totality.)
\begin{figure}
\begin{code}
applyTotal    ::  (a <=> b)    ->  a -> b
applyTotal        (f :<=>: _)  =   f

applyPartial  ::  (a <-> b)    ->  a -> Maybe b
applyPartial      (f :<->: _)  =   f

undef  ::  a <-> b
undef  =   const Nothing :<->: const Nothing

partial       ::  (a <=> b)    ->  (a <-> b)
partial           (f :<=>: g)  =   (f >>> Just) :<->: (g >>> Just)

unsafeTotal   ::  (a <-> b)    ->  (a <=> b)
unsafeTotal       (f :<->: g)  =   (f >>> fromJust) :<=>: (g >>> fromJust)
\end{code}
\caption{Utilities for partial and total
  bijections} \label{fig:partial-total}
\end{figure}

We now turn to developing tools for dealing with bijections involving
sum types. It is useful to have a type class for ``things which
compose in parallel''. If $f$ is some sort of relation between $A$ and
$A'$, and $g$ relates $B$ and $B'$, then their parallel sum
$f \parsum g$ relates the disjoint sums $A + B$ and $A' + B'$, which
we visualize by stacking vertically (\pref{fig:bij-sum}).
\begin{figure}
\begin{center}
\begin{diagram}[width=200]
  import Bijections

  dia =
    [ vsep 1
      [ drawGenBij tex (sg "A" .- lk "f" -.. sg "A'")
      , drawGenBij tex (sg "B" .- lk "g" -.. sg "B'")
      ]
    , tex "\\implies"
    , drawGenBij tex
      ((sg "A" +++ sg "B")
      .-  lks "f \\parsum g" [("A","A'"), ("B","B'")]
      -.. (sg "A'" +++ sg "B'"))
    ]
    # map centerY
    # hsep 1
\end{diagram}
\end{center}
\caption{Parallel composition (sum) of generalized bijections} \label{fig:bij-sum}
\end{figure}
For example, normal functions $A \to A'$ compose in parallel: if
$f : A \to A'$ and $g : B \to B'$ then $f \parsum g : A+B \to A'+B'$
is the function which runs $f$ on elements of $A$ and $g$ on elements
of $B$; we saw this parallel composition of functions in the
introduction.  Kleisli arrows over the same monad |m| also compose in
parallel: the parallel sum of $f : A \to_m A'$ and $g : B \to_m B'$
works the same as the parallel sum of normal functions, but has the
effects of whichever one actually runs.  Finally, since Kleisli arrows
compose in parallel, so can generalized bijections, by composing the
forward and backward directions separately.  The code is shown
in \pref{fig:par-comp}.

\begin{figure}
\begin{code}
class Category arr => Parallel arr where
  (|||) :: arr a c -> arr b d -> arr (a + b) (c + d)

instance Parallel (->) where
  (|||) = bimap

factor :: Functor m => m a + m b -> m (a + b)
factor = either (fmap Left) (fmap Right)

instance Monad m => Parallel (Kleisli m) where
  K f ||| K g = K ((f ||| g) >>> factor)

instance Monad m => Parallel (Bij m) where
  (B f g) ||| (B h i) = B (f ||| h) (g ||| i)
\end{code}
\caption{Parallel composition} \label{fig:par-comp}
\end{figure}

% Next, we can construct general bijections witnessing the
% associativity of the type-level sum constructor.  |assoc| is a
% generalized bijection relating $A + (B+C)$ to $(A+B)+C$:
% \begin{center}
% \begin{diagram}[width=60]
%   import Bijections

%   dia = drawGenBij tex
%     (
%       (sg "A" +++ (sg "B" +++ sg "C"))
%       .-  lks "\\mathit{assoc}" [("A","A"), ("B","B"), ("C","C")]
%       -.. ((sg "A" +++ sg "B") +++ sg "C")
%     )
% \end{diagram}
% \end{center}
% |reassocL| takes a generalized bijection between a nested sum and
% reassociates both sides, by composing with |inverse(assoc)| and |assoc|:
% \begin{center}
% \begin{diagram}[width=200]
%   import Bijections

%   dia =
%     [ drawGenBij tex
%         (   (sg "A" +++ (sg "B" +++ sg "C"))
%         .-  lk "f"
%         -.. (sg "A'" +++ (sg "B'" +++ sg "C'"))
%         )
%     , tex "\\implies"
%     , drawGenBij tex
%         (   ((sg "A" +++ sg "B") +++ sg "C")
%         .-  lks "\\overline{\\mathit{assoc}}" [("A","A"), ("B","B"), ("C","C")]
%         -.  (sg "A" +++ (sg "B" +++ sg "C"))
%         .-  lk "f"
%         -.  (sg "A'" +++ (sg "B'" +++ sg "C'"))
%         .-  lks "\\mathit{assoc}" [("A'","A'"), ("B'","B'"), ("C'","C'")]
%         -.. ((sg "A'" +++ sg "B'") +++ sg "C'")
%         )
%     ]
%     # map centerY
%     # hsep 1
% \end{diagram}
% \end{center}
% The code for |assoc| and |reassocL| is shown in \pref{fig:assoc}.

% \begin{figure}
% \begin{code}
% (<~>) :: Monad m => (a -> b) -> (b -> a) -> Bij m a b
% f <~> g = B (K (f >>> return) (K (g >>> return))

% assoc :: Monad m => Bij m (a + (b + c)) ((a + b) + c)
% assoc =
%   either (Left >>> Left) (either (Right >>> Left) Right)
%   <~>
%   either (either Left (Left >>> Right)) (Right >>> Right)

% reassocL
%   :: Monad m
%   => Bij m (a + (b + c)) (a' + (b' + c'))
%   -> Bij m ((a + b) + c) ((a' + b') + c')
% reassocL bij = inverse assoc >>> bij >>> assoc
% \end{code}
% \caption{Associativity of sum} \label{fig:assoc}
% \end{figure}

% % XXX put in reassocR iff we need it
% % reassocR
% %   :: Monad m
% %   => Bij m ((a + b) + c) ((a' + b') + c')
% %   -> Bij m (a + (b + c)) (a' + (b' + c'))
% % reassocR bij = assoc >>> bij >>> inverse assoc

We also define |left|, the partial bijection which injects $A$ into
$A + B$ in one direction, and drops $B$ in the other direction:
\begin{center}
  \begin{diagram}[width=60]
    import Bijections

    dia = drawGenBij tex
      ( sg "A" .- lks "\\mathit{left}" [("A","A")] -.. (sg "A" +++ sg "B") )
  \end{diagram}
\end{center}
From this we define the \term{left partial projection}.  If |f : A+B
<-> A'+B'|, then the left partial projection of $f$, denoted
|leftPartial(f)|, has the type |leftPartial(f) : A <-> A'|, and
consists of only those edges of |f| which go between |A| and |A'|.
Any edges involving elements in |B| or |B'| are dropped.  This can be
accomplished simply by sandwiching |f| in between |left| and
|inverse(left)|, as shown in \pref{fig:left-partial}; code for |left|
and |leftPartial| is shown in \pref{fig:left-partial-code}. (The
functions |right| and |rightPartial| could be defined similarly, but
we do not need them.) \pref{fig:left-partial-ex} shows an example of
computing the left partial projection |leftPartial(h)|, using the same
bijection $h$ from the introduction.
\begin{figure}
\begin{center}
\begin{diagram}[width=200]
  import Bijections

  dia =
    [ drawGenBij tex
        (   (sg "A" +++ sg "B")
        .-  lk "f"
        -.. (sg "A'" +++ sg "B'")
        )
    , tex "\\implies"
    , drawGenBij tex
        (   sg "A"
        .-  lks "\\mathit{left}" [("A","A")]
        -.  (sg "A" +++ sg "B")
        .-  lk "f"
        -.  (sg "A'" +++ sg "B'")
        .-  lks "\\overline{\\mathit{left}}" [("A'","A'")]
        -.. sg "A'"
        )
    ]
    # map centerY
    # hsep 1
\end{diagram}
\end{center}
\caption{Constructing the left partial projection via |left|} \label{fig:left-partial}
\end{figure}

\begin{figure}
\begin{code}
left :: a <-> a + b
left = (Left >>> Just) :<->: either Just (const Nothing)

leftPartial :: (a + b <-> a' + b') -> (a <-> a')
leftPartial f = left >>> f >>> inverse left
\end{code}
\caption{|left| and |leftPartial|} \label{fig:left-partial-code}
\end{figure}

\begin{figure}
  \centering
  \begin{diagram}[width=300]
    import Bijections

    dia = hsep 3
      [ drawBComplex (bcF # labelBC ["$h$"])
      , tex "\\implies"
      , lpF
        # labelBC ["$\\mathit{left}$", "$h$", "$\\overline{\\mathit{left}}$"]
        # drawBComplex
      , tex "="
      , ( a0
           .- single (mkABij a0 b0 succ) -..
          b0
        )
        # labelBC ["$\\langle\\Varid{h}||$"]
        # drawBComplex
      ]

    bcF = (a0 +++ a1) .- bijF -.. (b0 +++ b1)
    bijF = single $ mkABij (a0 +++ a1) (b0 +++ b1) ((`mod` 5) . succ) -- $

    lpF =
      a0
        .- single (mkABij a0 (a0 +++ a1) id) -.
      a0 +++ a1
        .- bijF -.
      b0 +++ b1
        .- single (mkABij (b0 +++ b1) b0 id) -..
      b0
  \end{diagram}
  \caption{Computing the left partial projection |leftPartial(h)|}
  \label{fig:left-partial-ex}
\end{figure}

% We don't actually need these laws since there's really nothing to
% prove!  Our definition of gmip was way too complicated; with a
% better definition the proof of equivalence between gmip and gcbp is
% two lines.

% We can write down a few algebraic laws about the way |left|, |assoc|,
% and parallel composition interact.  Rather than formal algebraic
% proofs, we give pictorial proofs instead.

% \begin{lem}
%   |left >>> inverse left = id|
% \end{lem}
% \begin{center}
% \begin{diagram}[width=150]
%     import Bijections

%     dia :: Diagram B
%     dia = hsep 1
%       [ b1
%       , tex "=" # translateY (-height b2 / 2)
%       , b2
%       ]
%       where
%         b1, b2 :: Diagram B
%         b2 = drawGenBij tex
%           ( sg "A" .- lk "" -.. sg "A" )
%         b1 = drawGenBij tex
%           ( sg "A"
%               .- lks "\\mathit{left}" [("A","A")] -.
%             (sg "A" +++ sg "B")
%               .- lks "\\overline{\\mathit{left}}" [("A","A")] -..
%             sg "A"
%           )
% \end{diagram}
% \end{center}

% Note that it is \emph{not} automatically the case that |f >>>
% inverse f = id| when |f| is a partial bijection; indeed, it is not even
% the case that |inverse left >>> left = id| (in fact |inverse left >>>
% left = id |||||| undef|).

% \begin{lem}
%   |left >>> assoc = left >>> left|
% \end{lem}
% \begin{center}
%   \begin{diagram}[width=240]
%   import Bijections

%   dia = hsep 1
%     [ drawGenBij tex
%       ( sg "A"
%           .- lks "\\mathit{left}" [("A","A")] -.
%         (sg "A" +++ (sg "B" +++ sg "C"))
%           .-  lks "\\mathit{assoc}" [("A","A"), ("B","B"), ("C","C")] -..
%         ((sg "A" +++ sg "B") +++ sg "C")
%       )
%     , tex "=" # translateY (-2)
%     , drawGenBij tex
%       ( sg "A"
%           .- lks "\\mathit{left}" [("A","A")] -.
%         (sg "A" +++ sg "B")
%           .- lks "\\mathit{left}" [("A","A"),("B","B")] -..
%         ((sg "A" +++ sg "B") +++ sg "C")
%       )
%     , tex "=" # translateY (-2)
%     , drawGenBij tex
%       ( sg "A"
%           .- lks "" [("A","A")] -..
%         ((sg "A" +++ sg "B") +++ sg "C")
%       )
%     ]
% \end{diagram}
% \end{center}

% By taking the inverse of both sides, we also deduce the corollary
% |inverse assoc >>> inverse left = inverse left >>> inverse left|.

% \begin{lem}
%   |left >>> (f |||||| g) = f >>> left|
% \end{lem}
% \begin{center}
%   \begin{diagram}[width=200]
%     import Bijections

%     dia = hsep 1
%       [ drawGenBij tex
%         ( sg "A"
%             .- lks "\\mathit{left}" [("A","A")] -.
%           (sg "A" +++ sg "B")
%             .- lks "f \\parsum g" [("A","A'"),("B","B'")] -..
%           (sg "A'" +++ sg "B'")
%         )
%       , tex "="
%       , drawGenBij tex
%         ( sg "A"
%             .- lks "f" [("A","A'")] -.
%           sg "A'"
%             .- lks "\\mathit{left}" [("A'","A'")] -..
%           (sg "A'" +++ sg "B'")
%         )
%       ]
% \end{diagram}
% \end{center}

\section{GCBP, take 1}

We now have the tools we need to construct a first attempt at a
high-level, point-free version of the Gordon Complementary Bijection
Principle.  Although this first version will ultimately turn out to be
unusable in practice, it has most of the important ingredients of the
more sophisticated variants developed later.

The basic idea will be to construct the diagram at the top of
\pref{fig:ping-pong} step-by-step, taking $h$ as a starting point and
building up the whole diagram incrementally, accumulating more
information about the final bijection as more elements land in the top
set, until all elements have landed in the top set and we can
stop. The left partial projection of the result (which keeps only the
top half of the diagram) will then be the bijection we are looking
for.
\begin{figure}[htp]
  \centering
  \begin{diagram}[width=200]
    import Bijections

    dia = vsep 1 . map centerX $ -- $
      [ gcbp
        # labelBC (cycle ["$h$", "$\\overline{g}$"])
        # drawBComplex
      , hsep 3
        [ arrowV (2 ^& 0)
        , ( a0 .-
              ( mkABij a0 b0 ((`mod` 3) . succ)
                # single
                # colorEdge (toNameI 0) (colors !! 4)
                # colorEdge (toNameI 1) (colors !! 4)
                # colorEdge (toNameI 2) (colors !! 5)
              ) -..
            b0
          )
          # labelBC ["$f$"]
          # drawBComplex
        ]
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
    bij2 = single $ mkABij (a0 +++ a1) (b0 +++ b1) ((`mod` 5) . succ) -- $
  \end{diagram}
  \caption{The GCBP construction}
  \label{fig:ping-pong}
\end{figure}

Unfortunately, \pref{fig:ping-pong} is misleading: if we literally
compose copies of $h$ and |inverse(g)| as shown at the top of the
figure and then take the left projection, we don't actually get the
desired $f$, but rather we get the partial bijection shown in
\pref{fig:ping-pong-wrong}.  The problem is that some of the paths
that we want to have in the final bijection actually stop short of the
last iteration, so they are lost when composing the entire diagram.
Only continuous paths from the top, leftmost set all the way to the
top, rightmost set survive the composition; in this case, there is
only one such path.  The classical, elementwise formulation of GCBP
specifies that the iteration for each particular element continues
only until landing in the target set; the number of iterations may be
different for each particular element.  When building GCBP at a higher
level, however, we must somehow keep track of everything at once.
\begin{figure}
  \centering
  \begin{diagram}[width=50]
    import Bijections

    dia = ( a0 .-
            (mkABij a0 b0 ([3,3,0]!!) # single # colorEdge (toNameI 2) (colors !! 5))
            -.. b0
          )
          # drawBComplex
  \end{diagram}
  \caption{The literal result of the composition in
    \pref{fig:ping-pong}}
  \label{fig:ping-pong-wrong}
\end{figure}

Let's see how we might start building up something like
\pref{fig:ping-pong}.  First of all, we can't compose
$h : A+B \bij A' + B'$ with $|inverse(g)| : B' \bij B$ directly, since
their types do not match. (Note, once again, that in typical mathematical
presentations, this is glossed over since a subtyping relationship
$B' \leq A' + B'$ is assumed.)  However, if we compose |inverse(g)| in
parallel with $|undef : A' <-> A|$ we get
\[ |undef |||||| inverse(g) : A'+B' <-> A+B|. \] Sequencing $h$ with
this followed by another copy of $h$ gives the first iteration of
GCBP, shown in \pref{fig:hg}.
\begin{figure}
  \centering
  \begin{diagram}[width=200]
    import Bijections

    dia = hsep 2
      [ ( (a0 +++ a1)
          .- single (mkABij (a0 +++ a1) (b0 +++ b1) ((`mod` 5) . succ)) -.
          (b0 +++ b1)
          .- (empty +++ reversing bij1) -.
          (a0 +++ a1)
          .- single (mkABij (a0 +++ a1) (b0 +++ b1) ((`mod` 5) . succ)) -..
          (b0 +++ b1)
        )
        # labelBC ["$h$", "$\\varnothing \\parsum \\overline{g}$", "$h$"]
        # drawBComplex
      , text "$=$"
      , ( (a0 +++ a1)
          .- single (mkABij (a0 +++ a1) (b0 +++ b1) (\n -> if n < 2 then 100 else (n+2))) -..
          (b0 +++ b1)
        )
        # drawBComplex
      ]
  \end{diagram}
  \caption{The first step of GCBP}
  \label{fig:hg}
\end{figure}
However, the problem crops up here already: the result of
$|h >>> (undef |||||| inverse(g))|$ is a partial bijection which is
undefined on the first two elements of $A$ (dark blue).  Those
elements already mapped to $B$ (light blue) under $h$, so they are
already ``done'': the only reason to keep iterating is to find out
what will happen to the third element.  But as soon as we start
iterating we lose the knowledge of what happened to the first two.

One (bad!) idea is to ``recycle'' elements that have landed in $B$,
sending them back to where they started so the cycle can repeat.  That
is, instead of taking the parallel sum of |inverse(g)| with |undef| at
each step, we take the parallel sum of |inverse(g)| with the inverse
of (the left partial projection of) whatever we have constructed so
far.  At the very first step this means using not |undef ||||||
inverse(g)| but the parallel sum of |leftPartial(inverse(h))| and |g|,
as shown in \pref{fig:hg2}.
\begin{figure}
  \centering
  \begin{diagram}[width=200]
    import Bijections

    dia = hsep 2
      [ ( (a0 +++ a1)
          .- single (mkABij (a0 +++ a1) (b0 +++ b1) ((`mod` 5) . succ)) -.
          (b0 +++ b1)
          .- (single (mkABij b0 a0 pred) +++ reversing bij1) -.
          (a0 +++ a1)
          .- single (mkABij (a0 +++ a1) (b0 +++ b1) ((`mod` 5) . succ)) -..
          (b0 +++ b1)
        )
        # labelBC ["$h$", "$\\langle \\overline{h} || \\parsum \\overline{g}$", "$h$"]
        # drawBComplex
      , text "$=$"
      , ( (a0 +++ a1)
          .- single (mkABij (a0 +++ a1) (b0 +++ b1) (\n -> if n < 2 then (n+1) else (n+2))) -..
          (b0 +++ b1)
        )
        # drawBComplex
      ]
  \end{diagram}
  \caption{The first step of GCBP, patched}
  \label{fig:hg2}
\end{figure}
On the second iteration, we would take the partial bijection
constructed so far, namely, \[ |f1 = h >>> (leftPartial(inverse(h)) |||||| inverse(g)) >>> h|, \]
and use its inverse to ``plug the hole'' over the second copy of
|inverse(g)|, that is,
\[ |f2 = f1 >>> (leftPartial(inverse(f1)) |||||| inverse(g)) >>> h|, \]
and so on; in general we would define
\[ |fip1 = fi >>> (leftPartial(inverse(fi)) |||||| inverse(g)) >>>
  h|. \] This ensures that every time a path lands in $B$, it
is sent back to the element in $A$ it started from, allowing it to
cycle through again while it is ``waiting'' for other elements to land
in $B$.

Unfortunately, this is quite inefficient.  For one thing, evaluating
each $f_{i+1}$ on a particular input requires evaluating two copies of
$f_i$, leading to exponential time complexity to evaluate $f_n$ at a
given input (at least barring any clever optimizations).  Second,
there is something else we have swept under the rug up to this point:
how do we know how long to keep iterating?  Note that because of the
way we send each path back to the start while waiting for other paths
to complete, at the point when the last path completes the others may
be in the middle of a cycle.  So in fact, we must iterate for a number
of steps equal to the least common multiple of the cycle lengths,
until all the cycles ``line up'' and the paths all land in $B$ at the
same time. This can be exponentially bad as well. For example, suppose
we have cycles of lengths $2$, $3$, $5$, $7$, and $11$: instead of
iterating just $11$ times, we have to wait through
$2\cdot 3 \cdot 5 \cdot 7 \cdot 11 = 2310$ iterations for all the
cycles to line up!  Even worse, computing the lengths of the cycles in
the first place would seem to require essentially running the original
pointful GCBP algorithm, nullifying the point of the whole exercise.

Fortunately, there is a much better way to emulate at a high level
what is really going on when we carry out the elementwise GCBP
process. To understand it, we must first explore a few more primitive
operations on partial bijections.

\section{Compatibility and merging}

We want to think of the iteration process as monotonically revealing
more and more information about the final bijection.  As soon as one
path completes, we have learned the fate of its starting element, and
once learned, we should never ``unlearn'' such a fact.  This motivates
thinking about partial bijections in terms of their information
content, and formalizing what it means for one partial bijection to be
``more informative'' than another.  We start by formalizing some
intuitive notions about partial \emph{functions}, and then lift them
to corresponding notions on partial bijections.

We say that two partial functions |f, g : A -> Maybe B| are
\term{compatible}, written $f \compat g$, if they agree at all points
where both are defined, that is, for all |a : A| and |b : B|, \[ |f a =
Just b| \text{ if and only if } |g a = Just b|. \] 

% Formally, $f \compat g$ if and only if |dom g
% >>> f = dom f >>> g|, that is, restricting $f$ to $g$'s domain yields
% the same partial function as restricting $g$ to $f$'s
% domain.

% \begin{diagram}[width=200]
% {-# LANGUAGE LambdaCase #-}
% import Bijections

% dia :: Diagram B
% dia = hsep 3
%   [ (a .- domg -. a .- f -.. b)
%     # labelBC ["$\\mathit{dom}\\; g$", "$f$"]
%     # drawBComplex
%   , text "$=$"
%   , (a .- common -.. b)
%     # drawBComplex
%   , text "$=$"
%   , (a .- domf -. a .- g -.. b)
%     # labelBC ["$\\mathit{dom}\\; f$", "$g$"]
%     # drawBComplex
%   ]
%   where
%     a = nset 4 (colors!!0)
%     b = nset 4 (colors!!2)
% f = single $ bijFun [0..3] (\case { 1 -> Just 0; 3 -> Just 3; _ -> Nothing}) -- $
% domf = single $ bijFun [0..3] (\case { 1 -> Just 1; 3 -> Just 3; _ -> Nothing}) -- $
% g = single $ bijFun [0..3] (\case { 0 -> Just 1; 1 -> Nothing; x -> Just x}) -- $
% domg = single $ bijFun [0..3] (\x -> if x `elem` [0,2,3] then Just x else Nothing) -- $
% common = single $ bijFun [0..3] (\case { 3 -> Just 3; _ -> Nothing}) -- $
% \end{diagram}

%% Tried making above picture to illustrate dom g ; f = dom f ; g but
%% it's too small.  Perhaps need to rethink it.  It's not that
%% important anyway.

% If |f| is a total function, |dom f = id|, and hence when |f| and |g|
% are total functions, $f \compat g$ if and only if $f = g$: since total
% functions are defined everywhere, the only way for them to be
% compatible is to be equal.

If two partial functions |f, g : A -> Maybe B| are compatible, we can
define their \term{merge} as \[ |(f <||||> g) x = f x <||> g x|, \]
where the |(<||>)| operator from the |Alternative| type class
(\pref{fig:mergeable}) merges |Maybe| values, yielding |Nothing| if
both arguments are |Nothing|, and the leftmost |Just| value otherwise.
In the case of compatible partial functions, however, when both |f x|
and |g x| are |Just|, they must be equal, so merging compatible
functions does not introduce any bias---that is, when $f$ and $g$ are
compatible, $f \mrg g = g \mrg f$.

These notions lift easily to the setting of partial bijections.  Two
partial bijections |f, g : A <-> B| are compatible if their forward
directions are compatible and their backward directions are
compatible; the merge of two compatible partial bijections $f \mrg g$
is computed by merging their forward and backward directions
separately.

We define a type class |Mergeable|, shown in \pref{fig:mergeable}, for
categories with a monoidal structure given by a binary operator
|(<||||>)| and a distinguished identity morphism |undef|.  Kleisli
arrows |Kleisli m a b| are |Mergeable| as long as the monad |m| has a
suitable monoidal structure (via an |Alternative| instance), and this
lifts to a corresponding instance of |Mergeable| for partial
bijections.
\begin{figure}
  \begin{spec}
class Applicative f => Alternative f where
  empty  :: f a
  (<|>)  :: f a -> f a -> f a

class Category arr => Mergeable arr where
  undef   :: arr a b
  (<||>)  :: arr a b -> arr a b -> arr a b

instance (Monad m, Alternative m) => Mergeable (Kleisli m) where
  undef = K (const empty)
  K f <||> K g = K $ \a -> f a <|> g a

instance Mergeable (<->) where
  undef = B undef undef
  (B f g) <||> ~(B f' g') = B (f <||> f') (g <||> g')
\end{spec}
%$
\caption{The |Mergeable| type class} \label{fig:mergeable}
\end{figure}
Notice that we use an \emph{irrefutable} (\ie lazy) \emph{pattern match} in the
definition of |(<||||>)| for partial bijections, which means |h <||||>
h'| can output something of the form |B (...) (...)| \emph{before}
demanding evaluation of |h'|.  Evaluation of |h'| will only be
demanded if evaluation of |h| on a particular input is undefined.
This ensures that a chain of merged partial bijections can be
evaluated lazily on each input, stopping as soon as the first
partial bijection defined on the given input is found.  This will be
especially important in the next section, in which we will fold an
\emph{infinite} list via |(<||||>)|.

\section{GCBP via merge}

As we have seen, the GCBP construction consists in starting with
$h : A+B \bij A'+B'$, and then iteratively extending it by the
composite |(undef |||||| inverse(g)) >>> h|.  Let us give a name to
this iterated operation:
\begin{spec}
extend g h k = k >>> (undef ||| inverse(g)) >>> h
\end{spec}
The leftmost column of \pref{fig:iterating-ext} shows an example of
iterating this extension operation.
\begin{figure}
  \centering
  \begin{diagram}[width=350]
    {-# LANGUAGE LambdaCase #-}

    import Bijections
    import Grid

    dia = grid' (with & colsep .~ 2 & rowsep .~ 2) $  -- $

      map (map alignL)
      [ [ text "$h$" <> strutX 2
        , text "$=$"
        , ( (a0 +++ a1)
            .- single h -..
            (b0 +++ b1)
          )
          # labelBC ["$h$"]
          # drawBComplex
          # alignL
        , text "$=$"
        ,
          ( (a0 +++ a1)
            .- single h -..
            (b0 +++ b1)
          )
          # drawBComplex
        , text "$\\implies$"
        ,
          ( a0 .- single (mkABij a0 b0 ([1,2,100]!!)) -.. b0 )
          # drawBComplex
        , text "$=$"
        , text "$\\langle h ||$" <> strutX 2
        ]
      , [ text "$\\mathit{ext}_{g,h} h$"
        , text "$=$"
        , ( (a0 +++ a1)
            .- single h -.
            (b0 +++ b1)
            .- (empty +++ reversing bij1) -.
            (a0 +++ a1)
            .- single h -..
            (b0 +++ b1)
          )
          # labelBC ["$h$", "$\\varnothing \\parsum \\overline{g}$", "$h$"]
          # drawBComplex
          # alignL
        , text "$=$"
        ,
          ( (a0 +++ a1)
            .- single (mkABij (a0 +++ a1) (b0 +++ b1) (\case { 2 -> 4; 3 -> 0; _ -> 100 })) -..
            (b0 +++ b1)
          )
          # drawBComplex
        , text "$\\implies$"
        ,
          ( a0 .- single (mkABij a0 b0 (const 100)) -.. b0 )
          # drawBComplex
        , text "$=$"
        , text "$\\langle \\mathit{ext}_{g,h} h ||$" <> strutX 2
        ]
      , [ text "$\\mathit{ext}_{g,h}^2 h$"
        , text "$=$"
        , ( (a0 +++ a1)
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
          # alignL
        , text "$=$"
        ,
          ( (a0 +++ a1)
            .- single (mkABij (a0 +++ a1) (b0 +++ b1) (\case { 2 -> 0; _ -> 100 })) -..
            (b0 +++ b1)
          )
          # drawBComplex
        , text "$\\implies$"
        ,
          ( a0 .- single (mkABij a0 b0 ([100,100,0]!!)) -.. b0 )
          # drawBComplex
        , text "$=$"
        , text "$\\langle \\mathit{ext}_{g,h}^2 h ||$" <> strutX 2
        ]
      ]
      where
        h = mkABij (a0 +++ a1) (b0 +++ b1) ((`mod` 5) . succ)
  \end{diagram}
  \caption{Iterating $\mathit{ext}_{g,h}$}
  \label{fig:iterating-ext}
\end{figure}
Consider this sequence of
partial bijections
\[ |h|,\quad |extend g h h|,\quad |extend g h^2 h|,\quad |extend g h^3
  h|,\quad \dots \] generated by iterating |extend g h|.  That is, the
first is $h$, the next is |h >>> (undef |||||| inverse(g)) >>> h|,
then
\[ |h >>> (undef |||||| inverse(g)) >>> h >>> (undef ||||||
  inverse(g)) >>> h|, \] and so on.  Now we take the left projection
of each, as illustrated in the rightmost column of
\pref{fig:iterating-ext}. In this particular example, all the left
partial projections produced are compatible with each other; and
moreover, the domains on which they are defined are completely
disjoint.  In fact, this is no coincidence: the partial bijections
|leftPartial(extend g h^n h)| will always be pairwise compatible.

Why is this?  The path an element of $A$ takes under iteration of
|extend g h| can bounce around in the bottom sets ($B$ and $B'$), but
stops once it reaches $A'$, since on the next iteration it will be
sequenced with |undef|.  Suppose it takes some $a \in A$ exactly $n$
iterations to reach some $a' \in A'$.  If we iterate fewer than $n$
times, $a$ will be mapped to some element of $B'$, and hence the left
projection will be undefined at $a$.  If we iterate exactly $n$ times,
$a$ will be mapped to $a' \in A'$, and hence it will map to $a'$ in
the left projection as well.  If we iterate more than $n$ times, the
resulting partial bijection will be undefined at $a$, because after
reaching $a'$ it will be composed with |undef|.  So for any given
$a \in A$, there is exactly one value of $n$ such that
|leftPartial(extend g h^n h)| is defined at $a$.  Also, there can
never be two different elements of $A$ which map to the same $A'$: two
paths can never ``converge'' in this way since we are composing
partial \emph{bijections}, which in particular are injective where
they are defined.

Hence, we are justified in considering the infinite merge
\[ |leftPartial(h) <||||> leftPartial(extend g h h) <||||>
  leftPartial(extend g h^2 h) <||||> leftPartial(extend g h^3 h)
  <||||> ...| \] For every element of $A$, there is some finite $n$
for which |leftPartial(extend g h^n h)| is defined on it, and hence
this infinite merge actually defines a \emph{total} bijection, so we
are justified in using |unsafeTotal| to convert it.  Again, because of
the irrefutable pattern match in the definition of |(<||||>)|, this
infinite expression only evaluates as far as necessary for any given
input.  Intuitively, this is doing exactly the same thing that the
original pointwise implementation of GCBP was doing, but without
having to explicitly talk about individual points $a \in A$.

With this insight, we can finally implement GCBP as follows:
\begin{code}
gcbp :: (a + b <=> a' + b') -> (b <=> b') -> (a <=> a')
gcbp h g = unsafeTotal . foldr1 (<||>) . map leftPartial . iterate (extend g' h') $ h'
  where
    g' = partial g
    h' = partial h
\end{code} %$
\pref{fig:gcbp-example} demonstrates this implementation of |gcbp| using our
running example.

The use of |unsafeTotal| reflects the fact that the totality of the
bijection constructed by |gcbp| still does not fall out ``by
construction''; the external reasoning outlined above is required to
show that the call to |unsafeTotal| is in fact safe.  On the other
hand, what does fall out by construction is the fact that the
resulting bijection is in fact a valid (partial) bijection, since it
is constructed by composing and merging more primitive bijections.
This is in contrast to the original pointwise definition of GCBP,
which requires separate external reasoning to show both properties.

\begin{figure}
\begin{spec}
unsafeBuildBijection :: (Eq a, Eq b) => [(a,b)] -> (a <=> b)
unsafeBuildBijection pairs = unsafeTotal (f :<->: g)
  where
    f = flip lookup pairs
    g = flip lookup (map swap pairs)

data Three = One | Two | Three deriving (Eq, Show, Ord, Enum)

h :: Three + Bool <=> Three + Bool
h = unsafeBuildBijection
  [ (Left One,     Left Two     )
  , (Left Two,     Left Three   )
  , (Left Three,   Right False  )
  , (Right False,  Right True   )
  , (Right True,   Left One     ) ]

g :: Bool <=> Bool
g = id :<=>: id
\end{spec}
\medskip

  \begin{diagram}[width=200]
    import Bijections

    dia = hsep 2
      [ drawBComplex (bc2 # labelBC ["$h$"])
      , text "$-$" # translateY (-2.5)
      , drawBComplex (bc1 # labelBC ["$g$"]) # translateY (-2.5)
      , text "$=$"
      , drawBComplex ((a0 .- bijResult -.. b0) # labelBC ["$f$"])
      ]
    bc2 = (a0 +++ a1) .- bij2 -.. (b0 +++ b1)
    bij2 = single $ mkABij (a0 +++ a1) (b0 +++ b1) ((`mod` 5) . succ) -- $
    bijResult = single $ mkABij a0 b0 ((`mod` 3) . succ)  -- $
  \end{diagram}
  \medskip

\begin{verbatim}
> map (applyTotal (gcbp h g)) [One, Two, Three]
[Two,Three,One]
\end{verbatim}

\caption{Testing |gcbp|} \label{fig:gcbp-example}
\end{figure}


% \section{The Garsia-Milne Involution Principle}
% \label{sec:gmip}

% There is an alternative principle, the \term{Garsia-Milne involution
%   principle} (GMIP) \citep{garsia1981method, zeilberger1984garsia},
% which also allows subtracting bijections.  Although at first blush it
% seems more complex and powerful than the Gordon principle, it turns
% out that the two are equivalent; the situation is reminiscent of the
% relationship between ``weak'' and ``strong'' induction on the natural
% numbers, which are equivalent despite their names.  Although the
% equivalence between GCBP and GMIP seems to be folklore, we have never
% seen a proof written down.  The proof is not hard---one might
% reasonably assign it as an exercise in an undergraduate course on
% combinatorics---but \todo{elaborate; something about the insight
%   afforded by our presentation.  Simpler presentation of GMIP, and
%   intuitive explanation of why they are equivalent.}

% Let us first see GMIP the way it is usually presented.
% The setup is illustrated in \pref{fig:GMIP}, and can be described as follows:
% \begin{itemize}
% \item There are two sets $A$ and $B$, each partitioned into a
%   ``positive'' part and a ``negative'' part.  In more type-theoretic
%   terms, $A$ and $B$ are disjoint sums---that is, $A = A^- + A^+$, and
%   similarly for $B$.
% \item There is a bijection $f^- : A^- \bij B^-$ between the negative
%   parts of $A$ and $B$, and similarly a bijection $f^+ : A^+ \bij
%   B^+$.
% \item Finally, there are \emph{signed involutions} $\alpha$ and
%   $\beta$ on $A$ and $B$ respectively.  That is, in the case of $\alpha$:
%   \begin{itemize}
%     \item $\alpha : A \bij A$ is a permutation of $A$ such that
%     \item all fixed points of $\alpha$ are in $A^+$;
%     \item all other, non-fixed elements are sent from $A^+$ to $A^-$
%       or vice versa (that is, $\alpha$ always switches the ``sign'' of
%       any element it does not fix); and
%     \item $\alpha$ is an involution, that is, $\alpha \circ \alpha = \id$.
%   \end{itemize}
%   Similarly, $\beta$ is a signed involution on $B$.
% \end{itemize}
% You may be forgiven for thinking this seems rather complex!  As we
% will see, however, a lot of the complexity is merely incidental.

% \begin{figure}
%   \centering
%   \begin{diagram}[width=200]
%     import Data.Bool  (bool)
%     import Data.Maybe (fromJust)

%     signedset name involution flip =
%       mconcat
%       [ text ("$" ++ name ++ "^+$") # translate ((bool negate id flip) 0.5 ^& 0.5)
%       , text ("$" ++ name ++ "^-$") # translate (0 ^& (-0.7))
%       , mconcat
%         [ circle 0.4 # dashingL [0.05, 0.05] 0
%         , text ("$\\Fix" ++ involution ++ "$") # fontSizeL 0.2
%         ]
%         # translate ((bool id negate flip) 0.3 ^& 0.7)
%       , circle 1 # scaleY 1.5
%       , hrule 2
%       ]
%       # fontSizeL 0.4
%       # named name

%     dia :: Diagram B
%     dia = hsep 2 [signedset "A" "\\alpha" False, signedset "B" "\\beta" True]
%       # arrowBetweenAtY   ht  "f^+" ["A", "B"]
%       # arrowBetweenAtY (-ht) "f^-" ["A", "B"]
%       # involutionArrow ht (-1) "\\alpha" "A"
%       # involutionArrow ht 1    "\\beta"  "B"
%       where
%         ht = 0.7

%     arrowBetweenAtY y lab nms = withNames nms $ \[a,b] ->    -- $
%       let oa = location a
%           ob = location b
%           e1 = fromJust (traceP (oa # translateY y) (oa .-. ob) a)
%           e2 = fromJust (traceP (ob # translateY y) (ob .-. oa) b)
%       in  atop
%             ( mconcat
%               [ arrowBetween' arrowOpts e1 e2
%               , text ("$" ++ lab ++ "$") # moveTo (lerp 0.5 e1 e2 # translateY 0.3)
%               ]
%               # fontSizeL 0.4
%             )

%     arrowOpts = with & gaps .~ local 0.2 & arrowTail .~ dart'

%     involutionArrow ht lr nm thing = withName thing $ \a ->   -- $
%       let e1 = fromJust (traceP (location a # translateY ht) (lr *^ unit_X) a)
%           e2 = fromJust (traceP (location a # translateY (-ht)) (lr *^ unit_X) a)
%       in  atop (
%             mconcat
%             [ arrowBetween' (arrowOpts & arrowShaft .~ arc yDir (-lr/2 @@@@ turn)) e1 e2
%             , text ("$" ++ nm ++ "$") # moveTo (location a # translateX (lr * 1.6))
%             ]
%             # fontSizeL 0.4
%           )
%   \end{diagram}
%   \caption{Setup for GMIP}
%   \label{fig:GMIP}
% \end{figure}
% Let $\Fix \alpha$ denote the set of fixed points of $\alpha$; by
% definition $\Fix \alpha \subseteq A^+$.  Clearly $||A^-|| = ||B^-||$
% (because of the existence of the bijection $f^-$), and similarly
% $||A^+|| = ||B^+||$ because of $f^+$. Also, since $\alpha$ is its own
% inverse, and ``sign-reversing'' on the elements it does not fix, it
% constitutes a bijection between $A^-$ and the unfixed elements of
% $A^+$; hence $||A^-|| = ||A^+|| - ||\Fix \alpha||$ and similarly
% $||B^-|| = ||B^+|| - ||\Fix \beta||$.  Putting this all together, we
% conclude that $||\Fix \alpha|| = ||\Fix \beta||$ as well.  The
% question is whether we can construct a canonical bijection
% $\Fix \alpha \bij \Fix \beta$ to witness this equality of
% cardinalities; the answer, of course, is yes.

% Start with some $a \in \Fix \alpha$ and apply $f^+$ once.  If we land
% in $\Fix \beta$, we are done.  Otherwise, we land in $B^+$ and we then
% ``go around the loop''
% \[
%   \xymatrix{
%     B^+ \ar[r]^{\beta} & B^- \ar[r]^{\overline{f^-}} & A^-
%     \ar[r]^{\alpha} & A^+ \ar[r]^{f^+} & ?,
%   }
% \]
% as illustrated in \pref{fig:GMIP-loop}.  We may land in
% $\Fix \beta$---in which case we map the original $a$ to that element
% of $\Fix \beta$---or we may land in $B^+$ again, in which case we
% repeat the procedure. The Pigeonhole Principle ensures that this
% process must end; it cannot ``get stuck'' because everything is a
% bijection.
% \begin{figure}
%   \centering
%   \begin{diagram}[width=200]
%     import Data.Bool  (bool)
%     import Data.Maybe (fromJust)

%     signedset name involution flip =
%       mconcat
%       [ text ("$" ++ name ++ "^+$") # translate ((bool negate id flip) 0.5 ^& 0.5)
%       , text ("$" ++ name ++ "^-$") # translate (0 ^& (-0.7))
%       , mconcat
%         [ circle 0.4 # dashingL [0.05, 0.05] 0
%         , text ("$\\Fix" ++ involution ++ "$") # fontSizeL 0.2
%         ]
%         # translate ((bool id negate flip) 0.3 ^& 0.7)
%       , circle 1 # scaleY 1.5
%       , hrule 2
%       ]
%       # fontSizeL 0.4
%       # named name

%     dia :: Diagram B
%     dia = mconcat
%       [ pt # named "start" # translate (0.3 ^& 0.9)
%       , pt # named "Bp"    # translate (4.3 ^& 0.9)
%       , pt # named "Bm"    # translate (4 ^& (-1.2))
%       , pt # named "Am"    # translate (0 ^& (-1.2))
%       , pt # named "Ap"    # translate ((-0.3) ^& 1.1)
%       , text "?" # fc red # fontSizeL 0.4 # named "FB?"   # translate (3 ^& 1.7)
%       , hsep 2 [signedset "A" "\\alpha" False, signedset "B" "\\beta" True]
%         # arrowBetweenAtY   ht  "f^+" ["A", "B"]
%         # arrowBetweenAtY (-ht) "f^-" ["A", "B"]
%         # involutionArrow ht (-1) "\\alpha" "A"
%         # involutionArrow ht 1    "\\beta"  "B"
%       ]
%       # connect' arrowOptsLoop "start" "Bp"
%       # connect' arrowOptsLoop "Bp" "Bm"
%       # connect' arrowOptsLoop "Bm" "Am"
%       # connect' arrowOptsLoop "Am" "Ap"
%       # connect' (arrowOptsLoop & shaftStyle %~ dashingL [0.05, 0.05] 0)
%           "Ap" "FB?"
%       where
%         ht = 0.7
%         pt = circle 0.07 # fc red # lw none

%     arrowBetweenAtY y lab nms = withNames nms $ \[a,b] ->    -- $
%       let oa = location a
%           ob = location b
%           e1 = fromJust (traceP (oa # translateY y) (oa .-. ob) a)
%           e2 = fromJust (traceP (ob # translateY y) (ob .-. oa) b)
%       in  atop
%             ( mconcat
%               [ arrowBetween' arrowOpts e1 e2
%               , text ("$" ++ lab ++ "$") # moveTo (lerp 0.5 e1 e2 # translateY 0.3)
%               ]
%               # fontSizeL 0.4
%             )

%     arrowOpts = with & gaps .~ local 0.2 & arrowTail .~ dart'
%     arrowOptsLoop = with & gaps .~ local 0.2
%                          & shaftStyle %~ lc red
%                          & headStyle  %~ fc red
%                          & tailStyle  %~ fc red
%                          & arrowShaft .~ arc xDir (-1/6 @@@@ turn)

%     involutionArrow ht lr nm thing = withName thing $ \a ->   -- $
%       let e1 = fromJust (traceP (location a # translateY ht) (lr *^ unit_X) a)
%           e2 = fromJust (traceP (location a # translateY (-ht)) (lr *^ unit_X) a)
%       in  atop (
%             mconcat
%             [ arrowBetween' (arrowOpts & arrowShaft .~ arc yDir (-lr/2 @@@@ turn)) e1 e2
%             , text ("$" ++ nm ++ "$") # moveTo (location a # translateX (lr * 1.6))
%             ]
%             # fontSizeL 0.4
%           )
%   \end{diagram}
%   \caption{Going around the loop in GMIP}
%   \label{fig:GMIP-loop}
% \end{figure}

% This seems suspiciously familiar!  In fact, there is a close
% relationship to the GCBP, but it is somewhat obscured by the way GMIP
% is usually presented.  First, let us see an alternative presentation
% of GMIP.  Suppose we have six sets $U$, $V$, $W$, $U'$, $V'$, $W'$,
% and four bijections:
% \begin{itemize}
% \item $f : U+V \bij U'+V'$
% \item $g : W \bij W'$
% \item $v : V \bij W$
% \item $v' : V' \bij W'$
% \end{itemize}
% This situation is illustrated in \pref{fig:alt-GMIP}.
% \begin{figure}
% \begin{diagram}[width=200]
%   import Bijections

%   dia =
%     drawGenBij tex
%       ( ((sg "U" +++ sg "V") +++ sg "W")
%           .-  lks "\\mathit{assoc}" [("A","A"), ("B","B"), ("C","C")] -..
%         ((sg "U'" +++ sg "V'") +++ sg "W'")
%       )
% \end{diagram}
% \caption{An alternate presentation of GMIP} \label{fig:alt-GMIP}
% \end{figure}
% Ultimately we are
% interested in constructing a bijection $U \bij U'$.  But we can easily
% construct a bijection $v ; g ; \overline{v'} : V \bij V'$, which we
% can then subtract from $f : U+V \bij U'+V'$ using GCBP.

% In fact, the situation described above is equivalent to the usual
% setup of GMIP:
% \begin{itemize}
% \item Define $A^+ = U + V$, $A^- = W$, $B^+ = U' + V'$, and $B^- =
%   W'$.
% \item Define $f^+ = f$ and $f^- = g$.
% \item What about the signed involutions $\alpha$ and $\beta$?  Since
%   $v : V \bij W$ is a bijection, we can make it into an involution on
%   $(U + V) + W = A^+ + A^- = A$ which fixes $U$ and swaps $V$ and
%   $W$.  Formally, we define $\alpha$ by
% \[
%   \xymatrix{
%     (U + V) + W \ar@@{<->}[d]^{|assoc|} & & (U + V) + W \ar@@{<->}[d]^{\overline{|assoc|}}\\
%     U + (V + W) \ar@@{<->}[r]^{\id + (v +
%       \overline{v})} & U + (W + V) \ar@@{<->}[r]^{\id + |swap|} & U + (V + W)
%   }
% \]
%   $\beta$ is defined similarly in terms of $v'$.
% \end{itemize}

% Conversely, given $A^+$, $A^-$, $f^+$, $f^-$, $\alpha$, and $\beta$:
% \begin{itemize}
% \item Define $U = \Fix \alpha$,
% \item $V = A^+ - \Fix \alpha$,
% \item $W = A^-$,
% \item and similarly define $U'$, $V'$, and $W'$ in terms of $\beta$,
%   $B^+$, and $B^-$.
% \item Finally define $v : V \bij W$ as the action of $\alpha$ on
%   $V$---the image of $\alpha$ on $V = A^+ - \Fix \alpha$ must be
%   $W = A^-$, and this must be a bijection since $\alpha$ is
%   self-inverse.
% \end{itemize}

% XXX So what's with the sign-reversing involutions?  (the
% principle is typically presented like this due to the specific way it
% often arises from inclusion-exclusion arguments in combinatorics,
% where sign-reversing involutions were already a familiar feature)

% We have already seen how to implement this reformulated GMIP in terms
% of GCBP. \todo{show code}

% What about implementing GCBP in terms of GMIP?  This can also be done,
% and it is not too hard: the trick is to duplicate $B$ and $B'$, like
% so: \todo{picture} \todo{show code}

% \todo{Formal equational proof that these are equivalent?}

\section{Efficiency I: memoization}
\label{sec:efficiency}

Let us return to consider the infinite merge used to compute |gcbp|:
\[ |leftPartial(h) <||||> leftPartial(extend g h h) <||||>
  leftPartial(extend g h^2 h) <||||> leftPartial(extend g h^3 h)
  <||||> ...| \] Operationally, to compute the output on some
particular $a$, we perform the following series of steps:
\begin{enumerate}
\item Check if |leftPartial(h) a| is defined.  If yes, output it and stop.
\item Check if |leftPartial(extend g h h) a = (h >>> (undef +
  inverse(g)) >>> h) a| is defined.  If yes, output it and stop.
\item Check if |leftPartial(extend g h^2 h) a = (h >>> (undef +
  inverse(g)) >>> h >>> (undef + inverse(g)) >>> h) a| is defined. If yes, output it and stop.
\end{enumerate}
\dots and so on.  In general, in order to compute |leftPartial(extend
g h^n h) a|, we must evaluate an expression of size linear in $n$.
Evaluating |applyTotal (gcbp h g) a| therefore takes time
\emph{quadratic} in the number of iterations required for |a|, because
we first evaluate a path of length $1$, then length $3$, then length
$5$, \dots until we finally evaluate the path that takes $a \in A$ all
the way to some $a' \in A'$.

As you may have already noticed, however, we are doing a lot of
duplicate work. for example, to check whether |(h >>> (undef +
inverse(g)) >>> h >>> (undef + inverse(g)) >>> h) a| is defined, we
first compute |(h >>> (undef + inverse(g)) >>> h) a| and then apply
|(undef + inverse(g)) >>> h| to the result---but we already computed
|(h >>> (undef + inverse(g)) >>> h) a| on the previous iteration.  In
general, the path followed on each iteration is the same as the path
from the previous iteration, extended by one step.

The solution is \emph{memoization}: along with each partial bijection,
we store a map associating inputs to their corresponding outputs.
corresponding outputs. With these maps in place, evaluating a partial
bijection on a particular input may take any amount of time initially,
but subsequent evaluations at the same input take (essentially)
constant time. This means that each iteration needs to do only a
constant amount of additional work, and the whole evaluation reduces
to linear time instead of quadratic.

\pref{fig:memo} shows some necessary utilities for memoization.  We
make use of Conal Elliott's \verb+MemoTrie+ package
\citep{elliott:memoization, elliott:memotrie}, which provides
facilities for automatically memoizing pure functions, making clever
use of GHC's lazy evaluation model to store a lookup table which is
lazily filled in on demand. |KleisliM| represents memoized Kleisli
arrows, with a special constructor |Id| for representing the identity
arrow (which does not need to be memoized).  The constructor |Memo| is
not exported; instead, a smart constructor |kleisliM| is provided
which automatically wraps the given |a -> m b| function in a call to
|MT.memo|, which memoizes it.  A |Category| instance for |KleisliM|
defines composition, which requires another call to |MT.memo| to
ensure that the result of composition is also memoized.  Finally
|runKleisliM| re-extracts a function of type |a -> m b| from a
|KleisliM m a b|.  Together, |kleisliM| and |runKleisliM| witness a
sort of isomorphism between |a -> m b| and |KleisliM m a b|.  The
trick is that although |runKleisliM (kleisliM f)| is
\emph{semantically} equivalent to |f|, it is not \emph{operationally}
equivalent: in particular, evaluating |runKleisliM (kleisliM f)|
multiple times on the same input will only evaluate |f| once.
\begin{figure}
  \centering
  \begin{spec}
import            Data.MemoTrie    (HasTrie)
import qualified  Data.MemoTrie    as MT

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
  \end{spec}
  \caption{Utilities for memoization}
  \label{fig:memo}
\end{figure}
% We also define a type |Memo| to represent memoized functions |a -> b|,
% along with a smart constructor |memo| and its inverse |apply|.

Now all we have to do is redefine |Bij m|, along with our pattern
synonyms for working with total and partial bijections
(\pref{fig:bij-redef}).
\begin{figure}
\begin{spec}
data Bij m a b = B
  { ^^ fwd  :: KleisliM m a b
  , ^^ bwd  :: KleisliM m b a
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
\end{spec}
\caption{Redefining |Bij m| with memoization} \label{fig:bij-redef}
\end{figure}
The syntax for the pattern synonyms becomes even more horrendous, but
the good news is that once we have defined them our troubles are
(mostly) over: all the other code gets to stay pretty much the same,
except that we have to add lots of |HasTrie| constraints everywhere,
including the types of the |Parallel| and |Mergeable| methods, since
we can no longer freely use any types we like, but only types for
which a memo table can be built.

To see the difference in performance between the non-memoized and
memoized versions, consider the bijection |h : A + B <=> A + B| which
sends each element to the ``next'' element, except for the last
element of |B| which gets sent back to the first element of |A|.
Indeed, the |h| in our running example is of this form, with
$||A|| = 3$ and $||B|| = 2$.  Subtracting the identity bijection on
|B| is a worst case for GCBP: although most elements in |A| need zero
iterations to reach their final destination (\ie just a single
application of |h|), the last element of |A| needs $||B||$ iterations
before it finishes travelling through every element of |B| and finally
reaches its destination.  \pref{fig:pessimal} exhibits some code which
constructs this scenario, with $A = B = \{0, \dots,
4999\}$. \pref{fig:test-pessimal} shows the result of some simple
timing experiments at the GHCi prompt: without memoization, the
bijection $f$ constructed by GCBP needs 30 seconds to compute |f
4999|, whereas with memoization, it only needs half a second.
  \begin{figure}
    \centering
\begin{code}
pessimal :: Integer -> Integer
         -> (Integer + Integer <=> Integer + Integer, Integer <=> Integer)
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
\end{code}
    \caption{Constructing a pessimal input for GCBP}
    \label{fig:pessimal}
  \end{figure}

  \begin{figure}
    \centering
\begin{verbatim}
> let (h,g) = pessimal 5000 5000
> let f = gcbp h g
> applyTotal f 4999   -- without memoization
0
(30.40 secs, 12,135,183,272 bytes)


> let (h,g) = pessimal 5000 5000
> let f = gcbp h g
> applyTotal f 4999   -- with memoization
0
(0.55 secs, 302,438,560 bytes)
\end{verbatim}

    \caption{Testing GCBP without (top) and with (bottom) memoization}
    \label{fig:test-pessimal}
  \end{figure}

\section{Efficiency II: naive composition}

However, there is still a problem: part of the point of implementing
GCBP in a high-level style was so that we could compute \emph{both}
directions of the bijection at once.  Memoization helps with the
\emph{forward} direction, because each iteration sequences a new
partial bijection \emph{on the right}, which means it goes
\emph{after} the part we have already computed.  In the backwards
direction, however, sequencing a new bijection on the right means
putting it \emph{before} the part we have already computed, and this
means that we cannot reuse our previous computation. When evaluating
the backward direction on a particular input, we have to start over
from scratch every time.

\begin{figure}
  \centering
\begin{verbatim}
> let (h,g) = pessimal 5000 5000
> let f = gcbp h g
> applyTotal f 4999          -- with memoization
0
(0.55 secs, 301,398,688 bytes)
> applyTotal (inverse f) 0   -- memoization doesn't help!
^CInterrupted.
\end{verbatim}
  \caption{Memoization doesn't help with the backwards direction}
  \label{fig:memo-backwards}
\end{figure}
\pref{fig:memo-backwards} has a sample GHCi session showing that
memoization doesn't help with the backwards direction.  Not only does
it take a long time, it tends to use up all available memory so that
it has to be killed.

The solution is the same as the punchline to the old joke:
\begin{quote}
  \textit{Patient: Doctor, it hurts when I do this.\\
    Doctor: Well, don't do that then.
  }
\end{quote}
% Given two |m|-bijections $|f, g :: Bij m a a|$, we define a
% ``na\"ive composition'' operator |(^.)| as follows:
% \begin{spec}
% (^.) :: (Bij m a a) -> (Bij m a a) -> (Bij m a a)
% (B f g) ^. (B f' g') = B (f . f') (g . g')
% \end{spec}
% Notice that |g| and |g'| are composed ``the wrong way around'', which
% necessitates the more restrictive type.

% Normally this would be useless, since in general |g . g'| is not the
% inverse of |f . f'|, even when the types are restricted in this way.
% But there is one situation in which this does yield something useful:
% when the bijection we ultimately want to compute is a palindrome!

% Above actually doesn't work, the version that simply does naive
% composition is too restrictive.  We need a version that takes an
% existing a <-> b  bijection and extends it with two more bijections
% at a time: one b <-> a and one a <-> b.

Since adding new partial bijections on the right causes memoization to
be useless for the backwards direction, let's not do that.  You may
protest that if we add new partial bijections on the \emph{left}
instead, we may fix the problem for the backwards direction but will
surely reintroduce the same problem for the forwards direction, and
you would be exactly right.  But that isn't what we're going to do.

Question: when is
\[ (f_1 f_2 f_3 \dots f_n)^{-1} = f_1^{-1} f_2^{-1} f_3^{-1} \dots
  f_n^{-1}? \] Answer: when $f_1 \dots f_n$ is a palindrome!  If $f_1
\dots f_n$ is a palindrome, it is equal to its own reversal, and hence
\[ (f_1 f_2 f_3 \dots f_n)^{-1} = (f_n \dots f_3 f_2 f_1)^{-1} =
  f_1^{-1} f_2^{-1} f_3^{-1} \dots  f_n^{-1}. \] Luckily,
GCBP is in fact computing a palindrome, namely,
$h \overline{g} h \overline{g} h \dots h$.  So we define an operation
|extendPalindrome g h| which in general turns $(h g)^n h$ into
$(h g)^{n+1} h$, by postcomposing with another copy of $g$ and $h$.
\begin{code}
extendPalindrome
  ::  (b <-> a) ->  (a <-> b) ->  (a <-> b) -> (a <-> b)

extendPalindrome     (g :<->: g')  (h :<->: h')  (f :<->: f')
  = (f >>> g >>> h) :<->: (f' >>> g' >>> h')
\end{code}
Notice how this composes $f'$, $g'$, and $h'$ ``backwards'': one would
expect
\[ |(f :<->: f') >>> (g :<->: g') >>> (h :<->: h') = (f >>> g >>> h)
  :<->: (h' >>> g' >>> f')|, \] but in this specific case the
``naive'' ordering works, since we know $f$ is a palindrome built from
|g| and |h|:
\[ hg[(hg)^n h] = [(hg)^n h] g h = (hg)^{n+1}h. \] If we redefine
|gcbp| using |extendPalindrome| in place of |ext|, as shown in
\pref{fig:opt-gcbp}, both the forwards and the backwards directions
will now be sequenced together in an order which allows them to take
advantage of memoization. \pref{fig:ext-pal} has one last sample GHCi
session showing that the backwards direction is now just as fast as
the forwards direction.
\begin{figure}
  \centering
  \begin{code}
gcbp' :: (a + b <=> a' + b') -> (b <=> b') -> (a <=> a')
gcbp' h g = unsafeTotal . foldr1 (<||>) . map leftPartial . iterate (extendPalindrome g' h') $ h'
  where
    g' = partial g
    h' = partial h
  \end{code} %$
  \caption{Optimized |gcbp| with |extendPalindrome|}
  \label{fig:opt-gcbp}
\end{figure}

\begin{figure}
  \centering

\begin{verbatim}
> let (h,g) = pessimal 5000 5000
> let f = gcbp' h g
> applyTotal f 4999
0
(0.55 secs, 301,398,688 bytes)
> applyTotal (inverse f) 0
4999
(0.25 secs, 181,462,968 bytes)
\end{verbatim}
  \caption{Forwards and backwards with memoization and
    |extendPalindrome|}
  \label{fig:ext-pal}
\end{figure}

\section{Conclusion}
\label{sec:conclusion}

In the end, what have we gained?  Certainly nothing of immediate
practical value: the original, pointwise implementation of GCBP is
probably still the fastest, and proving it correct is not too
difficult.  Though it is easier to see why the high-level
implementation must produce a bijection, it seems the same effort is
still required to see why the produced bijection is total.  And as
pointed out by several reviewers, proving the correctness of the
\emph{optimized} high-level implementation is probably much
\emph{harder} than proving the pointwise implementation correct in the
first place!

So why bother?  This work initially grew, not out of a need for a
solution or a desire to optimize, but out of a desire to
\emph{understand} the complementary bijection principle.  Re-imagining
the principle in a high-level, ``point-free'' way gives us much better
insight into the original problem, its solution, and related
ideas. For example, there is another principle, the celebrated
\emph{Garsia-Milne involution principle} \citep{garsia1981method},
which turns out to be equivalent to GCBP---and this becomes very easy
to see when thinking in terms of our point-free framework of partial
bijections.  Re-imagining GCBP at a higher level also yields potential
new opportunities for generalization.  For example, what happens when
we choose a monad other than |m = Maybe| for our |m|-bijections?  Is
there a deeper relationship between this work and traced monoidal
categories \citet{joyal1996traced}, and if so, what can it tell us?
Finally, the high-level construction also gives us new tradeoffs to
play with when writing a mechanized formal proof; although the
resulting formal proof may not be any shorter, we expect it will be
more modular, with more reusable pieces (and, perhaps, more pleasant
to write!).  Instead of proving many tedious statements about
individual elements, we can focus on proving higher-level properties
of partial bijections and their operations.

% \todo{joyal1996traced}

% \appendix
% \section{Appendix Title}

% This is the text of the appendix, if you need one.

\begin{acks}
  We would like to thank the anonymous reviewers for their many
  helpful comments and suggestions.  We also thank Jacques Carette for
  comments on a draft and pointing out some related work.

  This material is based upon work supported by the
  \grantsponsor{GS100000001}{National Science
    Foundation}{http://dx.doi.org/10.13039/100000001} under Grant
  No.~\grantnum{GS100000001}{1521539} and Grant
  No.~\grantnum{GS100000001}{1703835}.  Any opinions, findings, and
  conclusions or recommendations expressed in this material are those
  of the author and do not necessarily reflect the views of the
  National Science Foundation.
\end{acks}

\bibliography{GCBP-paper}

\end{document}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% MATERIAL ON PIE

% At first sight, however, it
% seems unmotivated and baroque.  To properly understand this principle,
% we must first take a detour through the \term{Principle of
%   Inclusion-Exclusion} (PIE).

% \subsection{The Principle of Inclusion-Exclusion}
% \label{sec:PIE}

% In its most basic version, PIE is usually presented in terms of unions
% and intersections of sets.  Given a finite collection of finite sets
% $S_1, S_2, \dots, S_n$, we can compute the size of their union in
% terms of the sizes of all possible intersections, adding intersections
% of an odd number of sets and subtracting even ones.  For example, when
% $n = 3$,
% \begin{multline*}
% ||S_1 \cup S_2 \cup S_3|| = ||S_1|| + ||S_2|| + ||S_3|| \\ - ||S_1 \cap S_2|| -
% ||S_1 \cap S_3|| - ||S_2 \cap S_3|| + ||S_1 \cap S_2 \cap S_3||.
% \end{multline*}
% We can write the general case as
% \[ \left|| \bigcup_{1 \leq i \leq n} S_i \right|| = \sum_{\substack{I
%     \subseteq \{1, \dots, n\} \\ I \neq \varnothing}} (-1)^{||I||+1}
% \left||\bigcap_{i \in I} S_i \right||, \]
% where the sum is taken over all nonempty subsets of $\{1, \dots, n\}$.
% Intuitively, adding the sizes of $S_1$ through $S_n$ overcounts
% elements in their intersections; subtracting elements in any
% intersection of two sets means elements in more than two sets are now
% undercounted; and so on.  Although the need for some sort of
% alternating sum seems intuitive, it is far from obvious that this is
% the right one.

% A proof can be given in terms of the binomial theorem, but we will not
% consider that proof here.  Instead, we consider a more abstract
% formulation of PIE, which leads to better notation and, more
% importantly, a lovely proof that avoids the need for any algebra
% whatsoever and paves the way for understanding GMIP.

% Suppose we have a finite set of elements $A$, and a finite set of
% properties $P$.  For each $p \in P$ and each $a \in A$, either $a$ has
% property $p$ (written $p(a)$) or it does not.  (To make the connection
% back to the previous formulation of PIE, we can identify each property
% $p$ with the subset $A_p = \{ a \in A \mid p(a) \}$ of elements of $A$
% having property $p$.)

% \newcommand{\ANP}{A_{\mathrm{NP}}}

% If $J \subseteq P$ is a subset of the set of properties, we write
% $J(a)$ to denote the fact that $a$ has all the properties in $J$.
% Likewise, we write $A_J = \{ a \in A \mid J(a) \}$ to denote the
% subset of $A$ with all the properties in $J$; note that
% $A_J = \bigcap_{p \in J} A_p$.  We have $A_\varnothing = A$, since
% every $a \in A$ trivially satisfies all the properties in the empty
% set of properties.  Finally, we write $\ANP$ to denote the set of
% those $a \in A$ with \emph{no} properties in $P$; that is,
% $\ANP = \{ a \in A \mid \forall p \in P.\, \neg p(a) \}$.

% \todo{Note this kind of setup is common in combinatorics.
%   Duality---same as looking for elements with \emph{all} properties;
%   just negate all the properties.}

% We may now express a generalized version of PIE as follows: \[
% ||\ANP|| = \sum_{J \subseteq P} (-1)^{||J||} ||A_J||. \] (The previous
% formulation of PIE can be recovered by subtracting both sides from
% $||A|| = ||A_\varnothing||$, and specializing from properties to
% subsets.)

% The following proof is due to \citet{zeilberger1984garsia}, and
% indirectly to \citet{garsia1981rogers}:

% \newcommand{\bigA}{\mathcal{A}}
% \newcommand{\bigAe}{\bigA_{\mathrm{even}}}
% \newcommand{\bigAo}{\bigA_{\mathrm{odd}}}
% \newcommand{\bigANP}{\bigA_{\mathrm{NP}}}

% \begin{proof}
%   Let
%   \[ \bigA = \{ (a, J) \mid a \in A, J \subseteq P, J(a) \} \]
%   be the set of pairs $(a,J)$ where $a$ has all the properties in $J$.
%   $\bigA$ is in general larger than $A$, since there may be multiple
%   elements of $\bigA$ for each element of $A$: whenever
%   $(a,J) \in \bigA$ and $J' \subseteq J$ then $(a,J') \in \bigA$ as
%   well.  Define $\bigAe$ to be the set of $(a,J) \in \bigA$ where
%   $||J||$ is even, and $\bigAo$ similarly.  Also let $\bigANP$ be the
%   set of those $(a,J)$ where $a$ has no properties---note that in this
%   case $J$ is necessarily empty, since $a$ must satisfy all the
%   properties in $J$.  Hence $||\bigANP|| = ||\ANP||$.

%   Pick an arbitrary ordering of the properties in $P$, and let $s(a)$
%   denote the smallest property possessed by $a$ (if $a$ has any
%   properties).  Then define $\alpha : \bigA \to \bigA$ by \[
%   \alpha(a, J) = \begin{cases} (a, J \cup \{ s(a) \}) & s(a) \notin
%     J \\ (a, J \setminus \{ s(a) \}) & s(a) \in J \\ (a,J) &
%     \text{$a$ has no properties} \end{cases} \]  That is, $\alpha$
%   toggles the presence of the smallest property possessed by $a$, or
%   acts as the identity if $a$ has no properties.  We observe the
%   following:
%   \begin{itemize}
%   \item $\alpha$ is an involution, that is, $\alpha^2 =
%     \id$, and hence $\alpha$ is a permutation of $\bigA$.
%   \item $\alpha$ always sends odd-size $J$ to even-size $J$, and vice
%     versa---except when $a$ has no properties (in which case $J =
%     \varnothing$ is even).
%   \end{itemize}
%   We conclude that $\alpha$ is a bijection bewteen $\bigAe \setminus
%   \bigANP$ and $\bigAo$, so in particular $||\bigAe|| - ||\bigANP|| =
%   ||\bigAo||$; rearranging, we have \[ ||\ANP|| = ||\bigANP|| = ||\bigAe|| -
%   ||\bigAo||. \] It remains only to show that \[ ||\bigAe|| -
%   ||\bigAo|| = \sum_{J \subseteq P} (-1)^{||J||} ||A_J||, \] which
%   follows from the fact that pairs $(a,J) \in \bigA$ are in 1-1
%   correspondence with elements of $A_J$.
% \end{proof}

% \todo{WHAT IS A COMPUTATIONAL INTERPRETATION OF PIE?}

% \todo{OMG, now that I go back and reread the Gordon paper I actually
%   understand what it is doing. It's constructing a bijection in
%   exactly this sort of PIE situation---with two families of sets that
%   are ``sieve-equivalent'', that is, we have bijections $f_J : A_J
%   \bij B_J$ for each $J \subseteq P$.}

% \todo{Note that Gordon himself claims GCBP is equivalent to GMIP, but
%   gives no proof.}

% \subsection{Signed involutions and GMIP}
% \label{sec:signed-involutions}

% \todo{Basic setup of a set $\bigA$ partitioned into a
%   ``positive''/``even'' part and a ``negative''/``odd'' part, with an
%   involution that fixes the set we are interested in and is otherwise
%   sign/parity-reversing.  This situation comes up all the
%   time---whenever PIE is involved.  GMIP builds on this situation,
%   saying what we can do when we have two such partitioned sets that
%   correspond.}

% \todo{Why would the situation of two related partitioned sets come up?
%   There is still some part of the story I'm missing\dots}

% \todo{check out garsia1981method.}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% OLD MATERIAL ON PARTIAL FUNCTIONS


% \subsection{Partial functions}

% Partial functions, in turn, are built atop the familiar |Maybe| monad,
% with
% \begin{spec}
% data Maybe a = Nothing | Just a
% \end{spec}
% and \emph{Kleisli composition} defined by
% \begin{spec}
% (<=<) :: (b -> Maybe c) -> (a -> Maybe b) -> (a -> Maybe c)
% f <=< g = \a -> g a >>= f
% \end{spec}
% We also define a partial order on |Maybe a| by setting $|Nothing|
% \sqsubset x$ for all |x :: Maybe a|, and taking $\sqsubseteq$ as
% the reflexive, transitive closure of $\sqsubset$ (though transitivity
% admittedly does not add much).  Intuitively, $x \sqsubseteq y$ if $y$
% is ``at least as defined as'' $x$.

% \todo{Partial functions: Kleisli category.  Definedness partial order
%   is pointwise.  Define sum, prove abides.  Define compatibility.
%   Define subsets as pfun $\subseteq$ id (benefit: restriction is just
%   composition).  Define dom operator.  Prove compatibility is the same
%   as $f . dom g = g . dom f$. Prove lemma involving dom of a
%   composition (with picture).  Finally, define merge of compatible
%   partial functions: use symbol $\sqcup$ since it's a join in the
%   partial order (should change Agda code to use this symbol too).}

% Using the |Maybe| monad, we can define the type of partial functions,
% \(a \rightharpoonup b\) as |a -> Maybe b|. This function space forms a Kleisli
% category; that is, they can be composed using the |(<=<)| operation,
% whose identity is the monadic |return|. We overload \(\circ\) and |id| throughout
% this paper for anything fitting a category structure.

% We define equivalence \(\approx\) on partial functions in the usual pointwise
% way---that they are equal on all possible inputs.

% Moreover, partial functions also participate in a partial order,
% determined by their pointwise defined-ness. That is to say, we define
% the partial order on partial functions \(\sqsubseteq\) as the pointwise lifting
% of the defined-ness partial order on |Maybe|, wherein |Nothing| \(\sqsubseteq\) |m|
% for all |m|, |Just x| \(\sqsubseteq\) |Just y| when |x = y|, and all other values
% are incomparable.

% These partial functions also allow a sum construction akin to that for
% ordinary functions.

% For some |f :: a| \(\rightharpoonup\) |b| and |h :: c | \(\rightharpoonup\) |d|, we define

% \begin{spec}
%   f + h = either (fmap Left . f) (fmap Right . h)
% \end{spec}

% \begin{proof}[Composition Abides Sum]
%   For all partial functions
%   \(f : B_0 \rightharpoonup C_0\), \(g : A_0 \rightharpoonup B_0\),
%   \(h : B_1 \rightharpoonup C_1\), \(k : A_1 \rightharpoonup B_1\),
%   the sum of compositions \((f \circ g) + (h \circ k)\) is equivalent to
%   the composition of sums \((f + h) \circ (g + k)\).
%   \todo{Needs proof, really needs diagram.}
% \end{proof}

% We say that two partial functions are \emph{compatible} if they agree on all
% inputs for which they are both defined---that is, |f| and |g| are compatible if
% for all inputs |x| for which |f x = Just y| and |g x = Just z|, \(y = z\).
% We will abbreviate this predicate as \(f\,||||\, g\).

% Another less point-wise way of stating compatibility for partial functions
% is to say that two functions are compatible when they are equal upon restriction
% to the other's domain. We define a new |dom| operator over partial functions,
% so that |dom f| is the identity on all inputs for which |f| is defined, and
% returns nothing for all inputs on which |f| is undefined.

% With |dom|, we can restate the notion of compatiblity in a point-free style:
% two functions |f| and |g| are compatible if and only if
% \(f \circ dom\ g \approx g \circ dom\ f\).

% \todo{Prove this.}



% \todo{Now define partial bijections as a pair of pfuns such that left,
%   right dom laws hold.  Note equivalence to other possible set of
%   laws.  Prove composition (using nicer equational proof).}
