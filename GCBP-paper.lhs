% -*- mode: LaTeX; compile-command: "runhaskell Shake" -*-

\documentclass[preprint]{sigplanconf}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% lhs2TeX

%include polycode.fmt

%format a0
%format a1
%format b0
%format b1

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

Suppose we have four sets $A_0, A_1, B_0,$ and $B_1$ with bijections
$f_0 : A_0 \bij B_0$ and $f_1 : A_1 \bij B_1$, as illustrated in
\todo{make illustration}.  Then we can easily ``add'' these bijections
to produce a new bijection \[ f : A_0 + A_1 \bij B_0 + B_1 \]
(where $+$ denotes the disjoint union of sets): we just take
$f = f_0 + f_1$, that is, the function which applies $f_0$ when given
an $A_0$, and $f_1$ when given an $A_1$. That is, in Haskell,
\begin{code}
type (+) = Either

(+) :: (a0 -> b0) -> (a1 -> b1) -> (a0 + a1 -> b0 + b1)
(f + g) (Left x)   = Left   (f x)
(f + g) (Right y)  = Right  (g y)
\end{code}
$(f + g)$ is a bijection as long as $f$ and $g$ are.

So we can define the \emph{sum} of two bijections.  What about the
\emph{difference}?  That is, given
\[ f : A_0 + A_1 \bij B_0 + B_1 \] and
\[ f_1 : A_1 \bij B_1, \] can we compute some
\[ f_0 : A_0 \bij B_0? \]

This comes up in combinatorics, when \todo{finish}.  \todo{Also definition of
virtual species, XXX other places.}

Certainly we can say that $A_0$ and $B_0$ have the same size: the
existence of the bijections $f$ and $f_1$ tell us that
$|A_0 + A_1| = |B_0 + B_1|$ and $|A_1| = |B_1|$; since, in general,
$|X + Y| = |X| + |Y|$, we can just subtract sizes to conclude that
$|A_0| = |B_0|$.  So, if we are willing to use the law of excluded
middle, we can say that there \emph{must exist} some bijection
$A_0 \bij B_0$.  But what if we want to actually \emph{compute} a
concrete bijection $A_0 \bij B_0$?  Then LEM is too big a
sledgehammer: we need something more subtle.

To see why this problem is not as trivial as it may first seem,
consider \todo{figure}.  The bijection $A_0 + A_1 \bij B_0 + B_1$ may
arbitrarily mix elements, so we cannot just drop $A_1$ and $B_1$.
Some of the elements in $A_0$ may map to elements in $B_1$, and vice
versa.

An algorithmically elegant solution was introduced by \todo{cite Gordon}.

\appendix
\section{Appendix Title}

This is the text of the appendix, if you need one.

\acks

Acknowledgments, if needed.

% We recommend abbrvnat bibliography style.

\bibliographystyle{abbrvnat}

% The bibliography should be embedded for final submission.

% \begin{thebibliography}{}
% \softraggedright

% \bibitem[Smith et~al.(2009)Smith, Jones]{smith02}
% P. Q. Smith, and X. Y. Jones. ...reference text...

% \end{thebibliography}


\end{document}
