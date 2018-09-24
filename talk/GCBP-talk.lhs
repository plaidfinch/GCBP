% -*- mode: LaTeX; compile-command: "./build.sh" -*-

\documentclass[xcolor={usenames,dvipsnames,svgnames,table},12pt,aspectratio=169]{beamer}

%include polycode.fmt

%format Either = "\Tycon{Either}"

%format a    = "\SetA{a}"
%format a'   = "\SetAP{a^{\prime}}"
%format b    = "\SetB{b}"
%format b'   = "\SetBP{b^{\prime}}"

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
    XXX solution
  \end{xframe}

\end{document}
