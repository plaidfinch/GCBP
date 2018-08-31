% -*- mode: LaTeX; compile-command: "./build.sh" -*-

\documentclass[xcolor=svgnames,12pt]{beamer}

%include polycode.fmt

\renewcommand{\onelinecomment}{--- \itshape}
\renewcommand{\Varid}[1]{{\color{blue}{\mathit{#1}}}}

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

% uncomment me to get 4 slides per page for printing
% \usepackage{pgfpages}
% \pgfpagesuselayout{4 on 1}[uspaper, border shrink=5mm]

% \setbeameroption{show only notes}

\usepackage[english]{babel}
\usepackage{graphicx}
\usepackage{ulem}
\usepackage{url}
\usepackage{fancyvrb}

\graphicspath{{images/}}

\title{Title}
\date{Venue \\ Date}
\author{Brent Yorgey \\ University of Pennsylvania}

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

\end{document}

