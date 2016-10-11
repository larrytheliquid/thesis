\documentclass[12pt]{report}
\usepackage{psu-thesis}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\usepackage{amsmath,amsfonts,amssymb,textgreek,stmaryrd}
\usepackage{bbm}
\usepackage[greek,english]{babel}
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{autofe}
\usepackage[references]{agda}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\usepackage{amsthm}
\usepackage{lmodern}
\usepackage[sort&compress,square,comma,numbers,longnamesfirst]{natbib}
\usepackage{semantic}
\usepackage[hang]{caption}
\usepackage{color}
\usepackage{tcolorbox}
\usepackage{comment}
\usepackage{textcomp}
\usepackage{dashbox}
\usepackage{lscape}
\usepackage{afterpage}
\usepackage{url}
\usepackage{listings}
\usepackage[normal]{subfigure}
\usepackage[all]{xy}
\usepackage{enumerate}
\usepackage[shortlabels]{enumitem}
\usepackage{makeidx}
\usepackage{hyperref}

\usepackage[subfigure]{tocloft}
\usepackage[titletoc]{appendix}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\DeclareUnicodeCharacter{8759}{\ensuremath{::}}
\DeclareUnicodeCharacter{10218}{\guillemotleft}
\DeclareUnicodeCharacter{10219}{\guillemotright}

\newcommand{\cL}{{\cal L}}

\newcommand{\refsec}[1]{Section \ref{sec:#1}}
\newcommand{\AgdaData}[1]{\AgdaDatatype{#1}}
\newcommand{\AgdaCon}[1]{\AgdaInductiveConstructor{#1}}
\newcommand{\AgdaFun}[1]{\AgdaFunction{#1}}
\newcommand{\AgdaVar}[1]{\AgdaBound{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\renewcommand{\contentsname}{Table of Contents}

\addtocontents{toc}{\protect\renewcommand{\protect\cftpartpresnum}{\partname\;}}
\addtocontents{toc}{\protect\renewcommand{\protect\cftchappresnum}{\chaptername\;}}
\setlength{\cftchapnumwidth}{\widthof{\sc\chaptername~00~~~}}

\makeindex

\definecolor{grey}{rgb}{0.8,0.8,0.8}
\definecolor{gray}{rgb}{0.57,0.57,0.57}

\setlist{partopsep=-3em}
\setlist{topsep=-3em}
\setlist{parsep=-2em}
\setlist{itemsep=-.2em}

\newcommand{\Fig}[1]{Figure~\ref{fig:#1}}

\newcommand{\cf}[0]{{cf.}}
\newcommand{\eg}[0]{{e.g.}}
\newcommand{\ie}[0]{{i.e.}}
\newcommand{\aka}[0]{{a.k.a.}}

\newtheorem{proposition}{Proposition}
\newtheorem*{proposition*}{Proposition}
\newtheorem{theorem}{Theorem}
\newtheorem{lemma}{Lemma}
\newtheorem{corollary}{Corollary}
\newtheorem{conjecture}{Conjecture}
\theoremstyle{definition}
\newtheorem{definition}{Definition}
\newtheorem{example}{Example}
\theoremstyle{remark}
\newtheorem{remark}{Remark}

\numberwithin{definition}{section}
\numberwithin{equation}{section}
\numberwithin{proposition}{section}
\numberwithin{conjecture}{section}
\numberwithin{theorem}{section}
\numberwithin{lemma}{section}
\numberwithin{corollary}{section}
\numberwithin{example}{section}
\numberwithin{remark}{section}


\newcommand{\Title}{Generic Dependently Typed Programming\\and Closed Universes}

\begin{document}

\AgdaHide{
\begin{code}
module Thesis where
\end{code}}

\title{\Title}
\titleline{\Title}

\author{Larry Diehl}
\principaladviser{Tim Sheard}{\ }
\firstreader{James Hook}
\secondreader{Mark P. Jones}
\thirdreader{Andrew Tolmach}
\graduaterepresentative{Robert Bass}
\departmenthead{Warren Harrison}
\grantdate{January}{1}{2017}

\titlep
\prefatory
\prefacesection{Abstract}
\vskip-5.5ex
$~~~~~~$Abstract goes here.

\prefacesection{Dedication} 
Dedication goes here.

\prefacesection{Acknowledgments}
Acknowledgments go here.
\newpage

\afterpreface
\body

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\part{Prelude}\label{part:prelude}

\chapter{Introduction}\label{ch:intro}
\section{Motivation}
\section{Depedently Typed Generic Programming}
\section{Agda Color Conventions}

\chapter{Algebraic \& Computational Datatypes}\label{ch:algcomp}
\section{Algebraic \& Computational Datatypes}
\section{Computational Argument \& Return Types}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\part{Open Type Theory}\label{part:open}

\chapter{Open Algebraic Datatypes}\label{ch:desc}
\section{Dependent Types}
\section{Indexed Types}
\section{Inductive-Recursive Types}
\section{Indexed Inductive-Recursive Types}
\chapter{Type Theory as a DSL}\label{ch:gelim}
\section{Generic Type Former}
\section{Generic Constructor}
\section{Generic Eliminator}
\section{Generic Type Declaration}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\part{Closed Type Theory}\label{part:closed}

\chapter{Closed Type Universes}\label{ch:closed}
\section{Closure under W Types}
\section{Closure under $\mu$ Types}
\chapter{Generic Lookup \& Replace}\label{ch:greplace}
\section{Generic Lookup}
\section{Generic Replace}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\part{Hierarchical Closed Type Theory}\label{part:hier}

\chapter{Closed Hierarchy of Universes}\label{ch:hier}
\chapter{Generic Datatype Arguments}\label{ch:gargs}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\part{Large Datatype Constructions}\label{part:large}

\chapter{Small Slice \& Family Equivalence}\label{ch:equiv}
\chapter{Large Induction-Recursion}\label{ch:largeir}
\chapter{Large Recursion-Induction}\label{ch:largeri}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\part{Postlude}\label{part:postlude}
\chapter{Related Work}\label{ch:related}
\chapter{Future Work}\label{ch:future}
\chapter{Conclusion}\label{ch:conc}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% \addtocontents{toc}{\protect\renewcommand{\protect\cftpartpresnum}{}}
%% \addtocontents{toc}{\protect\renewcommand{\protect\cftchappresnum}{}}
%% \clearpage
%% \phantomsection{}
%% \addcontentsline{toc}{part}{Bibliography}
%% \bibliographystyle{plainnat}
%% \bibliography{thesis}

%% \clearpage
%% \phantomsection
%% \addcontentsline{toc}{part}{Index}
%% {\small
%% \begin{singlespace}
%% \printindex
%% \end{singlespace}
%% }

%% \clearpage
%% \begin{appendices}
%% \include{appendix}
%% \end{appendices}

\end{document}

