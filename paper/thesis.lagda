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
\section{Depedently Typed Universes \& Generic Programming}

%% could do universe of bool closed under list formation (all and any functions)

%% then Dan PLMW licata's (also Ulf gist and idris github) printf
%% extend this to Vec IR Format types from Power of Pi
%% extend this to codes for function types
%%   and domain supplement for how to print function types

%% typed Format strings as:
%% "Hello " < %nat > " world."
%% 3 , tt

%% hardcoded collection of types, what if we want to define this for
%% any type in the language?

%% bool + list universe
%% domain specific functions like any and all
%% domain generic functions like show/lookup/update
%% maybe domain generic elim...

%% maybe extend elim from just Desc/Mu to also Type

%% lookup and update of Bool/List scales to Set/List
%% any/all of Bool/List do not scale to Set/List
%%%% if this Set is Bool, and its value is true, then true else false
%%%% or if this Set is any type with two arguments, and value is right injection
%%%% or any type with >1 argument, any constructor besides first is true
%%%% now we can show expanding closed universe with Vec and cons is true
%%%% or just add Prod and Sum for conjuction and disjunction
%% however Any/All works for (Bool -> Set)/List (open universe) or Set/List

\section{Agda Color Conventions}

%% Inductive \& Recursive Type Families
%% inductive introduces new inductiion principle, recursive derives
%% from IP of index
\chapter{Algebraic \& Computational Datatypes}\label{ch:algcomp}
\section{Algebraic \& Computational Datatypes}
\section{Computational Argument \& Return Types}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\part{Open Type Theory}\label{part:open}

\chapter{Open Algebraic Datatypes}\label{ch:desc}
\section{Dependent Types}
%% start with Func, then specialize to mutual Args
%% List, Rose, and Term
\section{Indexed Types}
%% Vec, BigStep, ScopedTerm
%% show both constructor Vec and computational Vec
%% Algebraic = Inductve, Computational = Recursive
%% Algebraic Type Families vs Computational Type Families
%% vs Computational-Algebraic Type Families
%% PRE: Recursive-Inductive Families of Types
%% FINAL: Recursive-Inductive Families of Inductive-Recursive Types
\section{Inductive-Recursive Types}
%% Arith, Type
\section{Indexed Inductive-Recursive Types}
%% Norm

\chapter{Type Theory as a DSL}\label{ch:gelim}
%% write example using anon pattern matching lambdas
%% then same example using only elims for pairs
\section{Generic Type Former}
\section{Generic Constructor}
\section{Generic Eliminator}
%% Hyps an example of domain-supplement to ind

%% First chapter on regular generic-elim/Swedish
%% Second on index and parameter awareness
%% Third on `Desc codes with implicit args and FO \delta

%% OPEN generic example of lookup/update only at recursive positions
%% this should make index-preservation easy to state

%% data List (A : Set) : Set really module Foo (A : Set) data List : Set -> Set

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\part{Closed Type Theory}\label{part:closed}

%% maybe show how lookup/update cannot effectively work in open
%% universe for certain types, and maybe show closed univ elim
%% (extending elim to Type too)

%% generalized universe
%% not Uni (U : Set) (El : U -> Set)
%% but Uni (A : Set a) (B : Set b) (U : A) (El : U -> B) : suc (max a b)

\chapter{Closed Type Universes}\label{ch:closed}
\section{Closure under W Types}
\chapter{Closure under First-Order Types}\label{ch:closed}
\section{Closure under $\mu$ Types}
\chapter{Generic Lookup \& Update}\label{ch:gupdate}
%% PropVecRose for needing inductive PathVec and update of type family
%% ConstantVecRose for update of infinitary value
\section{Generic Lookup}
\section{Generic Update}

%% combinator for congruence over restricted Desc (no Bool/Sum or
%% kappa), doing congruence for Type cases (GP tactical)

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

\part{Irish Encodings}\label{part:irish}
\chapter{Irish Descriptions}\label{ch:irish}
\chapter{Description-Only Closed Universes}\label{ch:desconly}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\part{Postlude}\label{part:postlude}
\chapter{Inductive vs Recursive Families}\label{ch:related}
%% when to use one over the other
\chapter{Related Work}\label{ch:related}
%% comparison with other Desc representations
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

