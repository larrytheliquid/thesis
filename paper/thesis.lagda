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
\setlength{\cftchapnumwidth}{\widthof{\sc\chaptername~00~}}

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


\newcommand{\Title}{Closed-Universe\\Generic Dependently Typed Programming}

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
%%%% %% esac

\afterpreface
\body

Body goes there.


%% %% BEGIN PART1
%% \part{Prelude}\label{part:Prelude}
%% \include{intro}   %% Introduction                          {ch:intro}
%% \include{poly}    %% Polymorphic type systems              {ch:poly}
%% %% END PART1

%% %% BEGIN PART2
%% \part{Mendler style}\label{part:Mendler}
%% \include{mendler} %% Mendler-style recursion schemes       {ch:mendler}
%% %% END PART2

%% %% BEGIN PART3
%% \part{Term-Indexed Lambda Calculi}\label{part:Calculi}
%% \include{fi}      %% System Fi                             {ch:fi}
%% \include{fixi}    %% System Fixi                           {ch:fixi}
%% %% END PART3

%% %% BEGIN PART4
%% \part{Nax Language}\label{part:Nax}
%% \include{nax}     %% The Nax language                      {ch:nax}
%% %%%% \include{casestd} %% Case studies                          {ch:casestd}
%% %% END PART4

%% %% BEGIN PART5
%% \part{Postlude}\label{part:Postlude}
%% \include{relwork} %% Related work                          {ch:relwork}
%% \include{futwork} %% Future work                           {ch:futwork}
%% \include{concl}   %% Conclusion                            {ch:concl}
%% %% END PART5

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

