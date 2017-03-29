\AgdaHide{
\begin{code}
module _ where
open import Function
open import Appendix
\end{code}}

\chapter{Fully Generic Functions}\label{ch:fullyg}

In this chapter we formally model fully generic programming in a
closed dependently typed language. We write fully generic functions in
the universe of \refsec{closed},
supporting user-declared datatypes while remaining closed.

Thus far, we have focused on defining concrete datatypes in our
universe of (inductive-recursive) algebraic types.
\textit{Smart constructors} (defined as functions, first demonstrated
\refsec{nondepalgtps}), for the type former and constructors of a
concrete algebraic datatypes, allow us
to \textit{construct} concrete types and their values while hiding
their generic encoding in terms of initial algebra
semantics. Similarly, \textit{pattern synonyms}
(demonstrated in \refsec{nondepalgtps}),
for constructors of
concrete types encoded using initial algebra semantics,
allow us to
\textit{deconstruct} generically encoded values by writing
functions defined by pattern matching
while hiding underlying algebraic encodings.

While smart constructors and pattern synonyms shelter users from
generic encodings when they construct and deconstruct
\textit{concrete} datatypes, fully generic programming requires users
to understand how to generically construct and deconstruct \textit{encoded}
datatypes, by applying and matching against the \Con{init}ial algebra
constructor of \Data{μ₁}. By definition, fully generic functions can
be applied to (and may return) values of any user-declared type, thus
understanding the underlying generic encoding is necessary. In this
chapter we define 4 fully generic functions:
\begin{enumerate}
\item \Fun{count}, in \refsec{gcount}, counting the number of nodes
  in a generically encoded value.
\item \Fun{lookup}, in \refsec{glookup}, looking up any subnode in a
  in a generically encoded value.
\item \Fun{update}, in \refsec{gupdate}, updating any subnode in a
  in a generically encoded value.
\item \Fun{ast}, in \refsec{gast}, marshalling any generically
  encoded value to an abstract syntax tree (AST), defined as a rose
  tree.
\end{enumerate}




\section{Fully Generic Count}\label{sec:gcount}

\section{Fully Generic Lookup}\label{sec:glookup}

\section{Fully Generic Update}\label{sec:gupdate}

\section{Fully Generic AST}\label{sec:gast}

