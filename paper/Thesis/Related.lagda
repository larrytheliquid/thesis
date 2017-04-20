\AgdaHide{
\begin{code}
module _ where
open import Function
open import Appendix
open import Data.Nat hiding ( zero ; suc ; _+_ )
open Prim
open Alg
open ClosedHier
open import HierIR
open Nat
\end{code}}

\chapter{Related Work}\label{ch:related}

In discussing work related to generic programming,
the topic of this dissertation,
we only consider generic programming within dependent type
theory. Namely, intrinsically type-safe generic programming as
dependent functions over some universe,
taking a code argument (\Var{A} : \Data{Code})
and a subsequent dependentlty typed argument,
whose type is the meaning of the
code (\Fun{⟦ \Var{A} ⟧})
within type theory:

\AgdaHide{
\begin{code}
module _ where
 private
  postulate
   Code : Set
   ⟦_⟧ : Code → Set
   ⋯ : Set
\end{code}}

\begin{code}
   generic : (A : Code) → ⟦ A ⟧ → ⋯
\end{code}


\section{Fixed Open or Closed Universes}

By a fixed universe, we mean a universe that encodes some fixed number
of type formers, but does not support encoding encoding user-declared
datatypes. Generic programming over fixed universe,
whether it is open (as in \refsec{openu}) or
closed (as in \refsec{closedu}) is standard
dependently typed programming practice.

For example, Oury and Swierstra~\cite{oury:tpop} demonstrate
``The Power of Pi'' (or dependently typed programming),
by creating a file \Data{Format} universe, and writing
\textit{fully generic} \Fun{parse} and \Fun{print} functions for all
file formats that the universe encodes.
The universe is closed under (among other things)
dependent pair formation (whose code they call \Con{Read}), as well as a base
universe (\Data{U}) encoding bits, characters, natural numbers, and
even vectors. Even though \Fun{parse} and \Fun{print} are
\textit{fully generic functions}, they are defined over a fixed
universe of types. This makes sense for the problem at hand, where
file formats should be able to use the dependenty type of vectors to
encode the length of the remaining file format, after reading a
natural number specifiying said length. In their setting, it does not
make sense to support arbitrary user-declared types when defining file
formats. In contrast, our goal is to model an entire closed
dependently typed programming language
(as in \refsec{closed} or \refsec{hierir}), rather than file formats,
so this dissertation concerns itself with a closed
\textit{extendable} universe (by user-declared datatypes).

\section{Open Algebraic Universes}

%% \section{Closed Well-Order Universe}

\section{Nearly Closed Algebraic Universes}
