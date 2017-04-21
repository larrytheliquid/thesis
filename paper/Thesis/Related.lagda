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
   generic : (A : Code) (a : ⟦ A ⟧) → ⋯
\end{code}


\section{Fixed Open or Closed Universes}

By a \textit{fixed} universe, we mean a universe that encodes some fixed number
of type formers, but does not support encoding encoding user-declared
datatypes. Generic programming over fixed universe,
whether it is open (as in \refsec{openu}) or
closed (as in \refsec{closedu}) is standard
dependently typed programming practice.

\paragraph{File Formats}

For example, Oury and Swierstra~\cite{oury:tpop} demonstrate
``The Power of Pi'' (or dependently typed programming),
by creating a file \Data{Format} universe, and writing
\textit{fully generic} \Fun{parse} and \Fun{print} functions for all
file formats that the universe encodes.
The universe is closed under (among other things)
dependent pair formation (whose code they call \Con{Read}), as well as a base
universe (\Data{U}) encoding bits, characters, natural numbers, and
even vectors.

Even though \Fun{parse} and \Fun{print} are
\textit{fully generic functions}, they are defined over a fixed
universe of types. This makes sense for the problem at hand, where
file formats should be able to use dependent pairs and vectors to
encode the length of the remaining file format, after reading a
natural number specifiying said length. In their setting, it does not
make sense to support arbitrary user-declared types when defining file
formats. In contrast, our goal is to model an entire closed
dependently typed programming language
(as in \refsec{closed} or \refsec{hierir}), rather than file formats,
so this dissertation concerns itself with a closed
\textit{extendable} universe (by user-declared datatypes).

\paragraph{Termination}

A more theoretical example of generic programming is Coquand's proof
that an operational semantics of type theory terminates
~\cite{coquand:realizability}. This is achieved using a logical
relation defined as an inductive-recursive universe, which can
be viewed an extension of a universe of
natural numbers (\Con{`ℕ}),
closed under dependent function
formation (\Con{`Π}).

The codes (\Data{Ψ}) of the logical relation are
additionally indexed by a syntax of expressions (\Data{ε}).
The codes are
inhabited for all the expressions corresponding to types in the
language. The meaning function (\Fun{ψ}) of the logical relation is
indexed by two expressions, where the first represents the type and
the second represents values of that type. The meaning function is
inhabited whenever the expression value is a valid member of the
expression type.

The meaning function is also indexed by the result
of applying the code type former to the expression index
representing type of the other expression index (representing the
value of said type). Hence,
the logical relation (or universe) is
an inductive-inductive type~\cite{indind},
in addition to being an inductive-recursive type.
One final difference between the logical relation and an ordinary
universe of types, is that the logical relation also contains termination
evidence, in the form of inhabitants of the
operational semantics judgement
(defined as a type that is indexed by expressions).

Once again, we emphasize that the logical relation for a dependent
type theory can be considered a \textit{universe},
albeit one with additional
indexing and containing additional data in the form of termination
witnesses. The fundamental theorem,
used to prove that the operational semantics terminates,
is defined over this universe (i.e. the logical relation is one of its
arguments). Hence, the fundamental theorem can be
seen as a \textit{fully generic} function. Many lemmas used in the
proof of termination can likewise be seen as fully generic
functions. Finally, we note that even though these functions are fully
generic, they operate over a fixed universe of natural numbers, closed
under dependent function formation.

\section{Extendable Open or Closed Well-Order Universes}

\paragraph{Open Universe}

Morris~\cite{morristhesis} demonstrates
generic programming over small \textit{indexed}
containers in an \textit{open} universe. Because indexed containers
can represent arbitrary user-declared datatypes, the universe is also
\textit{extendable}.

Morris writes generic functions, like \Fun{map},
over the open universe of indexed containers.
This corresponds to
writing generic functions over the open universe
of inductive-recursive types in \refsec{iralgmod},
because small induction-recursion and small indexing are
equivalent~\cite{smallir}. 

Recursive containers are represented using the
\Data{W} type of well-orderings,
which can be seen a the fixpoint of containers. Because 
As explained in \refsec{inad}, \Data{W} types inadequately encode
first-order types in intensional type theory, which is why we use the
more complicated (but adequate) algebraic semantics of
\refsec{iralgagda}, defined in terms of
\Data{Desc} and \Data{μ₁}.

\paragraph{Closed Universe}

We expect that it would be straightforward to extend the generic
functions that Morris wrote over an open universe of containers,
to operate over a closed universe of well-orderings
(like the universe in \refsec{wuni}).
Once again, we were not interested in this option for adequacy
reasons (\refsec{inad}).

\section{Extendable Open Algebraic Universes}

There is a lot of work on generic programming over an
\textit{open} algebraic universe, similar to the one in
\refsec{iralgmod}. It should be possible to extend any such generic
functions over an \textit{open} universe, to be fully generic over a
\textit{closed} universe (or hierarchy of universes),
using techniques from \refchap{fullyg}
(and \refsec{lgcount}).

\paragraph{Universal Algebra}

Benke et al.~\cite{benke:generic}
perform generic programming in the domain of universal
algebra. Various restrictions of the open inductive-recursive universe
of \refsec{iralgmod} are used
for each algebra (e.g. one-sorted term algebras, many-sorted
term algebras, parameterized term algebras, etc.). Some of these
algebras restrict the universe to be finitary, some remain infinitary,
but all of them restrict the use of induction-recursion. As they
state, their work could have been instead defined as restrictions over
a universe of indexed inductive types without induction-recursion.

\paragraph{Induction Principles}

Chapman et al.~\cite{Chapman:2010:GAL:1932681.1863547}
define \AgdaData{Desc}riptions for
indexed dependent types (without induction-recursion). Defining
generic \AgdaFun{ind}uction principles for types encoded by
\AgdaData{Desc}riptions requires a computational argument type for all
the inductive hypotheses (\AgdaData{All}, also called \AgdaData{Hyps}). 
Although \AgdaData{Desc} is not inductive-recursive, it is still
infinitary so generic functions over such types, like \AgdaFun{ind},
share many of the same properties as our generic functions.

Our previous work~\citep{diehl:gelim} expands upon the work of
Chapman et al.~\cite{Chapman:2010:GAL:1932681.1863547},
defining an alternative interface to
induction as generic type-theoretic
\AgdaFun{elim}inators for \AgdaData{Desc}riptions. Defining these
eliminators involves several nested constructions, where both
computational argument types (to collect inductive hypotheses) and return
types (to produce custom eliminator types for each description) are
used for information retrieval but not modification of infinitary
descriptions.

\paragraph{Ornaments}

McBride~\cite{mcbride2010ornamental} builds a theory
of \AgdaData{Orn}aments on top of \AgdaData{Desc}riptions for
indexed dependent types (without induction-recursion). Ornaments allow
a description of one type (such as a \AgdaData{Vec}tor) to be related
to another type (such as a \AgdaData{List}) such that a \AgdaFun{forget}ful map
from the more finely indexed type to the less finely indexed type can
be derived as a generic function.
Dagand and McBride~\cite{dagand2012transporting}
expand this
work to also derive a certain class of functions with less finely
indexed types from functions with more finely indexed types.

%% TODO \paragraph{disjointness and injectivity}
%% TODO \paragraph{Nearly Closed Universe of Morris
%% TODO ahmal
%% TODO sijling

%% TODO \section{Previous Work}


