\AgdaHide{
\begin{code}
module _ where
open import Data.Bool
open import Data.Unit
open import Data.Sum
open import Data.Product
\end{code}}

\section{Inductive-Recursive Types}\label{sec:iralg}

In this section we extend the algebraic semantics of
\textit{infinitary} and \textit{dependent} types
(\refsec{depalg})
to \textit{inductive-recursive} types
(\refsec{irtypes}). An inductive-recursive type is mutually defined
with a \textit{decoding} function that may be used in the inductive
definition of the type.

\subsection{Algebraic Semantics}\label{sec:iralgsem}

In all of the previous algebraic semantics we have worked with,
the pattern functors were \textit{endofunctors}
of the category of sets. That is, each functor
($F : \set \arr \set$)
mapped each set to another set.
Consequently, the fixpoint
($\mu : (\set \arr \set) \arr \set$)
of such a functor gave us back a set ($\mu F : \set$).
Hence, previously each type could be semantically modeled as
a set ($\set$).

In order to model \textit{inductive-recursive} types, we need to model
a type ($X : \set$) along with its mutually defined
\textit{decoding} function ($d : X \arr O$), mapping values of the
type to values of some output type ($O : \set$). For example,
\refsec{irtypes} presents the type of arithmetic expressions
($X \triangleq~$\AgdaData{Arith}) mutually defined with a decoding function
($d \triangleq~$\AgdaFun{eval} : \AgdaData{Arith} \arr~ \AgdaData{ℕ})
that evaluates an
expression to its natural number ($O \triangleq~$\AgdaData{ℕ}) result.
Thus, algebraic semantics models inductive-recursive types
as the dependent product of a set and its decoding function. Such a
dependent product is called a \textit{slice}, notated as
$\set/O$ (where $O$ is the output set).
$$
\set/O \triangleq (X : \set) \cdot (X \arr O)
$$

Pattern functors for inductive-recursive types are endofunctors
($F : \set/O \arr \set/O$)
of the slice category $\set/O$
\footnote{
  Objects of the slice category $\set/O$ are functions
  $f : X \arr O$ (where $X$ is some set). Its morphisms are
  functions $h : X \arr Y$ between objects
  $f : X \arr O$ and $g : Y \arr O$ such that
  $f = g \circ h$.
  
},
and the fixpoint
($\mu : (\set/O \arr \set/O) \arr \set/O$)
of such a pattern functor returns a slice
($\mu F : \set/O$).

%% Compared to the semantics of dependent types
