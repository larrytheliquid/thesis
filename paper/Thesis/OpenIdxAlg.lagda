\AgdaHide{
\begin{code}
module _ where
open import Data.Bool
open import Data.Unit
open import Data.Sum
open import Data.Product
\end{code}}

\section{Indexed Types}\label{sec:idxalg}

In this section we cover the algebraic semantics of
\textit{indexed} and \textit{dependent} types. For pedagogical reasons,
we temporarily remove \textit{induction-recursion} (\refsec{iralg}), and
subsequently reintroduce it in \refsec{iiralg}.
An \textit{indexed} type (\refsec{indx}) is a collection of types
indexed by some type $I$.

\subsection{Algebraic Semantics}\label{sec:idxalgsem}

Previously (in \refsec{irlalgsem}) we gave the algebraic semantics of
inductive-recursive types in the category of \textit{slices}
(for some output set $O$),
where an object is a slice $\set/O$ consisting of a set and its
decoding function. Hence,
pattern functors ($F : \set/O \arr \set/O$)
and fixpoints ($\mu : (\set/O \arr \set/O) \arr \set/O$).

The algebraic semantics for indexed types is given in the category of
\textit{type families} (for some index set $I$),
where an object is a type family $\set^I$
(which is a function from elements of $I$ to sets).
$$
\set^I \triangleq I \arr \set
$$

Hence, the algebraic semantics for pattern functors and fixpoints of
indexed types is defined using $\set^I$ objects. Additionally, because
there is no decoding function, $F$ and $\mu$ can be defined without
breaking their definitions into 2 components.
$$
F : \set^I \arr \set^I
$$
$$
\mu : (\set^I \arr \set^I) \arr \set^I
$$

Throughout this section, it is important to remember that $\set^I$ is
notation for $I \arr \set$. An important consequence is that
$F$ and $\mu$ above actually have 2 arguments, where the second
argument is an $I$.
$$
F : \set^I \arr I \arr \set
$$
$$
\mu : (\set^I \arr \set^I) \arr I \arr \set
$$

Another consequence is that $\set^I$ arguments, like the first
argument of $F$, are actually
\textit{functions} (i.e. $I$-indexed families of sets, or
\textit{type families} for short)
from $I$ to $\set$
(rather than mere $\set$s).
$$
F : (I \arr \set) \arr \set^I
$$

So if we expand everything out, we get the type signatures
below. Notice in particular that the first argument of $\mu$ takes 2
arguments, an $I$-indexed family of sets and an $I$, and
returns a $\set$. Of course, the type of the first argument of $\mu$
is the same as the type of $F$, the functor whose least fixed point is
being calculated.
$$
F : (I \arr \set) \arr I \arr \set
$$
$$
\mu : ((I \arr \set) \arr I \arr \set) \arr I \arr \set
$$

It turns out~\cite{TODO} that the category of type families
$\set^I$ is \textit{equivalent} to the category of slices
$\set/O$ when the index set $I$ is equal to the output set
$O$.
\footnote{
  Additionally, the sets $I$ and $O$ must be \textit{small} for this
  equivalence to hold. That is, $I$ and $O$ must be sets rather than
  sets of sets. In type theroetic terms, \AgdaVar{I} and \AgdaVar{O}
  must have type \AgdaData{Set} (the \textit{small} type of types)
  rather than \AgdaData{Set₁} (the \textit{large} type of kinds).
}
$$
\set^I \Leftrightarrow \set/I
$$

The left direction of this equivalence is the \textit{inverse}
functor ($\inv : \set/I \arr \set^I$)
whose object component maps slices $\set/I$ to
families $\set^I$.
$$
\inv \triangleq
\lambda (X , d).~
\lambda i.~
(x : X) \cdot (d~x = i)
$$

As seen above, the inverse functor ($\inv$) is defined to be a dependent
product. The left component is the set ($X$) of the
slice ($\set/I$), whose elements ($x$) the right component can depend
on. The right component constrains the result of
applying the decoding function ($d$) to the element $x$ to be
\textit{equal} to the index
argument $i$ of the family ($\set^I$) being returned by the functor.
Therefore, instead of directly defining an $I$-indexed family of sets
as a $\set^I$, we can first define an appropriate
slice  $\set/I$. Then, we can get an actual $I$-indexed family of
sets by applying the inverse functor ($\inv$) to our slice.

In \refsec{idxalgmod} we take advantage of the equivalence between
family ($\set^I$) and slice ($\set/I$) categories, and reuse our type
theoretic semantic model of inductive-recursive types.
We \textit{derive} a
type theoretic model of indexed types by reifying (a more
intentionally precise
version of) the inverse functor
($\inv$) as a function translating descriptions of indexed types to descriptions
of inductive-recursive types, for which we have an existing algebraic
model in type theory (\refsec{iralgmod}). 

\subsection{Algebraic Model}\label{sec:idxalgmod}

\subsection{Type Model}\label{sec:idxalgtps}


