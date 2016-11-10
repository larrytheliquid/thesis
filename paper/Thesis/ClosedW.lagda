\AgdaHide{
\begin{code}
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product
module _ where
\end{code}}

%% Extensional?
\section{Closed Inductive Universe}

\subsection{Closed Type Theory}

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open import Data.Fin
 open import Data.Vec
 private
  mutual
\end{code}}

A \textit{closed type theory} is a dependently typed language with a
built in collection of types that will never be extended. Such a type
theory can be modeled as a \textit{fully closed universe}. To qualify
as a closed type theory, we require that its collection of types is at
least closed under dependent function formation.
Consider the closed type theory below of the empty type, the unit
type, booleans, natural numbers, and finite sets closed under
vector formation, dependent pair formation, and dependent function
formation.

\begin{code}
   data `Set : Set where
     `⊥ `⊤ `Bool `ℕ : `Set
     `Fin : ℕ → `Set
     `Vec : `Set → ℕ → `Set
     `Σ `Π : (A : `Set) (B : ⟦ A ⟧ → `Set) → `Set
  
   ⟦_⟧ : `Set → Set
   ⟦ `⊥ ⟧ = ⊥
   ⟦ `⊤ ⟧ = ⊤
   ⟦ `Bool ⟧ = Bool
   ⟦ `ℕ ⟧ = ℕ
   ⟦ `Fin n ⟧ = Fin n
   ⟦ `Vec A n ⟧ = Vec ⟦ A ⟧ n
   ⟦ `Σ A B ⟧ = Σ ⟦ A ⟧ (λ a → ⟦ B a ⟧)
   ⟦ `Π A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
\end{code}

Just like the fully closed \AgdaData{ListStar} universe of
\ref{section-ListStar}, \AgdaData{`Set} also supports writing fully
generic functions. Fully generic functions take advantage of the
ability to pattern match on codes, which models pattern matching on
types. Thus pattern matching on types is supported in a closed type
theory, because we know ahead of time that the collection of types
will never be extended (hence total functions over types never
become partial).

The \AgdaData{`Set} universe above has enough types to write a lot of interesting
functions, but the specific collection of types that our closed
type theory contains is arbitrarily chosen. What if we later decide we also want
binary trees? By definition we cannot add datatypes to a closed type
theory (and if we did it would break generic generic functions over
the original universe).

\subsection{Universe Closed Under W}

\AgdaHide{
\begin{code}
module SetW where
  data W (A : Set) (B : A → Set) : Set where
  mutual
\end{code}}

On one hand, we would like a closed type theory because it supports
generic programing via pattern matching on types. On the other hand,
we want to support user defined datatypes (like an open type theory)
that may not be accounted for in our closed collection of types.

What if our closed theory had enough primitive types and type
formers to simulate adding new datatypes to the language?
That is, we want to support translating any ``new'' type
declaration into a definition in terms of an existing closed
collection of primitive types and type formers.

The type of \textit{well-orderings} (\AgdaData{W}) is used to define
the semantics of inductive datatypes in type theory, and is the key to
our debacle. After pruning some derivable types from the previous
universe and adding W types, we get a closed type theory that can
internally represent any type that would normally extend the language
in an open type theory.

\begin{code}
   data `Set : Set where
     `⊥ `⊤ `Bool : `Set
     `Σ `Π `W : (A : `Set) (B : ⟦ A ⟧ → `Set) → `Set
  
   ⟦_⟧ : `Set → Set
   ⟦ `⊥ ⟧ = ⊥
   ⟦ `⊤ ⟧ = ⊤
   ⟦ `Bool ⟧ = Bool
   ⟦ `Σ A B ⟧ = Σ ⟦ A ⟧ (λ a → ⟦ B a ⟧)
   ⟦ `Π A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
   ⟦ `W A B ⟧ = W ⟦ A ⟧ (λ a → ⟦ B a ⟧)
\end{code}

The closed type theory above consisting of the empty type, the unit
type, and booleans closed under
dependent pair formation,
dependent function formation, and well-order formation allows us to
model datatype declarations. We show how to model datatype
declarations by translating them into types from our closed universe
in the next section.

\subsection{W Types}

The type of well-orderings (\AgdaData{W}) can be used to model definitions of
inductively defined well-founded trees.
\footnote{The etymology of
``well-orderings'' comes from \AgdaData{W} being the constructive
version of the classical notion of a well-order. A well-order
interprets a set as an ordinal $\alpha$ and a relation specifying
which ordinals are less than $\alpha$. However, in this thesis we
focus on the more practical interpretation of \AgdaData{W} types as a
means to define inductive datatypes.}
It is defined as followed, where the \AgdaVar{A} parameter
is used for non-recursive arguments for each constructor of an
inductive datatype, and the cardinality of the \AgdaVar{B} parameter
(for each constructor) determines the number of recursive arguments.
\footnote{Besides cardinailty, the content of the \AgdaVar{B} parameter
also determines the domain of infinitary arguments, discussed in
\ref{section-inf}.
}

\begin{code}
data W (A : Set) (B : A → Set) : Set where
  sup : (a : A) (f : B a → W A B) → W A B
\end{code}

\noindent
We show how to model the semantics of inductive datatypes using
\AgdaData{W} by:

\begin{enumerate}
\item Starting with a high-level inductive datatype declaration.
\item Translating between a series of isomorphic datatype
  declarations.
\item Finally reaching a datatype declaration that can be encoded
  using a \AgdaData{W} type.
\end{enumerate}

As an example of elaborating a datatype declaration to a \AgdaData{W}
type, we begin with the tree type below. We define
binary \AgdaData{Tree}s with leaves containing \AgdaVar{A} values and binary
branches containing \AgdaVar{B} values in the middle of each branch.

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}
\begin{code}
  data Tree (A B : Set) : Set where
    leaf : A → Tree A B
    branch : Tree A B → B → Tree A B → Tree A B
\end{code}

\paragraph{\texttt{A × B → C ≅ A → B → C}}
Replace multiple arguments of constructors by
a single \textit{uncurried} argument.
Single argument constructors remain unchanged.

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}
\begin{code}
  data Tree (A B : Set) : Set where
    leaf : A → Tree A B
    branch : Tree A B × B × Tree A B → Tree A B
\end{code}

\paragraph{\texttt{A × B ≅ B × A}}
By commutativity of pairs, rearrange recursive constructor arguments
to all appear at the end.

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}
\begin{code}
  data Tree (A B : Set) : Set where
    leaf : A → Tree A B
    branch : B × Tree A B × Tree A B → Tree A B
\end{code}

\paragraph{\texttt{A × B ≅ Π Bool (λ b → if b then A else B)}}
A non-dependent pair can be defined as a dependent function from a
boolean to each component of the pair. Replace all pairs of recursive
constructor arguments with such a dependent function whose domain
cardinality is equal to the number of recursive arguments for that
constructor (i.e. \AgdaData{Bool} for 2 recursive arguments and
\AgdaData{⊥} for 0 recursive arguments).

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}
\begin{code}
  data Tree (A B : Set) : Set where
    leaf : A × (⊥ → Tree A B) → Tree A B
    branch : B × (Bool → Tree A B) → Tree A B
\end{code}

\paragraph{\texttt{(A → C) ⊎ (B → C) ≅ A ⊎ B → C}}
Replace the collection of constructors with a single constructor whose
argument type is the disjoint union of the argument types of each constructor.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Sum
 private
\end{code}}
\begin{code}
  data Tree (A B : Set) : Set where
    list : (A × (⊥ → Tree A B))
      ⊎ (B × (Bool → Tree A B))
      → Tree A B
\end{code}

\paragraph{\texttt{(A × B) ⊎ (A' × B') ≅ Σ (A ⊎ A') (λ x → if isLeft x then B else B')}}
Replace the disjoint union of pairs whose domain is non-recursive
arguments and codomain is recursive arguments, with a single pair
whose domain is the disjoint union of non-recursive arguments and
codomain is the disjoint union of recursive arguments.
\footnote{For datatypes with infinitary arguments,
\AgdaVar{B} and \AgdaVar{B'} may depend on \AgdaVar{A} and
\AgdaVar{A'} respectively, so the \texttt{if} conditional is replaced by
\texttt{case} analysis.}

\AgdaHide{
\begin{code}
module _ where
 open import Data.Sum
 private
  postulate isLeft : {A B : Set} → A ⊎ B → Bool
\end{code}}
\begin{code}
  data Tree (A B : Set) : Set where
    list : Σ (A ⊎ B) (λ x → if isLeft x
      then (⊥ → Tree A B)
      else (Bool → Tree A B))
      → Tree A B
\end{code}

\paragraph{\texttt{data ≅ W}} Encode the final datatype declaration as a \AgdaData{W}
type by using the first component of the pair for the \AgdaVar{A}
parameter, and the domains of each function in the second component of the
pair for the \AgdaVar{B} parameter.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Sum
 private
  postulate isLeft : {A B : Set} → A ⊎ B → Bool
\end{code}}
\begin{code}
  Tree : Set → Set → Set
  Tree A B = W (A ⊎ B) λ x → if isLeft x
    then ⊥
    else Bool
\end{code}

\subsection{Inadequacy of W}

It would seem like \AgdaData{W} is a sufficient datatype to represent
any inductive datatype a user would define. Our
fully closed universe from \ref{subsection-closedw} has enough
primitives to represent types in terms of \AgdaData{W} as values of
type \AgdaData{`Set}. For example, below we internalize (i.e. as universe
codes) disjoint unions in terms of internal dependent pairs and
booleans, and then internalize the \AgdaData{Tree} type in terms of
internal well-orderings.

\AgdaHide{
\begin{code}
module _ where
 open SetW
 private
\end{code}}
\begin{code}
  _`⊎_ : `Set → `Set → `Set
  A `⊎ B = `Σ `Bool (λ b → if b then A else B)

  `Tree : `Set → `Set → `Set
  `Tree A B = `W (A `⊎ B) λ x → if (not (proj₁ x))
    then `⊥
    else `Bool
\end{code}

If \AgdaData{W} were adequate for our purposes, then this
thesis could focus on writing fully generic functions over the
\AgdaData{`Set} universe. However, there are two issues:

\begin{enumerate}
\item Although \AgdaData{W} types can be extended to support
  definitions of inductively defined type families
  (described in \ref{section-indexed-desc}), they cannot be extended to support
  definitions of inductive-recursive datatypes
  (described in \ref{section-ir-desc}).

\item The base cases of inductively defined datatypes using
  \AgdaData{W} have an infinite number of intentionally distinct
  values. Recall that the base case \AgdaCon{leaf} had
   \texttt{⊥ → Tree A B} as its inductive argument. Because the
   codomain of the function is bottom, we can write it many different
   ways (i.e. \AgdaFun{elim⊥}, \AgdaFun{elim⊥ ∘ elim⊥}, etc). Even
   though all leaves containing such functions are extentionally
   equivalent, it is inadequate to have an infinite number of
   intentionally distinct canonical forms for the model of
   \AgdaData{Tree} (whose initial declaration was first-order).
\end{enumerate}

These two issues lead us to an alernative representation of inductive
datatypes, from the induction-recursion literature.


%% \paragraph{\texttt{A ⊎ B ≅ Σ Bool (λ b → if b then A else B)}}
%% The disjoint union of two types can be defined as a dependent pair whose
%% domain is a boolean and codomain is a function selecting the component
%% of the disjoint union.

%% \AgdaHide{
%% \begin{code}
%% module _ where
%%  private
%% \end{code}}
%% \begin{code}
%%   data Tree (A B : Set) : Set where
%%     list : Σ Bool (λ b → if b
%%       then A × (⊥ → Tree A B)
%%       else B × (Bool → Tree A B)
%%       ) → Tree A B
%% \end{code}


%% \section{Closed Universe of Inductive Types}

%% para poly concat generic despite not being able to make decisions
%% about values of open types

%% Para poly concat, hlist append, universe poly concat
%% ... finally fully-generic all

%% \section{Generic Programming with (Co)Domain Supplements}

%% inductive vs recursive type families (Vec)

%% head, append for unis, and quicksort


%% \subsection{Generic Functions}

%% In a sense, functions over open types are \textit{generic} with
%% respect to all concrete \AgdaData{Set}s that the open type may be
%% instantiated with. In fact, the functions must work the
%% \textit{same way} for all concrete \AgdaData{Set}s.
%% \footnote{In open type theories, there is no way to case-analyze
%%   values of \AgdaData{Set}, so functions cannot make decisions based
%%   on which concrete \AgdaData{Set} appears.}

%% Recall that functions defined over open types can be considered
%% \textit{generic} in the sense they are defined once and for all
%% \AgdaData{Set}s (those defined now or in the future). 
%% Similarly, \textit{generic} functions defined over a universe can be
%% defined once and for all types in the universe.

%% The difference is that a generic functions over an open type (such as
%% a parametrically polymorphic functions) must act the \textit{same} for
%% all possible \AgdaData{Set}s. In contrast, a generic
%% function over a universe can behave \textit{differently} for each type
%% in the universe, because there are a finite number of type
%% \textit{codes} to consider.
%% This is similar to the way a function over a closed type can behave
%% \textit{differently} for all values contained within it.





%% When we create a type, we
%% usually have particular properties in mind that values in the
%% collection adhere to.

%% idea of an open or closed type / collection of values
%% closed is all values defined by the type
%% closed List specialized to Nat


%% A function can be given a type to restrict 
%% The motivation behind types is the ability to write functions

%% that can
%% assume certain properties about its inputs to consume and output to
%% produce. 

%% to constrain functions to only operate on values

%% In a programming languages, a type captures the notion of a particular
%% collection of values.

%% The idea behind universes is to capture the notion of a collection of
%% datatypes as a first class entity in our programming language.
