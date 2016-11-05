\AgdaHide{
\begin{code}
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product
module _ where
\end{code}}

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
built in collection of types that will not be extended. Such a type
theory can be modeled as a \textit{fully closed universe}. Modeling a
closed type theory as a fully closed universe allows you to write
generic functions that work over any type
(and can make decisions about any value) in the language,
which is a powerful feature that this thesis focuses upon.
Writing generic functions over a fully closed universe models a closed
type theory that supports pattern matching on its types.

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

The universe above has enough types to write a lot of interesting
functions, but the specific collection of types that our closed
language contains is arbitrarily chosen. What if we later decide we also want
binary trees? By definition we cannot add datatypes to a closed type
theory (and if we did it would break generic generic functions over
the original universe).

\subsection{Universe Closed Under W}

\AgdaHide{
\begin{code}
module _ where
 data W (A : Set) (B : A → Set) : Set where
 private
  mutual
\end{code}}

Ideally we want a closed type theory with the minimum
number of type primitives necessary to simulate adding new datatypes
to the language, but only actually using the closed collection of
primitive types.

The type of \textit{well orderings} (\AgdaData{W}) is used to define
the semantics of inductive datatypes in type theory. After pruning
some derivable types from the previous universe and adding
W types, we get a closed type theory that can internally represent any
type that would normally extend the language in an open type theory.

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
model datatype declarations of an open type theory, but without
needing to actually extend the theory. We show how to model datatype
declarations by translating them into types from our closed universe
in the next section.

\subsection{W Types}

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
