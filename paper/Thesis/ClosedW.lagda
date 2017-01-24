\AgdaHide{
\begin{code}
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Nat
open import Data.Fin hiding ( _+_ ) renaming ( zero to here ; suc to there )
open import Data.Vec hiding ( sum ) renaming ( [] to nil ; _∷_ to cons )
module _ where
postulate ??? : {A : Set} → A
\end{code}}

%% Extensional?

\section{Closed Vector Universe}\label{sec:closedu}

In this section we present one example of a closed type theory, which
we call the \textit{Closed Vector Universe}. This universe contains
some standard types along with some types specifically for writing
programs operating over vectors.
The \textit{Closed Vector Universe} is an example of a simple closed
type theory (or programming language)
with a fixed set of primitives that does \textit{not}
support custom user-defined types.

\AgdaHide{
\begin{code}
module ClosedVec where
  mutual
\end{code}}

\subsection{Universe Model}

Below is the model of the \textit{Closed Vector Universe}. 
It has standard types like the empty type (\AgdaData{⊥}),
the unit type (\AgdaData{⊤}), booleans (\AgdaData{Bool})
and is closed under
dependent pair formation (\AgdaData{Σ})
and dependent function (\AgdaData{Π}) formation.
However, we call it the \textit{Closed Vector Universe} because it
also includes types for writing vector-manipulating programs,
namely the natural numbers (\AgdaData{ℕ})
and finite sets (\AgdaData{Fin}), and is
closed under vector (\AgdaData{Vec}) formation.

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

Recall our convention of prefixing universe code constructors
(e.g. \AgdaCon{`Bool}) with a backtick to distinguish the code (the
``quoted'' version of the type) from the actual type it models
(in this case \AgdaData{Bool}, which is the result of applying the
meaning function to the code). For closed type theories we establish the
new convention of prefixing the type of codes (\AgdaData{`Set}) with a
backtick. Applying the meaning function to a \AgdaData{`Set}
(a ``quoted'' type of types) yields a
\AgdaData{Set} (the actual type of types).

Finally, notice that \AgdaData{`Set} is
inductive-recursive (\refsec{irtypes}), as its
\AgdaCon{`Σ} and \AgdaCon{`Π} constructors refer to the
meaning function in their codomain argument (\AgdaVar{B}). 
Any universe modeling a dependently typed language is
similarly inductive-recursive, as the universe must have
$\Pi$ types to qualify as a model for DTT.


\subsection{Generic Programming}

Just like the fully closed \AgdaData{BoolStar} universe of
\refsec{fullygeneric}, \AgdaData{`Set} also supports writing fully
generic functions. Fully generic functions, over a universe model of a
closed type theory, model pattern matching on types (\AgdaData{Set})
by pattern matching on codes (\AgdaData{`Set}) instead.
Therefore, a generic function over all values of all types is modeled
by matching on a code, then a value from the interpretation of that
code, followed by any additional arguments and the return type.
$$
(\AgdaVar{A} : \AgdaData{`Set}) → \AgdaFun{⟦}~\AgdaVar{A}~\AgdaFun{⟧} → ...
$$

Thus pattern matching on types is supported in a closed type
theory, because we know ahead of time that the collection of types
will never be extended (hence total functions over types never
become partial).

\subsubsection{Generic Sum without Function Body}

\AgdaHide{
\begin{code}
module _ where
 open ClosedVec
 private
\end{code}}

Our example fully generic function is \AgdaFun{sum}, summing up
all natural numbers (and values that can be coerced
into natural numbers) contained within a value of the
closed vector universe.


\begin{code}
  sum : (A : `Set) (a : ⟦ A ⟧) → ℕ
\end{code}

Let's begin with \AgdaFun{sum}ming values of base types
(non-function type formers, like \AgdaData{Bool}):
Summing a natural number just means returning it. We can never receive
a value of the empty type, so we need not define that
case. The sum of unit is 0. The sum of a boolean is 0 if it is
false, and 1 if it is true (\AgdaCon{true}
is the second constructor of \AgdaData{Bool}, just as
\AgdaCon{suc zero} is the second value in the ordered
natural numbers). The sum of a finite set
\AgdaData{Fin} value is 0 for the \AgdaCon{here} index, and the
\AgdaCon{suc}essor of the previous index for the \AgdaCon{there}
case. 

\begin{code}
  sum `ℕ n = n
  sum `⊥ ()
  sum `⊤ tt = 0
  sum `Bool true = 0
  sum `Bool false = 1
  sum (`Fin (suc n)) here = 0
  sum (`Fin (suc n)) (there p) = suc (sum (`Fin n) p)
\end{code}

We \AgdaFun{sum} a vector by adding together all of the values it
contains, where each value is interpreted as a natural number by
recursive application of \AgdaFun{sum}. The empty vector contains no
values, so its sum is 0.

\begin{code}
  sum (`Vec A zero) nil = 0
  sum (`Vec A (suc n)) (cons x xs) = sum A x + sum (`Vec A n) xs
\end{code}

A pair is like a two-element vector, so we \AgdaFun{sum} a pair by
adding its components.
Finally, the \AgdaFun{sum} of a function is 0.

\begin{code}
  sum (`Σ A B) (x , xs) = sum A x + sum (B x) xs
  sum (`Π A B) f = 0
\end{code}

Defining the \AgdaFun{sum} of a function to be 0 may seem
unsatisfying, as its body contains other values of our closed vector
universe. Consider the types of variables in context when defining the
function case of \AgdaFun{sum}:

\AgdaBind
\AgdaHide{
\begin{code}
module _ (A : ClosedVec.`Set) where
 open ClosedVec
 private
  postulate
\end{code}}

\begin{code}
   B : ⟦ A ⟧ → `Set
   f : (x : ⟦ A ⟧) → ⟦ B x ⟧
\end{code}
\AgdaUnbind

The \AgdaFun{sum} cases for pairs and functions are actually for
\textit{dependent} pairs (\AgdaCon{`Σ})
and functions (\AgdaCon{`Π}). Notice that in our definition of sum for
pairs the recursive call of \AgdaFun{sum} for the second
component applies the codomain \AgdaVar{B} to an
\AgdaFun{⟦}~\AgdaVar{A}~\AgdaFun{⟧} value. Luckily, the first
component of the pair (\AgdaVar{x}) is exactly the value we need.
If we wanted to provide an alternative definition of sum for
functions, we would have no such luck because the value we are summing
(\AgdaVar{f}) is itself a function (i.e. there is no \AgdaVar{x} in sight).
In the next section we 
change our definitions to end up with an \AgdaVar{x} in the function
case that we can pass to both \AgdaVar{B} and \AgdaVar{f}.

\subsubsection{Generic Sum with Function Body}

Step back for a moment and consider what the \AgdaFun{sum} of a function
should mean. One interpretation is to consider the \AgdaFun{sum} of a
function to be many possible sums, one for each argument in the domain
of the function. Under this interpretation our \AgdaFun{sum} is
missing an argument, one that provides a domain value for each
occurrence of a function in the closed vector universe value we wish
to sum.

In other words, we consider our previous definition of
\AgdaFun{sum} to be a partial function (we cannot appropriately define
the function case).
In \refsec{domsup} we
learned how to create a total function from a partial one by adding a
\textit{domain supplement}.
Below, we define the computational argument family \AgdaFun{Sum} to be
used as a domain supplement for \AgdaFun{sum}.

\AgdaHide{
\begin{code}
module _ where
 open ClosedVec
 private
\end{code}}

The most significant case is the supplement for functions, in
which we request the interpretation of \AgdaVar{A} as an additional
argument (let's call it \AgdaVar{x}).
When defining \AgdaFun{sum} we will want to use \AgdaVar{x}
to recursively sum the body of the function, so we also
recursively request a supplement for the codomain of our
function (\AgdaVar{B}) applied to \AgdaVar{x}.

\begin{code}
  Sum : (A : `Set) → ⟦ A ⟧ → Set
  Sum (`Π A B) f = Σ ⟦ A ⟧ (λ x → Sum (B x) (f x))
\end{code}

A pair may contain functions in either of its components, so we
recursively request supplements for its domain and codomain. An
empty vector requires no supplement, but a non-empty vector
requires one for each of its elements. Finally, the base types do not
need supplemental values to sum them, so their supplement is a trivial
unit value.

\begin{code}
  Sum (`Σ A B) (x , xs) = Sum A x × Sum (B x) xs
  Sum (`Vec A zero) nil = ⊤
  Sum (`Vec A (suc n)) (cons x xs) = Sum A x × Sum (`Vec A n) xs
  Sum A a = ⊤
\end{code}

Below the domain of \AgdaFun{sum}'s type is altered to take the
supplement \AgdaFun{Sum} as an additional argument.

\begin{code}
  sum : (A : `Set) (a : ⟦ A ⟧) → Sum A a → ℕ
\end{code}

The only change we make to defining \AgdaFun{sum} for
base types and \AgdaData{Fin} is to ignore the additional
trivial unit value (\AgdaCon{tt}), and to supply it as an argument in
the recursive case of \AgdaCon{`Fin}.

\begin{code}
  sum `⊥ () tt
  sum `⊤ tt tt = 0
  sum `Bool false tt = 0
  sum `Bool true tt = 1
  sum `ℕ n tt = n
  sum (`Fin (suc n)) here tt = 0
  sum (`Fin (suc n)) (there p) tt = suc (sum (`Fin n) p tt)
\end{code}

Summing pairs and vectors is also relatively unchanged. For pairs the
only difference is that we thread along the left component of the
supplement (\AgdaVar{y})
when summing the left component of the pair (\AgdaVar{x}), and
the right component of the supplement (\AgdaVar{ys}) when summing the
right component of the pair (\AgdaVar{xs}). Summing a non-empty vector
is similar to summing a pair, and summing an empty vector remains 0.

\begin{code}
  sum (`Σ A B) (x , xs) (y , ys) = sum A x y + sum (B x) xs ys
  sum (`Vec A zero) nil tt = 0
  sum (`Vec A (suc n)) (cons x xs) (y , ys) = sum A x y + sum (`Vec A n) xs ys
\end{code}

Finally, we can sum a function by summing its body. Its body is
obtained by applying the function \AgdaVar{f} to \AgdaVar{x}
(whose type is the interpretation of \AgdaVar{A}), readily available
in the domain supplement. Of course, the body may have additional
functions to sum, so we thread along the domain supplement \AgdaVar{y} for
any of those.

\begin{code}
  sum (`Π A B) f (x , y) = sum (B x) (f x) y
\end{code}



\subsection{Conclusion}

The \textit{Closed Vector Universe} has enough types to write a lot of interesting
functions, but the specific collection of types that our closed
type theory contains is arbitrarily chosen. What if we later decide we also want
binary trees? By definition we cannot add custom types to a closed type
theory (and if we did it would violate the totality of generic
functions over the original universe).
Next (in \refsec{closedw}) we see how to model a closed type theory that
\textit{does} support custom user-defined types.

\section{Closed Well-Order Universe}\label{sec:closedw}

\AgdaHide{
\begin{code}
module SetW where
  data W (A : Set) (B : A → Set) : Set where
  mutual
\end{code}}

On one hand, we would like a closed type theory because it supports
fully generic programming (\refsec{fullygeneric})
via pattern matching on types. On the other hand,
we want to support custom user-defined types (like an open type theory)
that may not be present in the closed collection of types we fixed
ahead of time.

What if our closed theory had enough primitive base types and type
families to simulate adding new datatypes to the language?
That is, we want to support translating any ``new'' type
declaration into an isomorphic type defined in terms of our
closed collection of primitive types.

\subsection{Universe Model}

The type of \textit{well-orderings} (\AgdaData{W}) is used to define
the semantics of inductive datatypes in type theory, and is the key to
solving our problem. After pruning some derivable types from the previous
universe and adding \AgdaData{W} types, we get a closed type theory that can
internally represent any type that would normally extend the language
in an open type theory. Before explaining what \AgdaData{W} types are
and how they can be used to derive inductive types (\refsec{wtypes}),
we use them below to define a closed type theory universe supporting
custom user-defined types.

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

The closed type theory above consisting of the
empty type (\AgdaData{⊥}),
the unit type (\AgdaData{⊤}),
and booleans (\AgdaData{Bool})
closed under
dependent pair (\AgdaData{Σ}) formation,
dependent function (\AgdaData{Π}) formation,
and well-order (\AgdaData{W})
formation allows us to
model datatype declarations. We show how to model datatype
declarations by translating them into \AgdaData{W} types and other
primitive types in \refsec{wtypes}. In \refsec{inad} we show that the
universe of this section is sufficient for all such translations. 

\subsection{Types as Well-Orders}\label{sec:wtypes}

The type of well-orderings~\cite{TODO} (\AgdaData{W}) can be used to model
inductive datatype declarations as well-founded trees.
\footnote{The etymology of
``well-orderings'' comes from \AgdaData{W} being the constructive
version of the classical notion of a well-order. A well-order
interprets a set as an ordinal $\alpha$ and a relation specifying
which ordinals are less than $\alpha$. However, in this thesis we
focus on the more practical interpretation of \AgdaData{W} types as a
means to define inductive datatypes.}
It is defined below, where the \AgdaVar{A} parameter
encodes non-recursive arguments for each constructor of an
inductive datatype, and the cardinality of \AgdaVar{B}~\AgdaVar{a}
encodes the number of recursive arguments for each constructor.
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
type, we begin with the \AgdaData{Tree} type below. In the series of paragraphs
that follow, we change the definition of \AgdaData{Tree} by applying
isomorphisms.
Our binary \AgdaData{Tree} type begins with leaves containing
\AgdaVar{A} values and binary
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
Replace the collection of constructors with a single constructor.
The new constructor's argument type is the tuple of right-nested disjoint
unions formed from the argument types of each old constructor.

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

\subsection{Inadequacy of Well-Orders}\label{sec:inad}

It would seem like \AgdaData{W} is a sufficient datatype to represent
any inductive datatype a user would define. Our
fully closed universe from \refsec{closedw} has enough
primitives to represent types in terms of \AgdaData{W} as values of
type \AgdaData{`Set}. For example, below we internalize (i.e. as universe
codes) disjoint unions in terms of primitive
dependent pairs (\AgdaCon{`Σ}) and
booleans (\AgdaCon{`Bool}),
and then internalize the \AgdaData{Tree} type in terms of
primitive well-orderings (\AgdaCon{`W}).

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

%% TODO subo or auto for model in metalang
%%  only auto for object lang

%% TODO only dealing with first universe
%%   see Section Hier for hierarchy

%% TODO W types as denotational semantics of syntactic
%%   inductively declared datatypes

If \AgdaData{W} were adequate for our purposes, then this
thesis could focus on writing fully generic functions over the
\AgdaData{`Set} universe of \refsec{closedw}.
We could write functions similar to
\AgdaFun{sum} from \refsec{closedu}, except they would work for
any custom user-defined type!
However, there are two issues:

\begin{enumerate}
\item Although \AgdaData{W} types can be extended to support
  definitions of indexed types (\refsec{indx}),
  they cannot be extended to support
  definitions of inductive-recursive types
  (\refsec{irtypes}).

\item The base cases of inductively defined datatypes using
  \AgdaData{W} have an infinite number of intentionally distinct
  values. Recall that the base case \AgdaCon{leaf} had
   \texttt{⊥ → Tree A B} as its inductive argument. Because the
   domain of the function is bottom, we can write it many different
   ways (i.e. \AgdaFun{elim⊥}, \AgdaFun{elim⊥ ∘ elim⊥}, etc). Even
   though all leaves containing such functions are extensionally
   equivalent, it is inadequate~\cite{TODO} to have an infinite number of
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
