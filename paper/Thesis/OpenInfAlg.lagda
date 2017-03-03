\AgdaHide{
\begin{code}
module _ where
open import Data.Bool
open import Data.Unit
open import Data.Sum
open import Data.Product
\end{code}}

\section{Open Infinitary Types}\label{sec:infalg}

In this section we review the initial algebra semantics for
\textit{infinitary} (\refsec{inft}) non-dependent types.
We extend our previous categorical model, formal model,
and examples to support \textit{infinitary}
constructor arguments.

\subsection{Categorical Model}\label{sec:infalgsem}

The categorical model of \textit{infinitary} inductive datatypes
reuses the 1, (+) and ($\cdot$) polynomial set constructions. However,
the inductive occurrences construction $X$ is subsumed by the
\textit{infinitary} occurrences construction $X^A$. Functions are the
type theoretic equivalent of exponential terms, where $X$ raised to
the power of $A$ is equivalent to a function with domain $A$ and
codomain $X$.
\footnote{
  If $A$ and $X$ are finite sets, then the cardinality of $X^A$ is
  equal to the cardinality of the graph of the function $A \arr X$.
  }
$$
X^A \triangleq (A \arr X)
$$

Therefore, $X^A$ is notation for an infinitary polynomial set
construction whose domain is $A$ and whose codomain is an inductive
occurrence.
Any non-infinitary inductive argument $X$ can be isomorphically expressed
as an infinitary argument by raising $X$ to the power of 1 (or equivalently,
a function whose domain is 1 and whose codomain is $X$).

$$
X \cong (X^1 \triangleq 1 \arr X)
$$

\paragraph{Natural Numbers}

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

For example, consider the infinitary (but isomorphic) declaration of
the natural numbers below. The inductive argument to the
\AgdaCon{suc} constructor has been replaced with
the infinitary argument \AgdaVar{f}, using the unit type as its
domain.

\begin{code}
  data ℕ : Set where
    zero : ℕ
    suc : (f : ⊤ → ℕ) → ℕ
\end{code}

The categorical model of the infinitary \AgdaData{ℕ} type
is the fixpoint equation below.
$$
\nat \triangleq \mu X.~1 + X^1
$$

The only difference between the non-infinitary and infinitary
\AgdaData{ℕ} is that constructing it with \AgdaCon{suc} must supply a
function ignoring a \AgdaData{⊤} argument, and destructing
\AgdaCon{suc} requires applying \AgdaVar{f} to the trivial value
\AgdaCon{tt} to access the inductive value in the body of
\AgdaVar{f}.

\paragraph{Binary Trees}

Below is a straightforward infinitary encoding of binary trees,
replacing both inductive arguments of \AgdaCon{branch} with infinitary
ones by using the unit type as the domain.

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\begin{code}
  data Tree (A B : Set) : Set where
    leaf : A → Tree A B
    branch : (f : ⊤ → Tree A B) (b : B) (g : ⊤ → Tree A B) → Tree A B
\end{code}

This translates to the the categorical model of infinitary binary
trees below, without any surprises.
$$
\dfn{Tree} \lambda A.~ \lambda B.~ \mu X.~ A + X^1 \cdot B \cdot X^1
$$

However, recall our series of isomorphic translations of the binary
tree declaration used to model \AgdaData{Tree} via \AgdaData{W}
types (\refsec{wtypes}). We can borrow two of those isomorphisms
to transform \AgdaData{Tree} into a less trivial instance of an
infinitary type (i.e. one whose infinitary domains are types
other than unit).

First, we reorder the \AgdaVar{b} argument (of type \AgdaVar{B}) to the front via symmetry
(\texttt{A × B ≅ B × A}), swapping \AgdaVar{b} and the inductive
argument \AgdaVar{t₁} so that both inductive arguments
(\AgdaVar{t₁} and \AgdaVar{t₂})
to appear
at the end of \AgdaCon{branch}.

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\begin{code}
  data Tree (A B : Set) : Set where
    leaf : A → Tree A B
    branch : (b : B) (t₁ : Tree A B) (t₂ : Tree A B) → Tree A B
\end{code}

Second, we appeal to the isomorphism that defines a non-dependent
pair (the two arguments \AgdaVar{t₁} and \AgdaVar{t₂} above)
as a dependent function (\AgdaVar{f} below) from \AgdaData{Bool} to each component of
the pair (\texttt{A × B ≅ Π Bool (λ b → if b then A else B)}).

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\begin{code}
  data Tree (A B : Set) : Set where
    leaf : A → Tree A B
    branch : (b : B) (f : Bool → Tree A B) → Tree A B
\end{code}

This translates both inductive arguments into a \textit{single}
infinitary argument, where the domain is now \AgdaData{Bool} instead
of \AgdaData{⊤}. It makes sense for the domain (i.e. branching factor)
to be \AgdaData{Bool}, as we are defining \textit{binary} trees.
Given that the cardinality of \AgdaData{Bool} is 2, we use
initial algebra semantics to define a categorical model of
infinitary binary
trees by raising $X$ to the power of 2 in the encoding of the
\AgdaCon{branch} constructor.
$$
\dfn{Tree} \lambda A.~ \lambda B.~ \mu X.~ A + B \cdot X^2
$$

\subsection{Formal Model}\label{sec:infalgmod}

To formally model \textit{infinitary} types,
we make minor changes to our previous non-infinitary formal model
(\refsec{nondepalgmod}). In all aspects of our formal model,
we change from modeling merely inductive occurrences of types ($X$) to
infinitary occurrences ($X^A$).

\paragraph{Descriptions}

Our formal model of descriptions stays the same, except that we replace the
syntax for inductive occurrences (\AgdaCon{`X}) with a syntax for
infinitary occurrences (\AgdaCon{`X\carot}).
While inductive occurrences (\AgdaCon{`X}) have no arguments,
infinitary occurrences (\AgdaCon{`X\carot}) have a
\AgdaData{Set} argument
representing the domain of the infinitary function type.

\AgdaHide{
\begin{code}
module Desc where
\end{code}}

\begin{code}
  data Desc : Set₁ where
    `1 : Desc
    _`+_  _`∙_ : Desc → Desc → Desc
    `κ `X^ : Set → Desc
\end{code}

For example, below we convert the \AgdaCon{suc} constructor
in the description of natural numbers to take
an infinitary argument with a trivial domain.

\AgdaHide{
\begin{code}
module _ where
 open Desc
 private
\end{code}}

\begin{code}
  NatD : Desc
  NatD = `1 `+ `X^ ⊤
\end{code}

Finally, note that the ``carot'' in the syntax of
infinitary occurrences (\AgdaCon{`X\carot}) connotes raising an
inductive occurrence to some power (the power being
the cardinality of the domain argument of type \AgdaData{Set}).


\paragraph{Pattern Functors}

Again, pattern functors ($F : \set \arr \set$)
are not formally modeled
directly. Instead, the formal model
of a pattern functor (\AgdaFun{F} : \AgdaData{Set}
\arr~\AgdaData{Set})
is the result of partially applying a
description to the interpretation function
(\AgdaFun{⟦}\_\AgdaFun{⟧} : \AgdaData{Desc} \arr~\AgdaData{Set}
\arr~\AgdaData{Set}).

The interpretation of all patterns besides the infinitary pattern
\AgdaCon{`X\carot} remains the same.
The infinitary pattern \AgdaCon{`X\carot} \AgdaVar{A} is interpreted
as a function with domain \AgdaVar{A} and codomain \AgdaVar{X}. It is
crucial that \AgdaVar{X} (representing an inductive occurrence)
appears in the codomain (rather than domain)
of the function. Otherwise, our subsequent fixpoint construction
(\AgdaData{μ}) would support negative datatypes (the
Agda positivity checker prevents us from defining \AgdaData{μ}
with \AgdaVar{X} in the interpreted function domain even if we tried).

\AgdaHide{
\begin{code}
module El where
  open Desc
\end{code}}

\begin{code}
  ⟦_⟧ : Desc → Set → Set
  ⟦ `1 ⟧ X = ⊤
  ⟦ A `+ B ⟧ X = ⟦ A ⟧ X ⊎ ⟦ B ⟧ X
  ⟦ A `∙ B ⟧ X = ⟦ A ⟧ X × ⟦ B ⟧ X
  ⟦ `κ A ⟧ X = A
  ⟦ `X^ A ⟧ X = A → X
\end{code}

Partially applying \AgdaFun{NatD} to the interpretation function
results in the following pattern functor for an infinitary encoding of
natural numbers.

\AgdaHide{
\begin{code}
module _ where
 open Desc
 open El
 open import Relation.Binary.PropositionalEquality
 private
  NatD : Desc
  NatD = `1 `+ `X^ ⊤
  _ :
\end{code}}

\begin{code}
   ⟦ NatD ⟧ ≡ (λ X → ⊤ ⊎ (⊤ → X))
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}

Notice how the argument of the \AgdaCon{suc} constructor, which is the
type to the right of the disjoint union, is an function
from the unit type to the inductive \AgdaVar{X} occurrence.

\paragraph{Fixpoints}

The initial algebra semantics for least fixed points
($\mu : (\set \arr \set) \arr \set$) of \textit{infinitary} types
is formally modeled (\AgdaData{μ} : \AgdaData{Desc} \arr~\AgdaData{Set})
the same way as the non-infinitary version. The
\AgdaCon{init} constructor of \AgdaData{μ},
modeling the initial algebra ($\anit$), is also
unchanged.

\AgdaHide{
\begin{code}
module Fix where
  open Desc
  open El
\end{code}}

\begin{code}
  data μ (D : Desc) : Set where
    init : ⟦ D ⟧ (μ D) → μ D
\end{code}


The natural numbers can be defined as a fixpoint of their description,
as before. 

\AgdaHide{
\begin{code}
module _ where
 open Desc
 open El
 open Fix
 open import Relation.Binary.PropositionalEquality
 private
  NatD : Desc
  NatD = `1 `+ `X^ ⊤
\end{code}}

\begin{code}
  ℕ : Set
  ℕ = μ NatD
\end{code}

The type of the argument to the \AgdaCon{init}ial algebra
of natural numbers is like the type of the natural number pattern
functor, except with \AgdaVar{X} replaced by the type of natural
numbers. This makes the argument to the \AgdaCon{suc} constructor an
infinitary type, as the codomain ends with an inductive occurrence
(the \AgdaData{ℕ}) type.

\AgdaHide{
\begin{code}
  _ :
\end{code}}

\begin{code}
   ⟦ NatD ⟧ ℕ ≡ (⊤ ⊎ (⊤ → ℕ))
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}

\subsection{Examples}\label{sec:infalgtps}

Now we repeat the examples of formal models of non-infinitary types
(\refsec{nondepalgmod}), converting models to their infinitary
counterparts.
A straightforward translation from the non-infinitary to the
infinitary translates both the models for pattern functors and
datatypes to infinitary versions.

Alternatively, we can model non-infinitary datatypes that are defined
in terms of infinitary pattern functors. In this scenario type formers
do not require special treatment (i.e. their definitions can be
equivalent to their non-infinitary counterparts).
However, we must
take special care when modeling constructors by exposing a
non-infinitary type signature (i.e. interface) that is defined in
terms of an infinitary (hidden) implementation.

\paragraph{Natural Numbers}

Let's begin with the straightforward model of infinitary natural
numbers, defined with a model of an infinitary pattern functor. The infinitary
(due to the \AgdaVar{f} argument)
definition of natural numbers is below.

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\begin{code}
  data ℕ : Set where
    zero : ℕ
    suc : (f : ⊤ → ℕ) → ℕ
\end{code}

The infinitary pattern functor for this type is described by
\AgdaFun{NatD}. Its type former \AgdaData{ℕ}
appears below, and is modeled the same way
as its non-infinitary coutnerpart in \refsec{nondepalgmod}.

\AgdaHide{
\begin{code}
module _ where
 open Desc
 open El
 open Fix
 open import Relation.Binary.PropositionalEquality
 private
\end{code}}

\begin{code}
  NatD : Desc
  NatD = `1 `+ `X^ ⊤

  ℕ : Set
  ℕ = μ NatD
\end{code}

\AgdaHide{
\begin{code}
  _ :
\end{code}}

\begin{code}
   ⟦ NatD ⟧ ℕ ≡ (⊤ ⊎ (⊤ → ℕ))
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}

The model of the \AgdaCon{zero} constructor is also the same as its
non-infinitary counterpart.

\begin{code}
  zero : ℕ
  zero = init (inj₁ tt)
\end{code}

The model of the \AgdaCon{suc} constructor is different, because
it takes an infinitary argument (\AgdaVar{f}).

\begin{code}
  suc : (⊤ → ℕ) → ℕ
  suc f = init (inj₂ f)
\end{code}

But what if we wanted to model the non-infinitary definition of
natural numbers below, even though we can only
\AgdaData{Descr}ibe infinitary pattern functors?

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\begin{code}
  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ
\end{code}

To model a non-infinitary type with an infinitary pattern functor, we
never need to change the type former (so our definition of
\AgdaData{ℕ} above suffices). Because \AgdaCon{zero} was never
infinitary to begin with, its previous definition can also be
reused.

However, we take special care to model a non-infinitary
\AgdaCon{suc} constructor in terms of its underlying infinitary
pattern functor \AgdaFun{NatD}.
We expose the non-infinitary type signature of
\AgdaCon{suc}, acting as an interface.
The implementation of the \textit{infinitary}
pattern functor of the formal model is hidden by this interface.

\AgdaHide{
\begin{code}
module _ where
 open Desc
 open El
 open Fix
 open import Relation.Binary.PropositionalEquality
 private
  NatD : Desc
  NatD = `1 `+ `X^ ⊤
  ℕ : Set
  ℕ = μ NatD
\end{code}}

\begin{code}
  suc : ℕ → ℕ
  suc n = init (inj₂ (λ u → n))
\end{code}

The implementation ignores the trivial argument \AgdaVar{u} when
constructing the
predecessor as an infinitary function using the inductive input
\AgdaVar{n}.


\paragraph{Binary Trees}

Our pattern functor for binary trees models the the infinitary
definition of binary trees below.

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\begin{code}
  data Tree (A B : Set) : Set where
    leaf : A → Tree A B
    branch : (b : B) (f : Bool → Tree A B) → Tree A B
\end{code}

The description of the binary tree pattern functor, and its type
former, are given below.

\AgdaHide{
\begin{code}
module _ where
 open Desc
 open El
 open Fix
 open import Relation.Binary.PropositionalEquality
 private
\end{code}}

\begin{code}
  TreeD : Set → Set → Desc
  TreeD A B = `κ A `+ (`κ B `∙ `X^ Bool)

  Tree : Set → Set → Set
  Tree A B = μ (TreeD A B)
\end{code}

\AgdaHide{
\begin{code}
  _ : {A B : Set} →
\end{code}}

\begin{code}
   ⟦ TreeD A B ⟧ (Tree A B) ≡ (A ⊎ (B × (Bool → Tree A B)))
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}

The model of the \AgdaCon{leaf} constructor is straightforward, as it
is not infinitary.

\begin{code}
  leaf : {A B : Set} → A → Tree A B
  leaf a = init (inj₁ a)
\end{code}

However, we model a non-infinitary \AgdaCon{branch} constructor in
terms of its underlying infinitary pattern functor. Below the model of
the \AgdaCon{branch} constructor is non-infinitary because its type
signature does not contain any infinitary arguments (despite the fact
that its implementation supplies infinitary values to the
\AgdaCon{init}ial algebra, defined in terms of an infinitary pattern
functor).

\begin{code}
  branch : {A B : Set} → Tree A B → B → Tree A B → Tree A B
  branch t₁ b t₂ = init (inj₂ (b , (λ x → if x then t₁ else t₂)))
\end{code}

The second
component of the pair (in the right disjoint union injection) is an
infinitary function from \AgdaData{Bool} to
\AgdaFun{Tree} \AgdaVar{A} \AgdaVar{B}. Therefore, we simulate a
non-infinitary \AgdaCon{branch} by applying a conditional to the
boolean argument of the function, returning the inductive
\AgdaVar{t₁} argument in the true case and the inductive
\AgdaVar{t₂} argument in the false case.




