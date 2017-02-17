\AgdaHide{
\begin{code}
module _ where
open import Data.Bool
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality
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
\set^I \overset{\leftarrow}{\rightarrow} \set/I
$$

The left direction of this equivalence is the \textit{inverse}
functor ($(\inv) : \set/I \arr \set^I$)
whose object component maps slices $\set/I$ to
families $\set^I$.
$$
(\inv) \triangleq
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

In the following examples we show how to define pattern functors for
indexed types first in the category of families ($\set^I$), and second
in the category of slices ($\set/I$).

%% In \refsec{idxalgmod} we take advantage of the equivalence between
%% family ($\set^I$) and slice ($\set/I$) categories, and reuse our type
%% theoretic semantic model of inductive-recursive types.
%% We \textit{derive} a
%% type theoretic model of indexed types by reifying (a more
%% intentionally precise
%% version of) the inverse functor
%% ($\inv$) as a function translating descriptions of indexed types to descriptions
%% of inductive-recursive types, for which we have an existing algebraic
%% model in type theory (\refsec{iralgmod}).

\paragraph{Vectors}

We will show how to define two different pattern functors for vectors,
first as an endofunctor between type family categories ($\set^\nat$), and
second as an endofunctor between slice categories ($\set/\nat$).
Let's refamiliarize ourselves with the standard type family
definition of vectors \textit{indexed} by the natural numbers.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 private
  Set/ : Set → Set₁
  Set/ O = Σ Set (λ A → (A → O))
\end{code}}

\begin{code}
  data Vec (A : Set) : ℕ → Set where
    nil : Vec A zero
    cons : (m : ℕ) → A → Vec A m → Vec A (suc m)
\end{code}


The definition of vectors above is called a
\textit{general}~\cite{TODO} indexed type,
wherein the constructors \textit{implicitly} constrain the indices according to
the type of their codomain
(e.g. the \AgdaCon{zero} constraint in
\AgdaData{Vec} \AgdaVar{A} \AgdaCon{zero} of the \AgdaCon{nil}
\textit{codomain} above).
Alternatively, a \textit{restricted} indexed type is defined as a
parameterized type, where each constructor gains an additional
\textit{explicit} equality proof argument
(e.g. the \AgdaCon{zero} \AgdaData{≡} \AgdaVar{n}
argument of the \AgdaCon{nil} \textit{domain} below)
to constrain the datatype
parameter. For example, below is the definition of vectors as a
restricted indexed type.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 private
\end{code}}

\begin{code}
  data Vec (A : Set) (n : ℕ) : Set where
    nil : zero ≡ n → Vec A n
    cons : (m : ℕ) → A → Vec A m → suc m ≡ n → Vec A n
\end{code}

We may define the algebraic semantics for the restricted vector type
in terms of the (parameterized) type family endofunctor
($\Fi : \set \arr \set^\nat \arr \set^\nat$) below.
$$
\Fi \defeq \lambda A.~ \lambda X.~ \lambda n.~
\big( (\zero = n) \cdot 1 \big) +
\big( (m : \nat) \cdot A \cdot X~m \cdot (\suc m = n) \cdot 1 \big)
$$

Note that the inductive parameter of the functor ($X : I \arr \set$) is
a type family, allowing the inductive vector to be constrained to be $m$
by applying $X$ to $m$.
Now consider representing this indexed vector type as an
inductive-recursive type. We do this by defining a non-indexed type,
along with a decoding function whose codomain is the type that
originally was the index (i.e. \AgdaData{ℕ}).

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open import Relation.Binary.PropositionalEquality
 private
  Set/ : Set → Set₁
  Set/ O = Σ Set (λ A → (A → O))
\end{code}}

\begin{code}
  mutual
    data Vec₁ (A : Set) : Set where
      nil : Vec₁ A
      cons : (m : ℕ) → A → (xs : Vec₁ A) → Vec₂ xs ≡ m → Vec₁ A

    Vec₂ : {A : Set} → Vec₁ A → ℕ
    Vec₂ nil = zero
    Vec₂ (cons m x xs q) = suc (Vec₂ xs)
\end{code}

The decoding function (\AgdaFun{Vec₂}) returns the left
component of the equality constraint argument
(\AgdaCon{zero} for \AgdaCon{nil}
and \AgdaCon{suc} for \AgdaCon{cons})
in the original indexed type.
Original indices of inductive arguments (\AgdaVar{m}) within left
components are replaced by recursive calls of the decoding function
( \AgdaFun{Vec₂} \AgdaVar{xs}).

The type (\AgdaData{Vec₁}) removes equality constraints at base
cases (\AgdaCon{nil}), but replaces old \textit{index} constraints by new
\textit{decoding function} constraints in the inductive cases
(\AgdaCon{cons}). The replacement constraint for each inductive
argument requires the decoding function (\AgdaFun{Vec₂})
applied to the inductive
argument (\AgdaVar{xs}) to equal the index of the
original inductive argument (\AgdaVar{m}).

At this point we have an inductive-recursive type corresponding to the
first and second components of a slice (i.e. a dependent pair). To
derive an actual indexed type (\AgdaFun{Vec} below),
we must formalize type families
(\AgdaFun{Set}), the inverse functor (\AgdaFun{Inv}), and then apply
the inverse functor to the slice.

\begin{code}
  Set^ : Set → Set₁
  Set^ I = I → Set

  Inv : {I : Set} → Set/ I → Set^ I
  Inv (X , d) i = Σ X (λ x → d x ≡ i)

  Vec : Set → ℕ → Set
  Vec A n = Inv (Vec₁ A , Vec₂) n
\end{code}

\AgdaHide{
\begin{code}
  _ : {A : Set} {n : ℕ} →
\end{code}}

\begin{code}
   Vec A n ≡ Σ (Vec₁ A) (λ xs → Vec₂ xs ≡ n)
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}


Thus, we obtain a type family (\AgdaFun{Vec}) from a slice as a dependent pair
whose first component is the inductive-recursive type
(\AgdaData{Vec₁}),
and whose second component is a proof that constrains
the input index (\AgdaVar{n}) to be equal to the decoding function
applied to the first component (\AgdaFun{Vec₂} \AgdaVar{xs}).

The reason why we could remove (rather than replace) equality constraints from the
base cases of the inductive-recursive type's (\AgdaData{Vec₁}'s) constructors is because
each type family (\AgdaFun{Vec}, represented as a dependent pair) already contains the
constraint in its second component. To faithfully represent
\textit{inductive} occurrences of the
family \AgdaFun{Vec} (appearing within arguments of its first component
\AgdaData{Vec₁}), we must include the underlying
inductive-recursive type \AgdaData{Vec₁} \textit{and} its decoding
function constraint.


%% To a first approximation, we may think of the indexed vectors above as
%% the vectors we model in the category of families ($\set^\nat$). There
%% is a well known equivalence between vectors and lists constrained by
%% their length. Deriving vectors from the \AgdaData{List} type, the
%% \AgdaFun{length} function, and an equality constraint (\AgdaData{≡})
%% allows us to model vectors in the category of slices ($\set/\nat$).

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 private
  Set/ : Set → Set₁
  Set/ O = Σ Set (λ A → (A → O))

\end{code}}

\begin{code}
  data List (A : Set) : Set where
    nil : List A
    cons : A → List A → List A

  length : {A : Set} → List A → ℕ
  length nil = zero
  length (cons x xs) = suc (length xs)

  Vec : Set → ℕ → Set
  Vec A n = Σ (List A) (λ xs → length xs ≡ n)

\end{code}

\subsection{Algebraic Model}\label{sec:idxalgmod}

\subsection{Type Model}\label{sec:idxalgtps}


