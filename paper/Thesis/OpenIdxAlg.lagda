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

We show how to define two different pattern functors for vectors,
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

The algebraic semantics that we use for indexed types models the
restricted version of indexed types.
\footnote{It is adequate to only model restricted indexed types
  because restricted and general indexed types are isomorphic. This is
  adequate because our algebraic semantics for
  types with various properties identifies isomorphic types
  (e.g. inductive arguments and trivially infinitary
  arguments are isomorphic).
}
We define the algebraic semantics for the restricted vector type
in terms of the (parameterized) \textit{type family} endofunctor
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
originally was the index (i.e. \AgdaData{ℕ}). We transform the indexed
type into an inductive-recursive type in 3 steps:

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

\begin{enumerate}
\item The decoding function (\AgdaFun{Vec₂}) is defined by returning the
left component of the equality constraint argument
(\AgdaCon{zero} for \AgdaCon{nil}
and \AgdaCon{suc} for \AgdaCon{cons})
in the original indexed type (\AgdaData{Vec}).
Original indices of inductive arguments (\AgdaVar{m}) within left
components are replaced by recursive calls of the decoding function
(\AgdaFun{Vec₂} \AgdaVar{xs}).

\item The inductive-recursive type (\AgdaData{Vec₁}) removes
(from the original indexed type \AgdaData{Vec})
equality constraints at base
cases (\AgdaCon{nil}), but replaces old \textit{index} constraints by new
\textit{decoding function} constraints in the inductive cases
(\AgdaCon{cons}). The replacement constraint for each inductive
argument constrains the decoding function (\AgdaFun{Vec₂})
applied to the inductive
argument (\AgdaVar{xs}) to be equal to the index of the
original inductive argument (\AgdaVar{m}).

\item At this point we have an inductive-recursive type corresponding to the
first and second components of a slice (i.e. a dependent pair). To
derive an actual indexed type (\AgdaFun{Vec} below),
we must formalize type families
(\AgdaFun{Set}), the inverse functor (\AgdaFun{Inv}), and then apply
the inverse functor to the slice.
\end{enumerate}

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
constraint (\AgdaData{≡}) in its second component. To faithfully represent
\textit{inductive} occurrences of the
family \AgdaFun{Vec} (appearing within arguments of its first component
\AgdaData{Vec₁}), we must include the underlying
inductive-recursive type \AgdaData{Vec₁} \textit{and} its decoding
function constraint.

We could emphasize that the inductive-recursive type \AgdaData{Vec₁}
contains inductive arguments of the derived indexed type \AgdaFun{Vec}
by defining them mutually. In the mutual definition, we replace the
inductive \AgdaData{Vec₁} argument and the decoding
constraint (\AgdaData{≡})
argument with a single \AgdaFun{Vec} argument.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open import Relation.Binary.PropositionalEquality
 private
  Set/ : Set → Set₁
  Set/ O = Σ Set (λ A → (A → O))

  Set^ : Set → Set₁
  Set^ I = I → Set

  Inv : {I : Set} → Set/ I → Set^ I
  Inv (X , d) i = Σ X (λ x → d x ≡ i)
\end{code}}

\begin{code}
  mutual
    Vec : Set → ℕ → Set
    Vec A n = Inv (Vec₁ A , Vec₂) n

    data Vec₁ (A : Set) : Set where
      nil : Vec₁ A
      cons : (m : ℕ) → A → (xs : Vec A m) → Vec₁ A

    Vec₂ : {A : Set} → Vec₁ A → ℕ
    Vec₂ nil = zero
    Vec₂ (cons m x (xs , q)) = suc (Vec₂ xs)
\end{code}

Finally, let's define the algebraic semantics for the derived vector
type family in terms of the (parameterized) \textit{slice} endofunctor
($\Fo : \set \arr \set/\nat \arr \set/\nat$) and
\textit{inverse} functor ($(\inv) : \set/I \arr \set^I$) below.
Note that it is easier to see the resemblance between the functor $G$
and the version of the \AgdaData{Vec₁} and \AgdaFun{Vec₂} \textit{not}
mutually defined with \AgdaFun{Vec}.
$$
\Fo \defeq \lambda A.~ \lambda (X, d).~
\iota~\zero +
(m : \nat) \cdot A \cdot (x : X) \cdot (d~x = m) \cdot
\iota~(\suc(d~x))
$$

Now that we have the endofunctor $\Fo$ between slices
($\set/\nat$), we can apply
the inverse functor to $\Fo$ and get a pattern functor that behaves
isomorphically (i.e. among objects resulting from applying each
functor to any type family $X$) to our previously defined endofunctor $\Fi$ between type
families ($\set^\nat$).
$$
\forall X.~ \Fi~X \simeq \Fo\inv~X
$$

For one additional insight, consider the popular derivation of the
vector type from the \AgdaData{List} type, the \AgdaFun{length}
function, and an equality constraint (\AgdaData{≡}). 

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

Above, \AgdaData{List} is similar to \AgdaData{Vec₁}
and \AgdaFun{length} is similar to \AgdaFun{Vec₂}. The main difference
is that the \AgdaCon{cons} constructor of \AgdaData{List} does not
have a natural number \AgdaVar{m} argument, or an equality
constraint (and because it does not have an equality constraint, it also
does not need to be defined inductive-recursively). Previously
we explained that we want inductive occurrences of \AgdaData{Vec₁}
to be the derived type family \AgdaFun{Vec}, which is not the case
with \AgdaData{List}. Nevertheless, the derivation of vectors
from a relationship between lists and their length serves as good
intuition for how type families ($\set^I$) are derived from inductive-recursive
slices ($\set/I$) and the inverse functor ($\inv$).

\paragraph{Natural Numbers}

We use the natural numbers as an example of a non-indexed type.
First, we model the natural numbers as a \textit{trivially indexed}
type using an endofunctor between type family categories
($\set^1$). Second,
we show how converting the type-family-based ($\set^1$) definition to
a slice-based ($\set/1$) using our rules results in modeling a
\textit{trivially inductive-recursive} type.

Let's begin by defining the natural numbers as a trivially indexed
type.

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\begin{code}
  data ℕ : ⊤ → Set where
    zero : ℕ tt
    suc : {u : ⊤} → ℕ u → ℕ u
\end{code}

We use a version where the codomain of inductive constructors
(\AgdaCon{suc}) reuses the the index (\AgdaVar{u}) of their inducive
arguments, and the base cases (\AgdaCon{zero}) are indexed by the
trivial value (\AgdaCon{tt}). Alternatively, we could have made
inductive constructor codomains and inductive arguments be immediately
indexed by \AgdaCon{tt}. Below is the restricted version of the
trivially indexed type of natural numbers.

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\begin{code}
  data ℕ (u : ⊤) : Set where
    zero : tt ≡ u → ℕ u
    suc : {v : ⊤} → ℕ v → v ≡ u → ℕ u
\end{code}

We define the algebraic semantics for the restricted trivially indexed
natural number type
in terms of the \textit{type family} endofunctor
($\Fi : \set^1 \arr \set^1$) below.
$$
\Fi \defeq \lambda X.~ \lambda u.~
\big( (\bullet = u) \cdot 1 \big) +
\big( (v : 1) \cdot X~v \cdot (v = u) \cdot 1 \big)
$$


\subsection{Algebraic Model}\label{sec:idxalgmod}

\subsection{Type Model}\label{sec:idxalgtps}


