\AgdaHide{
\begin{code}
module _ where
open import Function
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Bool
open import Data.Sum
open import Data.String

module Alg where
  data Id (A : Set) (x : A) : A → Set where
    refl : Id A x x

  data Desc (O : Set) : Set₁ where
    ι : (o : O) → Desc O
    σ : (A : Set) (D : A → Desc O) → Desc O
    δ : (A : Set) (D : (A → O) → Desc O) → Desc O

  {-# TERMINATING #-}
  {-# NO_POSITIVITY_CHECK #-}
  mutual
    ⟦_⟧₁ : {O : Set} (D R : Desc O) → Set
    ⟦ ι o ⟧₁ R = ⊤
    ⟦ σ A D ⟧₁ R = Σ A (λ a → ⟦ D a ⟧₁ R)
    ⟦ δ A D ⟧₁ R = Σ (A → μ₁ _ R) λ f → ⟦ D (μ₂ R ∘ f) ⟧₁ R
  
    ⟦_⟧₂ : {O : Set} (D R : Desc O) → ⟦ D ⟧₁ R → O
    ⟦ ι o ⟧₂ R tt = o
    ⟦ σ A D ⟧₂ R (a , xs) = ⟦ D a ⟧₂ R xs
    ⟦ δ A D ⟧₂ R (f , xs) = ⟦ D (μ₂ R ∘ f) ⟧₂ R xs

    data μ₁ (O : Set) (D : Desc O) : Set where
      init : ⟦ D ⟧₁ D → μ₁ O D

    μ₂ : {O : Set} (D : Desc O) → μ₁ O D → O
    μ₂ D (init xs) = ⟦ D ⟧₂ D xs
\end{code}}

\chapter{Closed Algebraic Universe}\label{ch:closed}

In this chapter we formally model a closed type theory,
or dependently typed language, supporting declared
datatypes and fully generic programming. The high-level idea is to
define a closed type theory, similar to the
\textit{Closed Well-Order Types} universe of \refsec{wuni},
but replacing \Data{W} types (\refsec{wtypes}) with
fixpoints (\Data{μ₁}) of descriptions
(formally modeling initial algebra semantics, as in
\refsec{iralgmod}).
Initial algebra semantics, unlike well-orderings,
adequately models declared datatypes in
intensional (as opposed to extensional) type theory.

We begin with a naive failed attempt at defining a closed type theory
using fixpoints (\refsec{naiveclosed}). After explaining why the
simple but naive attempt actually defines an open (rather than
closed) type theory, we explain how to properly close the theory
(\refsec{closed}).

\section{Open Inductive-Recursive Types}\label{sec:naiveclosed}

In this section we present a naive failed attempt at creating a
\textit{closed} universe using fixpoints. It is a failed attempt
because it actually defines an \textit{open} universe.
We will define a universe similar to the
\textit{Closed Well-Order Types} of \refsec{wtypes}, but replacing
\Data{W} with \Data{μ₁}, and
adding the identity (or equality) type \Data{Id}.
First, let's remind ourselves of the definitions of the identity type, and
the type of fixpoints for inductive-recursive definitions.

\AgdaHide{
\begin{code}
module _ where
 private
  data Desc (O : Set) : Set where
  postulate ⟦_⟧₁ : {O : Set} (D R : Desc O) → Set
\end{code}}

\begin{code}
  data Id (A : Set) (x : A) : A → Set where
    refl : Id A x x

  data μ₁ (O : Set) (D : Desc O) : Set where
    init : ⟦ D ⟧₁ D → μ₁ O D
\end{code}

The identity type allows us to propositionally state that two values
(\Var{x} and \Var{y}) are equal. If they are indeed equal,
the constructor \Con{refl} serves as a proof of the proposition.
In previous parts of this disseration, we used an infix
version of the identity type (\Data{≡}), in which the type of the
compared values is implicit. Here, we use \Data{Id} so we can
explicitly refer to the type (\Var{A}) of the compared values.
Similarly, above we define a version of the fixpoint operator
(\Data{μ₁}) that explicitly takes the codomain (\Var{O})
of the inductive-recursive decoding function.

In the vector example of \refsec{iralgtps} we saw that \textit{indexed types}
can be derived from \textit{inductive-recursive types} and
\textit{equality constraints}
(i.e. use of identity type). In our universe below, we want to encode
indexed types in addition to inductie-recursive types, thus we
replace \Con{`W} with \Con{`μ₁}, \textit{and} add
\Con{`Id}.

\AgdaHide{
\begin{code}
module _ where
 private
  data Id (A : Set) (x : A) : A → Set where
  data Desc (O : Set) : Set₁ where
    ι : (o : O) → Desc O
    σ : (A : Set) (D : A → Desc O) → Desc O
    δ : (A : Set) (D : (A → O) → Desc O) → Desc O
  data μ₁ (O : Set) (D : Desc O) : Set where
\end{code}}

\begin{code}
  mutual
    data `Set : Set₁ where
      `⊥ `⊤ `Bool : `Set
      `Σ `Π : (A : `Set) (B : ⟦ A ⟧ → `Set) → `Set
      `Id : (A : `Set) (x y : ⟦ A ⟧) → `Set
      `μ₁ : (O : `Set) (D : Desc ⟦ O ⟧) → `Set 

    ⟦_⟧ : `Set → Set
    ⟦ `⊥ ⟧ = ⊥
    ⟦ `⊤ ⟧ = ⊤
    ⟦ `Bool ⟧ = Bool
    ⟦ `Σ A B ⟧ = Σ ⟦ A ⟧ (λ a → ⟦ B a ⟧)
    ⟦ `Π A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
    ⟦ `Id A x y ⟧ = Id ⟦ A ⟧ x y
    ⟦ `μ₁ O D ⟧ = μ₁ ⟦ O ⟧ D
\end{code}

Nothing immediately stands out as being problematic, as our
universe looks quite like the \textit{Closed Well-Order Types}
universe. Let's take a closer look at why the addition of the
identity type (\Con{`Id})
is not problematic, but the addition of fixpoints
(\Con{`μ₁}) is, by constructing values of both.
First, we construct the (false) boolean proposition that true
is equal to false, using the identity type.

\begin{code}
  `Bottom : `Set
  `Bottom = `Id `Bool true false
\end{code}

Above, the proposition (\Fun{`Bottom}) can be encoded in the
universe (i.e. defined as a value of \Data{`Set})
by using the encoded identity type
(\Con{`Id}, rather than \Data{Id}).
Additionally, the type of the compared values
in the proposition can also be encoded in the universe
(as \Con{`Bool}, rather than \Data{Bool}). Next, let's try
to define the type of natural numbers in the universe.

\begin{code}
  NatD : Desc ⊤
  NatD = σ Bool (λ b → if b then ι tt else δ ⊤ (λ u → ι tt))

  `ℕ : `Set
  `ℕ = `μ₁ `⊤ NatD
\end{code}

Above, the type of natural numbers (\Fun{`ℕ})
and the codomain of the decoding
function can be defined \textit{within} the universe
(using \Con{`μ₁} and \Con{`⊤} respectively, rather than
\Data{μ₁} and \Data{⊤}). However, the
description (\Fun{NatD}) of the natural numbers is defined
\textit{outside} of the universe. This is because
\Con{σ} and \Con{δ} are respectively applied to the types
\Data{Bool} and \Data{⊤}, which are \textit{not} members of the
universe \Data{`Set}. Instead, they are types
(\Data{Set}) of our \textit{open} metatheory (Agda).
The second argument (\Var{D}) to code of fixpoints
(\Con{`μ₁}) has type \Data{Desc}, which seems harmless. However, let's
inspect the definition of descriptions.

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\begin{code}
  data Desc (O : Set) : Set₁ where
    ι : (o : O) → Desc O
    σ : (A : Set) (D : A → Desc O) → Desc O
    δ : (A : Set) (D : (A → O) → Desc O) → Desc O
\end{code}

The root of the problem is that the \Var{A} argument of \Con{σ} and
\Con{δ} has Agda's type \Data{Set}, rather a code of our universe
\Data{`Set}. Hence, the universe \Data{`Set} that we defined is
actually \textit{open} because \Con{`μ₁} has an argument
\Var{D} of type \Data{Desc}, which is an open type because it has \Data{Set}
arguments.
There are 2 major consequences resulting from \Con{`μ₁} having
an open type argument (\Var{D}):
\begin{enumerate}
\item Encodings of declared algebraic datatypes can include
  non-inductive arguments (and decoding codomains) whose types are
  \textit{not} in the universe \Data{`Set}. For example, a constructor
  could have a vector (\Data{Vec}) argument, which is in Agda's
  open universe \Data{Set}, rather than our universe \Data{`Set}
  (that we intended to be closed).
\item We \textit{cannot} write fully generic functions over the
  universe, which requires defining generic function that works
  over any \Con{`μ₁} applied to any \Data{Desc}. We would get suck on
  the \Con{σ} and \Con{δ} cases of such functions, because we could
  \textit{not} case-analyze (or recurse into) the
  \Var{A} arguments of type \Data{Set}.
\end{enumerate}

We overcome these problems, by truly defning \Data{`Set} as a
\textit{closed} universe, in the next section.

\section{Closed Inductive-Recursive Types}\label{sec:closed}

\AgdaHide{
\begin{code}
module _ where
 open Alg
 private
\end{code}}

\begin{code}
  mutual
    data `Set : Set where
      `⊥ `⊤ `Bool : `Set
      `Σ `Π : (A : `Set) (B : ⟦ A ⟧ → `Set) → `Set
      `Id : (A : `Set) (x y : ⟦ A ⟧) → `Set
      `μ₁ : (O : `Set) (D : `Desc O) → `Set 

    ⟦_⟧ : `Set → Set
    ⟦ `⊥ ⟧ = ⊥
    ⟦ `⊤ ⟧ = ⊤
    ⟦ `Bool ⟧ = Bool
    ⟦ `Σ A B ⟧ = Σ ⟦ A ⟧ (λ a → ⟦ B a ⟧)
    ⟦ `Π A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
    ⟦ `Id A x y ⟧ = Id ⟦ A ⟧ x y
    ⟦ `μ₁ O D ⟧ = μ₁ ⟦ O ⟧ ⟪ D ⟫

    data `Desc (O : `Set) : Set where
      `ι : (o : ⟦ O ⟧) → `Desc O
      `σ : (A : `Set) (D : ⟦ A ⟧ → `Desc O) → `Desc O
      `δ : (A : `Set) (D : (o : ⟦ A ⟧ → ⟦ O ⟧) → `Desc O)
        → `Desc O
  
    ⟪_⟫ : {O : `Set} → `Desc O → Desc ⟦ O ⟧
    ⟪ `ι o ⟫ = ι o
    ⟪ `σ A D ⟫ = σ ⟦ A ⟧ (λ a → ⟪ D a ⟫)
    ⟪ `δ A D ⟫ = δ ⟦ A ⟧ (λ o → ⟪ D o ⟫)
\end{code}

