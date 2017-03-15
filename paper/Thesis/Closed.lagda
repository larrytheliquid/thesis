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

  mutual
    ⟦_⟧₁ : {O : Set} (D R : Desc O) → Set
    ⟦ ι o ⟧₁ R = ⊤
    ⟦ σ A D ⟧₁ R = Σ A (λ a → ⟦ D a ⟧₁ R)
    ⟦ δ A D ⟧₁ R = Σ (A → μ₁ _ R) λ f → ⟦ D (μ₂ R ∘ f) ⟧₁ R
  
    ⟦_⟧₂ : {O : Set} (D R : Desc O) → ⟦ D ⟧₁ R → O
    ⟦ ι o ⟧₂ R tt = o
    ⟦ σ A D ⟧₂ R (a , xs) = ⟦ D a ⟧₂ R xs
    ⟦ δ A D ⟧₂ R (f , xs) = ⟦ D (λ a → μ₂ R (f a)) ⟧₂ R xs

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

\subsection{Formal Model}

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
(as \Con{`Bool}, rather than \Data{Bool}).

\subsection{Source of Openness}

To discover why \Data{`Set} actually defines an \textit{open}
universe, let's try
to define the type of natural numbers in the universe
(i.e. as a member of \Data{`Set}).

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
The second argument (\Var{D}) of encoded fixpoints
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
  universe, which requires defining generic functions that work
  over any \Con{`μ₁} applied to any \Data{Desc}. We would get suck on
  the \Con{σ} and \Con{δ} cases of such functions, because we could
  \textit{not} case-analyze (or recurse into) the
  \Var{A} arguments of type \Data{Set}.
\end{enumerate}

We overcome these problems, by truly defning \Data{`Set} as a
\textit{closed} universe, in the next section.

\section{Closed Inductive-Recursive Types}\label{sec:closed}

The key to creating an adequate (in intensional type theory)
closed universe of algebraic datatypes is paying attention to
not only \textit{types} (\Data{Set}),
but also \textit{kinds} (\Data{Set₁}).
Previously, we created the \textit{Closed Vector Types} universe
(\refsec{closedvecu}) and the 
\textit{Closed Well-Order Types} universe (\refsec{closedw}).
In those universes, the kind (\Data{Set₁})
of types (\Data{Set}) is the only kind in town. Now we create the
\textit{Closed Inductive-Recursive Types} universe, where we must
additionally consider the kind (\Data{Set₁})
of descriptions (\Data{Desc}).
\footnote{
  The type of types is a kind because \Data{Set} : \Data{Set₁}. Similarly,
  the type of descriptions is a kind because
  \Data{Desc} : (\Var{O} : \Data{Set}) → \Data{Set₁}. Distinctively,
  the type former of descriptions is a function. Even though the function
  domain (\Var{O}) is a type (\Data{Set}), descriptions are still
  kinds because the codomain of the functional type former
  is a kind (\Data{Set₁}). In other words, the codomain of a type
  former determines whether it is a type or a kind,
  not its domain.
  }
The lesson to learn is that closing a universe is not only about
closing over some collection of \textit{types}, but more generally some
collection of \textit{kinds}.

\subsection{Formal Model}

We wish to formally model a closed type theory, supporting
user-declared datatypes, within an open type theory (Agda).
To do so, we define a type of
\textit{closed types} (\Data{`Set}), and a meaning
function mapping each closed type (\Data{`Set}) to an
open type (\Data{Set}) of our model.

We saw in \refsec{naiveclosed} that descriptions
(\Data{Desc}) are actually \textit{open}. Therefore, to model closed
type theory we must also close over descriptions!
To do so, we define a type of
\textit{closed descriptions} (\Data{`Desc}), and a meaning
function mapping each closed description (\Data{`Desc}) to an
open description (\Data{Desc}) of our model.
Below, we \textit{mutually} define
closed types (\Data{`Set}) and
closed descriptions (\Data{`Desc}),
and their meaning functions
(\Fun{⟦\_⟧} and \Fun{⟪\_⟫} respectively).


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

Closed fixpoints (\Con{`μ₁}) of closed types (\Data{`Set})
now take a closed
description (\Data{`Desc}) as their \Var{D} argument,
compared to \refsec{naiveclosed}, where \Var{D}
was an open description (\Data{Desc}).
Correspondingly, closed non-inductive arguments (\Con{`σ}) and closed
infinitary arguments (\Con{`δ}) of
closed descriptions (\Data{`Desc}) now take a
closed type (\Data{`Set}) as their \Var{A} argument.
In contrast, the \Var{A}
argument of \Con{σ} and \Con{δ},
in the definition of open descriptions (\Data{Desc}),
is an open type (\Data{Set}).

Before, the meaning function (\Fun{⟦\_⟧}) for closed types only recursed
on closed types (\Data{`Set}), but now it must mutually recurse using the
meaning function (\Fun{⟪\_⟫}) for closed descriptions (\Data{`Desc}).
For example, consider
the case of defining the meaning of closed fixpoints (\Con{`μ₁}), where
\Fun{⟦\_⟧} is recursively applied to the closed type \Var{O}, and
\Fun{⟪\_⟫} is  recursively applied to the closed description
(\Var{D}).

Conversely, the \Con{`σ} case of the meaning function (\Fun{⟪\_⟫}) for
closed descriptions (\Data{`Desc}) must mutually recurse
using the meaning function (\Fun{⟦\_⟧}) for closed types
(\Data{`Set}). For example, consider
the case of defining the meaning of
non-inductive arguments (\Con{`σ}), where
\Fun{⟪\_⟫} is recursively applied to the closed description
(\Var{D} \Var{a}), and
\Fun{⟦\_⟧} is recursively applied to the closed type \Var{A}.

Finally, notice that closed descriptions (\Data{`Desc}) are
\textit{parameterized} by closed types
(\Var{O} of type \Data{`Set}).
Take a look at the type of the meaning
function (\Fun{⟪\_⟫}) for descriptions,
mapping a closed description (\Data{`Desc} \Var{O})
to an open description (\Data{Desc} \Fun{⟦} \Var{O} \Fun{⟧}).
Because open descriptions expect an
\textit{open type} (\Data{Set}) parameter, we must apply the meaning
function of types (\Fun{⟦\_⟧}) to the closed type \Var{O}, to ensure
that our parameter for open descriptions is well-typed
(i.e. is a \Data{Set} rather than a \Data{`Set}).


\subsection{Kind-Generalized Universes}

Because we are claiming that we are formally modeling a closed
\textit{universe} (\refsec{universes}), we must be able to
point out its type of \textit{codes} and its
\textit{meaning} function. A universe (\Data{Univ}) can be formally
modeled as a dependent record consisting of a \Field{Code} type, and
a \Field{Meaning} function mapping codes to types (\Data{Set}).
\footnote{
  In \refsec{universes}, universes are modeled as a dependent pair
  (\Data{Σ}) type, where the first component is the type of codes and
  the second is the meaning function. The \Data{Univ} record is really
  just a dependent pair that we have named \Data{Univ},
  and whose components we have named \Field{Code} and \Field{Meaning}. 
  }

\AgdaHide{
\begin{code}
module _ where
 private
  data Desc (O : Set) : Set₁ where
  data μ (O : Set) (D : Desc O) : Set where
 
  data `Set : Set where
  data `Desc (O : `Set) : Set where
  postulate
   ⟦_⟧ : `Set → Set
   ⟪_⟫ : {O : `Set} → `Desc O → Desc ⟦ O ⟧
\end{code}}

\begin{code}
  record Univ : Set₁ where
    field
      Code : Set
      Meaning : Code → Set
\end{code}

As expected, the types part of our \textit{Closed Inductive-Recursive Types}
universe is \Data{Univ}, by using \Data{`Set} for the
codes and \Fun{⟦\_⟧} for the meaning function.

\begin{code}
  `SetU : Univ
  `SetU = record { Code = `Set ; Meaning = ⟦_⟧ }
\end{code}

Thus, \Fun{`SetU} is the evidence that
\textit{Closed Inductive-Recursive Types} defines a universe,
where closed type codes \Data{`Set} are formally modeled by the
kind of open types \Data{Set} via the meaning function \Fun{⟦\_⟧}.
Now that we have defined a closed universe modeled in terms of
the kind of open types (\Data{Set}), can we similarly
define a closed universe modeled in terms of our other kind,
namely the kind of open descriptions (\Data{Desc})?

We can, and we call it the
\textit{Closed Inductive-Recursive Descriptions} universe. But first,
we must generalize what it means to be a universe. Previously, we
defined the \Data{Univ} record with a
\Field{Meaning} function whose codomain is the
kind \Data{Set}. Now, we will define a generalized version where the
codomain of the \Field{Meaning} function is an arbitrary
kind (\Var{K} : \Data{Set₁}).

\AgdaHide{
\begin{code}
module _ where
 private
  data Desc (O : Set) : Set₁ where
  data μ (O : Set) (D : Desc O) : Set where
 
  data `Set : Set where
  data `Desc (O : `Set) : Set where
  postulate
   ⟦_⟧ : `Set → Set
   ⟪_⟫ : {O : `Set} → `Desc O → Desc ⟦ O ⟧
\end{code}}

\begin{code}
  record Univ (K : Set₁) : Set₁ where
    field
      Code : Set
      Meaning : Code → K
\end{code}

We can still define
\textit{Closed Inductive-Recursive Types} as a
kind-generalized universe by specializing \Var{K} to the kind
\Data{Set}.

\begin{code}
  `SetU : Univ Set
  `SetU = record { Code = `Set ; Meaning = ⟦_⟧ }
\end{code}

However, now we can also define
\textit{Closed Inductive-Recursive Descriptions} as a
kind-generalized universe by specializing
\Var{K} to the kind \Data{Desc}.

\begin{code}
  `DescU : (O : `Set) → Univ (Desc ⟦ O ⟧)
  `DescU O = record { Code = `Desc O ; Meaning = ⟪_⟫ }
\end{code}

Thus, \Fun{`DescU} is the evidence that
\textit{Closed Inductive-Recursive Descriptions}
is a \textit{parameterized} universe (\refsec{paru}),
where the parameter \Var{O} represents the codomain of the decoding
function of the closed inductive-recursive algebraic datatypes.
If we modeled standard (i.e. not inductive-recursive) dependent
algebraic datatypes (like in \refsec{depalgmod}), then
this parameter would disappear.

By creating a closed universe of types that includes closed
user-declared datatypes modeled using initial algebra semantics, we
learn that the standard notion of a universe in type theory can be
generalized. A universe normally maps codes to \textit{types} (\Data{Set}), but
more generally the meaning function can map codes to any
\textit{kind}, such as \textit{descriptions} (\Data{Desc}).
This generalization explains why we call \Fun{⟦\_⟧} the
\textit{meaning} function for closed types (\Data{`Set}), but
also call \Fun{⟪\_⟫} the \textit{meaning} function
for closed descriptions (\Data{`Desc}).
