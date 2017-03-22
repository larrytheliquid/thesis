\AgdaHide{
\begin{code}
module _ where
open import Function
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Sum
open import Data.String

module Alg where
  open import Data.Product
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
 open import Data.Product
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
closed universe of algebraic datatypes is paying attention not
only to \textit{types} (\Data{Set}),
but also \textit{kinds} (\Data{Set₁}).
Previously, we created the \textit{Closed Vector Types} universe
(\refsec{closedvecu}) and the 
\textit{Closed Well-Order Types} universe (\refsec{closedw}).
In those universes, the kind (\Data{Set₁})
of types (\Data{Set}) is the only kind in town. Now we create the
\textit{Closed Inductive-Recursive Types} universe, where we
additionally account for the kind (\Data{Set₁})
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
 open import Data.Product
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

Notice that closed descriptions (\Data{`Desc}) are
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

Finally, recall that our naive attempt
(in \refsec{naiveclosed}) at closing the universe failed,
because the resulting universe is actually open. 
In \refsec{naiveclosed}, \Data{`Set} contains a
\Var{D} argument (in \Con{`μ₁}) whose \textit{kind} (\Data{Set₁})
is \Data{Desc}. Therefore, \Data{`Set} of \refsec{naiveclosed} must be a
\textit{kind}, to account for the size of its \Var{D} argument.
In contrast, the closed universe of types
(\Data{`Set}) of this section, and the
closed universe of descriptions (\Data{`Desc}), are merely
\textit{types} (\Data{Set}). Moreover, a measure of success for closing
a universe is the ability to fit
it in the size of types (\Data{Set}) rather kinds (\Data{Set₁}).

\subsection{Example Values}


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

As expected, we can model the
\textit{Closed Inductive-Recursive Types}
universe as a member \Data{Univ}, by using \Data{`Set} for the
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
kind \Data{Set}. Now, we define a generalized version where the
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


\section{How to Close a Universe}\label{sec:closing}

The closed universe of \refsec{closed} is a fine result, as it
supports user-declared datatypes,
but also fully generic programming (demonstrated in \refchap{fullyg}).
However, readers may be curious how we arrived at this universe.
Perhaps, more importantly, what \textit{procedure} turns
an open universe into a closed version? You may want to
support fully generic programming over a universe that represents
algebraic datatypes with different properties,
or uses a different encoding of descriptions, or
uses an entirely different style of semantics. We describe
a procedure to close a universe below.

\subsection{Procedure}

\begin{enumerate}
\item Select a kind \Var{K}, then mutually:

  \begin{enumerate}
  \item Declare a \textit{kind} \Var{`K},
    representing (what will be) closed codes of \Var{K}.
  \item For each formation rule of \Var{K},
    encode it as a constructor of \Var{`K}.
  \item Define a meaning function (\Fun{⟦\_⟧}) mapping each encoded constructor
    of \Var{`K} to the actual \Var{K} formation rule it represents.
  \end{enumerate}

\item In the kind former and constructors of \Var{`K}, and in the body of the
  meaning function (\Fun{⟦\_⟧}), simultaneously:
  \begin{enumerate}
  \item Replace occurrences of the kind \Var{K} with its closed encoding \Var{`K}.
  \item Replace references to \Var{A} of kind \Var{K}
    with the meaning function applied to the reference
    (\Fun{⟦} \Var{A} \Fun{⟧}).
  \end{enumerate}

\item Recursively apply this procedure for another kind \Var{J}.
  \begin{enumerate}
  \item Select \Var{J} from the arguments of either the kind former,
    or formation rules, of \Var{K}.
  \item In the recursive Step 1, for any \Var{K}  that has already
    been closed over, implicitly replace \Var{K} and its
    references with \Var{`K} and applications of its meaning function
    (\Fun{⟦\_⟧}).
  \end{enumerate}

\item Change \Var{`K} from a \textit{kind} to a \textit{type}, by
  replacing \Data{Set} with \Data{Set₁} in the codomain of the
  kind former of \Var{`K}.
\end{enumerate}

In the procedure above, all closed codes \Var{`K},
and their meaning functions (\Fun{⟦\_⟧}),
are \textit{mutually} defined.
Once the procedure terminates, all closed codes \Var{`K}
will be \textit{types} (\Data{Set}),
rather than \textit{kinds} (\Data{Set₁}),
thanks to \textbf{Step 4}. 

\subsection{Example Run}

Typically, we are interested
in closing over a universe of types, so our initial \Var{K} will be
the kind of open types (\Data{Set}), and its formation rules will
be \textit{type formers}
(e.g. \Data{Bool}, \Data{Id}, \Data{Σ}, \Data{μ₁}, etc.)
of some finite collection of types.
Subsequently, other kinds \Var{K} (e.g. \Data{Desc})
that we encounter have
\textit{constructors} (e.g. \Con{ι}, \Con{σ}, and \Con{δ})
as their formation rules.
For example, consider closing over the subset of the
kind \Data{Set} below.

\AgdaHide{
\begin{code}
module _ where
 private
  data Desc (O : Set) : Set where
  postulate ⟦_⟧₁ : {O : Set} (D R : Desc O) → Set
\end{code}}

\begin{code}
  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

  data Vec (A : Set) : ℕ → Set where
    nil : Vec A zero
    cons : {n : ℕ} → A → Vec A n → Vec A (suc n)

  data μ₁ (O : Set) (D : Desc O) : Set where
    init : ⟦ D ⟧₁ D → μ₁ O D
\end{code}

\paragraph{Step 1}

We select \Var{K} to be kind \Data{Set}, and
the \textit{type formers} of the collection of types above are its
\textit{formation rules}. Once this step is complete,
\Var{`K} is \Data{`Set} (representing what will be closed types),
and its meaning function is \Fun{⟦\_⟧}.
We present both below.

\AgdaHide{
\begin{code}
module _ where
 private
  data ℕ : Set where
  data Vec (A : Set) : ℕ → Set where
  data Desc (O : Set) : Set where
  data μ₁ (O : Set) (D : Desc O) : Set where
\end{code}}

\begin{code}
  data `Set : Set₁ where
    `ℕ : `Set
    `Vec : (A : Set) (n : ℕ) →  `Set
    `μ₁ : (O : Set) (D : Desc O) → `Set

  ⟦_⟧ : `Set → Set
  ⟦ `ℕ ⟧ = ℕ
  ⟦ `Vec A n ⟧ = Vec A n
  ⟦ `μ₁ O D ⟧ = μ₁ O D
\end{code}

\paragraph{Step 2}

Next, we replace occurrences of \Data{Set} with \Data{`Set},
and references \Var{A} of kind \Data{Set} with
\Fun{⟦} \Var{A} \Fun{⟧}.

\AgdaHide{
\begin{code}
module _ where
 private
  data ℕ : Set where
  data Vec (A : Set) : ℕ → Set where
  data Desc (O : Set) : Set where
  data μ₁ (O : Set) (D : Desc O) : Set where
  mutual
\end{code}}

\begin{code}
   data `Set : Set₁ where
     `ℕ : `Set
     `Vec : (A : `Set) (n : ℕ) →  `Set
     `μ₁ : (O : `Set) (D : Desc ⟦ O ⟧) → `Set
 
   ⟦_⟧ : `Set → Set
   ⟦ `ℕ ⟧ = ℕ
   ⟦ `Vec A n ⟧ = Vec ⟦ A ⟧ n
   ⟦ `μ₁ O D ⟧ = μ₁ ⟦ O ⟧ D
\end{code}

At this point, our universe is quite like
our failed attempt of a closed universe (\refsec{naiveclosed}),
because \Data{Desc} in argument \Var{D} of \Con{`μ₁} is not closed yet.

\paragraph{Step 3}

Next, we encounter of the kind of descriptions (\Data{Desc}) in the
\Var{D} argument of the \Con{`μ₁} constructor,
so we must recursively apply the
procedure by choosing \Var{J} to be \Data{Desc}.
We establish the Step $x$.$y$ naming convention, where $y$ refers to
the step number in the recursive call (encoding \Data{Desc}),
and $x$ refers to the
original step before the recursion (encoding \Data{Set}).
For reference, we present the kind of descriptions below.

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

\paragraph{Step 3.1}

The \textit{constructors} of \Data{Desc} above are its
\textit{formation rules}. Once this step is complete,
\Var{`J} is \Data{`Desc}
(representing what will be closed descriptions),
and its meaning function is \Fun{⟪\_⟫}.
We present both below.

\AgdaHide{
\begin{code}
module _ where
 private
  data ℕ : Set where
  data Vec (A : Set) : ℕ → Set where
  data Desc (O : Set) : Set₁ where
    ι : (o : O) → Desc O
    σ : (A : Set) (D : A → Desc O) → Desc O
    δ : (A : Set) (D : (A → O) → Desc O) → Desc O
  data μ₁ (O : Set) (D : Desc O) : Set where
  mutual
   data `Set : Set₁ where
     `ℕ : `Set
     `Vec : (A : `Set) (n : ℕ) →  `Set
     `μ₁ : (O : `Set) (D : Desc ⟦ O ⟧) → `Set
 
   ⟦_⟧ : `Set → Set
   ⟦ `ℕ ⟧ = ℕ
   ⟦ `Vec A n ⟧ = Vec ⟦ A ⟧ n
   ⟦ `μ₁ O D ⟧ = μ₁ ⟦ O ⟧ D
\end{code}}

\begin{code}
  data `Desc (O : `Set) : Set₁ where
    `ι : (o : ⟦ O ⟧) → `Desc O
    `σ : (A : `Set) (D : ⟦ A ⟧ → Desc ⟦ O ⟧) → `Desc O
    `δ : (A : `Set) (D : (⟦ A ⟧ → ⟦ O ⟧) → Desc ⟦ O ⟧) → `Desc O

  ⟪_⟫ : {O : `Set} → `Desc O → Desc ⟦ O ⟧
  ⟪ `ι o ⟫ = ι o
  ⟪ `σ A D ⟫ = σ ⟦ A ⟧ D
  ⟪ `δ A D ⟫ = δ ⟦ A ⟧ D
\end{code}

Notice that the kind former argument
\Var{O} (of \Data{`Desc}) \textit{already} has
kind \Data{`Set} (rather than \Data{Set})
because \Data{Set} was previously encoded as \Data{`Set}.
Similarly, \Var{A} arguments of \Data{`Desc} constructors,
and the \Var{O} argument in the type of
the closed descriptions meaning function (\Fun{⟪\_⟫}),
\textit{already} have kind \Data{`Set}.
In all 3 of these places, \textit{and} the body of
the closed descriptions meaning function (\Fun{⟪\_⟫}),
references (e.g. \Var{A}) to kinds
\Data{`Set} \textit{already}
have the meaning function of closed types
applied to them (e.g. \Fun{⟦} \Var{A} \Fun{⟧}).

\paragraph{Step 3.2}

Next, we replace occurrences of \Data{Desc} with \Data{`Desc},
and references \Var{D} of kind \Data{Desc} with
\Fun{⟪} \Var{D} \Fun{⟫}.

\AgdaHide{
\begin{code}
module _ where
 private
  data ℕ : Set where
  data Vec (A : Set) : ℕ → Set where
  data Desc (O : Set) : Set₁ where
    ι : (o : O) → Desc O
    σ : (A : Set) (D : A → Desc O) → Desc O
    δ : (A : Set) (D : (A → O) → Desc O) → Desc O
  data μ₁ (O : Set) (D : Desc O) : Set where
  mutual
   data `Set : Set₁ where
     `ℕ : `Set
     `Vec : (A : `Set) (n : ℕ) →  `Set
     `μ₁ : (O : `Set) (D : `Desc O) → `Set
 
   ⟦_⟧ : `Set → Set
   ⟦ `ℕ ⟧ = ℕ
   ⟦ `Vec A n ⟧ = Vec ⟦ A ⟧ n
   ⟦ `μ₁ O D ⟧ = μ₁ ⟦ O ⟧ ⟪ D ⟫
\end{code}}

\begin{code}
   data `Desc (O : `Set) : Set₁ where
     `ι : (o : ⟦ O ⟧) → `Desc O
     `σ : (A : `Set) (D : ⟦ A ⟧ → `Desc O) → `Desc O
     `δ : (A : `Set) (D : (⟦ A ⟧ → ⟦ O ⟧) → `Desc O) → `Desc O
   
   ⟪_⟫ : {O : `Set} → `Desc O → Desc ⟦ O ⟧
   ⟪ `ι o ⟫ = ι o
   ⟪ `σ A D ⟫ = σ ⟦ A ⟧ (λ a → ⟪ D a ⟫)
   ⟪ `δ A D ⟫ = δ ⟦ A ⟧ (λ o → ⟪ D o ⟫)
\end{code}

Notice that \Data{`Desc} (which replaced \Data{Desc}
in the \Var{D} arguments of the
\Con{`μ₁}, \Con{`σ}, and \Con{`δ} constructors) is applied to
\Var{O}, without the closed types meaning function
(\Fun{⟦\_⟧}), because the \Data{`Desc} kind former
expects a closed type (\Data{`Set}).

Additionally, the \Con{`σ} and \Con{`δ} cases of the
closed descriptions meaning function (\Fun{⟪\_⟫}) now recursively
apply \Fun{⟪\_⟫} to the result of the infinitary function \Var{D}.

\paragraph{Step 4}

Because there are no kinds left to recursively apply the procedure to,
steps 4.1 and 4.2 can be completed by changing
closed types (\Data{`Set}) and closed descriptions (\Data{`Desc}) from
\textit{kinds} to \textit{types}.
Any kinds that were arguments of the original collection of type
formers have been replaced by types, making the final universe
closed. Below is the final result of the procedure.

\AgdaHide{
\begin{code}
module _ where
 private
  data ℕ : Set where
  data Vec (A : Set) : ℕ → Set where
  data Desc (O : Set) : Set₁ where
    ι : (o : O) → Desc O
    σ : (A : Set) (D : A → Desc O) → Desc O
    δ : (A : Set) (D : (A → O) → Desc O) → Desc O
  data μ₁ (O : Set) (D : Desc O) : Set where
\end{code}}

\begin{code}
  mutual
   data `Set : Set where
     `ℕ : `Set
     `Vec : (A : `Set) (n : ℕ) →  `Set
     `μ₁ : (O : `Set) (D : `Desc O) → `Set
 
   ⟦_⟧ : `Set → Set
   ⟦ `ℕ ⟧ = ℕ
   ⟦ `Vec A n ⟧ = Vec ⟦ A ⟧ n
   ⟦ `μ₁ O D ⟧ = μ₁ ⟦ O ⟧ ⟪ D ⟫

   data `Desc (O : `Set) : Set where
     `ι : (o : ⟦ O ⟧) → `Desc O
     `σ : (A : `Set) (D : ⟦ A ⟧ → `Desc O) → `Desc O
     `δ : (A : `Set) (D : (⟦ A ⟧ → ⟦ O ⟧) → `Desc O) → `Desc O
   
   ⟪_⟫ : {O : `Set} → `Desc O → Desc ⟦ O ⟧
   ⟪ `ι o ⟫ = ι o
   ⟪ `σ A D ⟫ = σ ⟦ A ⟧ (λ a → ⟪ D a ⟫)
   ⟪ `δ A D ⟫ = δ ⟦ A ⟧ (λ o → ⟪ D o ⟫)
\end{code}

Reflecting upon how the procedure operates, we come to understand
that only \textit{kind} arguments of the original type
formers are encoded, and the meaning function is only applied to
members of kinds. This explains why the \Data{ℕ} argument of the
vector type former (encoded as \Con{`Vec}) did \textit{not} get
encoded. Hence, we \textit{did not} a create a code (i.e. \Con{`ℕ})
and meaning function for the \textit{type} of natural numbers, but we
\textit{did} (i.e. \Con{`Desc}) for the \textit{kind} of descriptions.
Additionally, the type meaning function
(\Fun{⟦\_⟧}) does not recurse on \Var{n} in the \Con{`Vec} case, nor
does the description meaning function (\Fun{⟪\_⟫})
recurse on \Var{o} in the
\Con{`ι} case, because both \Var{n} and \Var{o} are values of
a \textit{type} rather than members of a \textit{kind}.

\section{Types versus Kinds}

In \refsec{closing} we explain how to close over a subset of
types, mutually by closing over descriptions.
In this section we examine the distinctions between kinds and types in
more detail. In particular, we compare and contrast the kind of types
and descriptions, and where they show up (and do not show up) in the
universe construction.

\subsection{Open Types and Kinds}

While both type (\Data{Set}) and descriptions (\Data{Desc})
are \textit{open} kinds (\Data{Set₁}), somehow \Data{Desc} feels
``more closed'' than \Data{Set}. We will precisely identity the
properties that cause that feeling, by comparing and contrasting
the open \textit{kinds} \Data{Set} and \Data{Desc}.
First, let's revisit the idea of open \textit{types}
from \refsec{open}.

\paragraph{Lists}

Consider the type of lists (\Data{List} below),
parameterized by some type \Var{A} (representing the type of the
elements of the list).
\Data{List} is an \textit{open type},
because its collection of values is open.
Hence, whenever a new type is declared (in open type theory), it can
be used as the \Var{A} parameter
(e.g. by applying \Data{List} to \Data{Bool}, \Data{Tree}, etc.).
This is because the kind of the \Var{A} parameter is \Data{Set}, the
canonical source of openness.

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\begin{code}
  data List (A : Set) : Set where
    nil : List A
    cons : (a : A) (xs : List A) → List A
\end{code}

While the type of lists (\Data{List}) is \textit{open}, it is
inductively defined by a \textit{closed} collection of constructors.
This may seem obvious, but we will return to this point when
discussing the difference between the kinds \Data{Set} and
\Data{Desc}.

\paragraph{Descriptions}

Now let's consider the kind of descriptions (\Data{Desc} below),
parameterized by some type \Var{O}, representing the codomain of the
inductive-recursive decoding function.
\Data{Desc} is an \textit{open kind},
because its collection of elements is open. Henceforth, we refer to
the inhabitants of kinds as \textit{large values} (we could emphasize
the distinction with inhabitants of types by calling them
\textit{small values}). 

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

Similar to why \Data{List} is an open type, \Data{Desc} is an open
kind because its collection of large values grows as its \Var{O} parameter
is instantiated to different types, and is used as the type of the
\Var{o} argument in the \Con{ι} constructor. Another reason why descriptions
are an open kind, is because the \Var{A} argument of the \Con{σ} and
\Con{δ} constructors have kind \Data{Set}. Because \Data{Desc}
constructors define elements of a kind, we sometimes call them
\textit{large constructors}.

While the kind of descriptions (\Data{Desc}) is \textit{open}, it is
inductively defined by a \textit{closed} collection of constructors.
The \Data{List} type and \Data{Desc} kind are
both \textit{open}, but are defined by a \textit{closed} collection of
constructors, because they are both \textit{inductively defined}.

\paragraph{Types}

Finally, consider the kind of types (\Data{Set}). The kind of types is
open, as it is the canonical source of openness. Unlike \Data{Desc},
\Data{Set} is \textit{not} inductively defined. Every time a new
type is declared, its type former becomes a new ``constructor'' of the
kind of types (\Data{Set}). For example, consider the datatype
declarations below.

\AgdaHide{
\begin{code}
module _ where
 private
  data Desc (O : Set) : Set where
  postulate ⟦_⟧₁ : {O : Set} (D R : Desc O) → Set
\end{code}}

\begin{code}
  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

  data Vec (A : Set) : ℕ → Set where
    nil : Vec A zero
    cons : {n : ℕ} → A → Vec A n → Vec A (suc n)

  data μ₁ (O : Set) (D : Desc O) : Set where
    init : ⟦ D ⟧₁ D → μ₁ O D
\end{code}

We can split a datatype declaration into 2 parts.
\begin{enumerate}
\item The \textit{signature}, containing the type former between
  \Key{data} and \Key{where} keywords.
\item The \textit{body}, containing the constructors after the
  \Key{where} keyword.
\end{enumerate}

The formation rules of kind \Data{Set} are defined by the
\textit{signature} part of datatype declarations, but the collection
of formation rules is \textit{open} to extension (i.e. whenever a new
type is declared).
In contrast, the formation rules of kind \Data{Desc} is defined by the
\textit{body} part of its datatype declaration, using the
\textit{closed} collection of constructors in the body.

\subsection{Types versus Descriptions}

In an open type theory like Agda, \Data{Set} is a unique kind because
it is \textit{not} inductively defined (i.e. it has an open collection
of formation rules, extended by type formers in the signature of
datatype declarations).
Every other kind (like \Data{Desc}) is defined by
a closed collection of formation rules (i.e. the constructors in the body
of the datatype declaration for the kind).

The open versus closed formation rules distinction between kinds
\Data{Set} and \Data{Desc}, and the difference in the way the
formation rules are defined by datatype declaration signatures or
bodies, is what made coming up with an adequate definition of a closed
universe difficult. In fact, we first defined (an admitted to) an
inadequate definition of a closed universe~\cite{diehl:gupdate}, where
certain algebraic types (like natural numbers) were (adequately) encoded
in the first universe, but others (like parameterized lists) needed to
be (inadequately) lifted to the second universe.

The solution to adequately defining a closed universe
(as in \refsec{closed}, following the procedure in \refsec{closing})
is to create codes for types (\Data{`Set}) \textit{mutually} with
codes for descriptions (\Data{`Desc}). At first, this may seem odd
because descriptions (\Data{Desc}) can already be viewed as codes
(whose interpretation function is the fixpoint operator \Data{μ₁}).
Hence, \Data{`Desc} can be viewed as a a code for codes. However, this
is necessary because \Data{Desc} codes are \textit{open descriptions},
while \Data{`Desc} codes are \textit{closed descriptions}.

Part of what led us to realizing that codes for closed types (\Data{`Set})
need to be defined mutually with codes for closed descriptions
(\Data{`Desc}), was viewing the ``constructors'' of kinds \Data{Set}
and \Data{Desc} in a unifying way as kind formers. Rather than
focusing on the syntactic difference that a type former (of
\Data{Set}) appears in the signature of a declaration,
and a large constructor (of \Data{Desc}) appears in the body of a
declaration, we can simply focus on the fact they are both formation
rules of some kind. For example, below we list formation rules for
kind \Data{Set} and kind \Data{Desc} in a unified way.

\begin{center}
 \begin{tabular}{||c | c ||} 
 \hline
 \Data{Set} : \Data{Set₁} &
 \Data{Desc} : (\Var{O} : \Data{Set}) → \Data{Set₁} \\ [0.5ex] 
 \hline\hline
 \Data{ℕ} : \Data{Set} &
 \Con{ι} : (\Var{o} : \Var{O}) → \Data{Desc} \Var{O} \\ 
 \hline
 \Data{Vec} : (\Var{A} : \Data{Set}) (\Var{n} : \Data{ℕ}) → \Data{Set} &
 \Con{σ} : (\Var{A} : \Data{Set}) (\Var{D} : \Var{A} → \Data{Desc} \Var{O}) → \Data{Desc} \Var{O} \\
 \hline
 \Data{μ₁} : (\Var{O} : \Data{Set}) (\Var{D} : \Data{Desc} \Var{O}) → \Data{Set} &
 \Con{δ} : (\Var{A} : \Data{Set}) (\Var{D} : (\Var{A} → \Var{O}) → \Data{Desc} \Var{O}) → \Data{Desc} \Var{O} \\ [1ex] 
 \hline
\end{tabular}
\end{center}

The first row contains the \textit{kind formers} \Data{Set} and \Data{Desc}.
Subsequent rows in the first column contain \textit{type formers},
serving a role analogous to large constructors, but for kind \Data{Set}.
Subsequent rows in the second column
contain the large constructors of kind \Data{Desc}. This unified way of
presenting \Data{Set} and \Data{Desc} leads us to refer to
large constructors of \Data{Desc} as \textit{description formers}.

%% The reason why \Data{List} is open, is because the type of the \Var{a}
%% argument of \Con{cons} is the parameter \Var{A}, and the kind of
%% \Var{A} is \Data{Set}. Recall (from \refsec{open}) that we defined
%% open types (or kinds) to be those that mention \Data{Set}.

\subsection{Kind-Parameterized Types}

In order to perform fully generic programming, our original goal
was to create a closed universe of \textit{types}. This universe
corresponds to the first universe in a hierarchy of universes
(we define the hierarchy in \refchap{hier}). For the first universe to
be adquate, it should contain all possible \textit{small values}.
In other words, \Data{`Set} should encode \textit{types}
like \Con{`Bool}, \Con{`Σ}, and \Con{`Vec}, whose elements are small values.
However, it should \textit{not} encode \textit{kinds} like
\Con{`Set} and \Con{`Desc}, whose elements would be large values.
Encoding large values in the first universe leads to inconsistency
due to a \textit{type in type} paradox~\cite{TODO}.

If \Con{`Desc} should \textit{not} be encoded in our
first universe, then why do we need to close over it when defining our
universe at all? The answer is that the \textit{kind} \Data{Desc}
appears as an argument to the \textit{type} former of \Data{μ₁}. This
is similar to how the \textit{kind} \Data{Set} appears as an argument
to the \textit{type} former of \Data{Vec}. However, this leads us to the
next question, why can a type like \Data{Vec} have kind-level type
former arguments while remaining a type (rather than being lifted to a
kind)? The answer has to do with both \Data{Vec} and \Data{μ₁} being
defined as \textit{parameterized} types.

\paragraph{Vectors}

Consider the type of vectors, parameterized by
elements of some type \Var{A}, and indexed by the natural numbers. 

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 private
\end{code}}

\begin{code}
  data Vec (A : Set) : ℕ → Set where
    nil : Vec A zero
    cons : {n : ℕ} → A → Vec A n → Vec A (suc n)
\end{code}

Vectors are \textit{types}, rather than \textit{kinds},
because the codomain of their type former is \Data{Set} (rather than
\Data{Set₁}). An algebraic datatype can consistently be classified as
a \textit{type} so long as its constructors do not contain a
type (\Data{Set}) as a formal argument. Datatype \textit{parameters}
give us a way to refer to \Var{A} in the vector constructors,
without actually taking \Var{A} as a formal argument in the
\textit{declaration} of each constructor.
Hence, the declarations of the \Con{nil} and \Con{cons} constructors do not
have an \Var{A} argument.
However, if we consider the types of the constructors
(rather than their declarations),
we see that \Var{A} appears as an informal argument to each
constructor. 

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 private
  data Vec : Set → ℕ → Set where
\end{code}}

\begin{code}
    nil : {A : Set} → Vec A zero
    cons : {A : Set} {n : ℕ} → A → Vec A n → Vec A (suc n)
\end{code}

Notice that the \Con{cons} constructor must take \Var{n} as a formal
argument, so that it may determine the index to be \Con{suc} \Var{n}.
We call \Var{A} an informal argument because the
underlying constructor declaration does not store \Var{A}.
It is exactly this fact, that the declaration of the
\Con{nil} and \Con{cons} constructors
do not formally store \Var{A} as an argument, that allows 
\Data{Vec} to be a type (\Data{Set}) rather than a kind (\Data{Set₁}).
To see the difference, we define vectors to be indexed by \Var{A},
rather than parameterized \Var{A}, below

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 private
\end{code}}

\begin{code}
  data Vec : (A : Set) → ℕ → Set where
    nil : {A : Set} → Vec A zero
    cons : {A : Set} {n : ℕ} → A → Vec A n → Vec A (suc n)
\end{code}

Above, the type former declares \Var{A} to be an index
because it appears to the right of the colon in the datatype
declaration signature (appearing to the left makes it a
parameter). Now the \Con{nil} and \Con{cons} constructors
must take \Var{A} as a
formal argument,
because it is no longer available as a parameter. Because \Var{A}
is a \textit{kind} (\Data{Set}), and it appears as formal
constructor arguments, the indexed vector type must be a kind (hence,
the codomain of its former is \Data{Set₁}).

\paragraph{Fixpoints}

Now let's reconsider the definition of the \textit{type} of fixpoints,
\textit{parameterized} by the decoding codomain \Var{O} and
the description \Var{D}. Below, we only present the definition of the
interpretation function (\Fun{⟦\_⟧₁}) and the
fixpoint datatype (\Data{μ₁}), but see \refsec{iralgmod} for the
full definition (including the decoding functions).

\AgdaHide{
\begin{code}
module _ where
 open import Function
 open import Data.Unit
 open import Data.Product
 private
  data Desc (O : Set) : Set₁ where
    ι : (o : O) → Desc O
    σ : (A : Set) (D : A → Desc O) → Desc O
    δ : (A : Set) (D : (A → O) → Desc O) → Desc O
  mutual
\end{code}}

\begin{code}
    ⟦_⟧₁ : {O : Set} (D R : Desc O) → Set
    ⟦ ι o ⟧₁ R = ⊤
    ⟦ σ A D ⟧₁ R = Σ A (λ a → ⟦ D a ⟧₁ R)
    ⟦ δ A D ⟧₁ R = Σ (A → μ₁ _ R) λ f → ⟦ D (μ₂ R ∘ f) ⟧₁ R
  
    data μ₁ (O : Set) (D : Desc O) : Set where
     init : ⟦ D ⟧₁ D → μ₁ O D
\end{code}

\AgdaHide{
\begin{code}
    ⟦_⟧₂ : {O : Set} (D R : Desc O) → ⟦ D ⟧₁ R → O
    ⟦ ι o ⟧₂ R tt = o
    ⟦ σ A D ⟧₂ R (a , xs) = ⟦ D a ⟧₂ R xs
    ⟦ δ A D ⟧₂ R (f , xs) = ⟦ D (λ a → μ₂ R (f a)) ⟧₂ R xs
    
    μ₂ : {O : Set} (D : Desc O) → μ₁ O D → O
    μ₂ D (init xs) = ⟦ D ⟧₂ D xs
\end{code}}

Both parameters (\Var{O} and \Var{D}) of the
fixpoint datatype (\Data{μ₁}) are kinds
(\Data{Set} and \Data{Desc}, respectively). Hence, \Data{μ₁} can be
a type (\Data{Set}), rather than a kind (\Data{Set₁}), because its
constructor (\Con{init}) does not contain any formal arguments that
are classified by kinds.
While the type parameter (\Var{O}) is used similarly to the type
parameter (\Var{A}) of vectors, the description parameter (\Var{D}) is
used in a significant way. The interpretation function (\Fun{⟦\_⟧₁})
is applied to the \Var{D} parameter to compute the \textit{type} of
the argument to \Con{init}. While \Fun{⟦\_⟧₁} takes a \textit{kind}
(\Var{D}) as an input, it returns a type as an output. Hence,
\Con{init} never actually store a description (i.e. a kind) as a
formal argument.

We discuss the significance of computing over a
\textit{large} (i.e. a \textit{kind}) parameter in a constructor
argument of a \textit{type} in \refchap{future}.
Importantly, the result is that fixpoints can be defined as a
\textit{type}, hence it can model algebraic datatypes as types, whose
inhabitants are (small) \textit{values}. It would be inadequate to
model algebraic datatypes (like natural numbers or vectors) at the
level of kinds, because users expect to declare them as types.

\paragraph{Heterogenous Lists}

We have learned that certain datatypes can be declared as types,
rather than kinds, by changing datatype indices to datatype
parameters. However, if a datatype is not indexed, then this change is
not applicable, and the type must be declared as a kind. For example,
consider the \textit{kind} of heterogenous lists (\Data{HList} below).

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\begin{code}
  data HList : Set₁ where
    nil : HList
    cons : {A : Set} → A → HList → HList
\end{code}

Because the \Con{cons} constructor of heterogenous lists takes \Var{A}
of kind \Data{Set} as a formal argument, there is no choice but to
make \Data{HList} a kind (\Data{Set₁}). We could imagine indexing
\Data{HList} by the collection of types it contains, and then using
our trick to turn the index into a parameter. However, this would not
adquately define heterogenous lists, because the types of elements would
be statically determined.
For similar reasons, the descriptions (\Data{Desc}) must be a kind,
rather than a type.

The first closed universe (of \refsec{closed}) cannot encode
kinds like \Data{Set}, \Data{Desc}, and \Data{HList}.
However, \refchap{hier} defines a hiearchy of universes, allowing
kinds to be represented in the next (i.e. second) universe
(i.e. the universe of closed kinds). Further levels of the universe
correspond to superkinds (\Data{Set₂}), and so on
(\Data{Set₃}, \Data{Set₄}, ... , \Data{Set$_\omega$}).
