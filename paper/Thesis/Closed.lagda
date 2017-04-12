\AgdaHide{
\begin{code}
module _ where
open import Function
open import Appendix
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

We begin with a naive failing attempt at defining a closed type theory
using fixpoints (\refsec{naiveclosed}). After explaining why the
simple but naive attempt actually defines an open (rather than
closed) type theory, we explain how to properly close the theory
(\refsec{closed}). Then, we define a procedure to close any type
theory (\refsec{closing}), rather than just the universe we chose
for generic programming in this dissertation. Finally, we conclude
by comparing and contrasting types and kinds (\refsec{kinds}).

\section{Open Inductive-Recursive Types}\label{sec:naiveclosed}

In this section we present a naive failing attempt at creating a
\textit{closed} universe using fixpoints. It is a failing attempt
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
The fixpoint operator (\Data{μ₁})
also takes an explicit description argument (\Var{D}),
as before, where the kind of
inductive-recursive descriptions (\Data{Desc})
is defined in \refsec{iralgmod}.

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
 open Prim
 open Alg
 private 
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

Nothing immediately problematic stands out, as our
universe looks quite like the \textit{Closed Well-Order Types}
universe. Let's take a closer look at why the addition of the
identity type (\Con{`Id})
is not problematic, but the addition of fixpoints
(\Con{`μ₁}) is problematic, by constructing values of both.
First, we construct the (uninhabited) boolean proposition that true
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

Hence, the identity type (\Data{Id}) can be encoded in the universe
using its backtick equivalent (\Con{`Id}). Additionally,
its \textit{type} argument can be \Con{`Bool},
the backtick universe encoding of type \Data{Bool}.
Next (in \refsec{source}), we will see that while the fixpoint
type (\Data{μ₁}) can be encoded in the universe using its
backtick equivalent (\Con{`μ₁}), its \textit{description}
argument cannot be a backtick encoding of a \Data{Desc}
constructor, which is the source of openness of our universe.

\subsection{Source of Openness}\label{sec:source}

To discover why \Data{`Set} actually defines an \textit{open}
universe, let's try
to define the type of natural numbers in the universe
(i.e. as a member of \Data{`Set}).

\begin{code}
  NatDs : Bool → Desc ⊤
  NatDs true = ι tt
  NatDs false = δ ⊤ (λ u → ι tt)

  NatD : Desc ⊤
  NatD = σ Bool NatDs

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

Both of these consequences are a result of \Data{Desc} being a valid
model of algebraic datatype declarations in
an \textit{open} universe (where we can use any type, or \Data{Set},
of the Agda metalanguage to construct a \Data{Desc}),
but not in a \textit{closed} universe (where we need to restrict
\Data{Desc} to only be constructed from closed types,
or \Con{`Set}s).
We overcome these problems, by truly defning \Data{`Set} as a
\textit{closed} universe (in terms of a closed equivalent of descriptions,
named \Data{`Desc}), in the next section.


\section{Closed Inductive-Recursive Types}\label{sec:closed}

The key to creating an adequate\footnote{
  By \textit{adequate} we mean that values of algebraic types
  have intensionally unique canonical forms. This property is violated when
  values of algebraic types are encoded using well-orderings,
  as explained in \refsec{inad}. In contrast,
  encoding values of algebraic types using
  descriptions and fixpoints (like the examples in \refsec{iralgtps}) is adequate.
  }
closed universe of algebraic datatypes
in intensional type theory,
is paying attention not
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
  The ``type'' of types is actually a \textit{kind}
  because \Data{Set} : \Data{Set₁}. Similarly,
  the ``type'' of descriptions is actually a \textit{kind} because
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
 open Prim
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

\subsection{Examples}\label{sec:closedeg}

In \refsec{iralgtps} we demonstrated various examples of encoding
types and constructors using the universe of \textit{open}
inductive-recursive types (\refsec{iralgmod}). Now, we repeat these
examples in our \textit{closed} universe (\refsec{closed}).

Datatypes encoded with \textit{open descriptions} can use any
\textit{open type} (\Data{Set}) for the \Var{O} parameter of descriptions
(\Data{Desc}), and the \Var{A} argument of \Con{σ} and \Con{δ}. In
contrast, \textit{closed descriptions} (\Data{`Desc})
may only use \textit{closed types} (\Data{`Set})
for the \Var{O} parameter and \Var{A} argument.

\paragraph{Natural Numbers}

We will encode a closed version of the following trivially infinitary
and trivially inductive-recursive definition of the natural
numbers.

\AgdaHide{
\begin{code}
module _ where
 open Prim
 private
\end{code}}

\begin{code}
  data ℕ : Set where
    zero : ℕ
    suc : (⊤ → ℕ) → ℕ

  point : ℕ → ⊤
  point zero = tt
  point (suc f) = point (f tt)
\end{code}

Below, we encode the closed description of the natural
numbers. Compared to the description in \refsec{iralgtps}, the one
below uses the closed type \Con{`⊤} in the codomain of \Fun{NatDs} and
argument to \Con{`δ}, and uses the closed type \Con{`Bool} in the
argument to \Con{`σ}.

\AgdaHide{
\begin{code}
module Nat where
  open Prim
  open Alg
  open Closed
\end{code}}

\begin{code}
  NatDs : Bool → `Desc `⊤
  NatDs true = `ι tt
  NatDs false = `δ `⊤ (λ f → `ι (f tt))

  NatD : `Desc `⊤
  NatD = `σ `Bool NatDs
\end{code}

Below, we define the type former for natural numbers in two parts.
First, we define the \textit{code} for the closed type of natural
numbers, naming it \Fun{`ℕ} and having type \Data{`Set}. Second, we
define the interpretation of the closed code for the natural number
type into our open formal model, naming it \Fun{ℕ} and having kind
\Data{Set}. By convention, we prefix closed type formers with a
backtick to distinguish them from their interpretation in our open
formal model.

\begin{code}
  `ℕ : `Set
  `ℕ = `μ₁ `⊤ NatD

  ℕ : Set
  ℕ = ⟦ `ℕ ⟧
\end{code}

Defining the decoding function \Fun{point} for closed natural numbers
amounts to applying the decoding function component \Data{μ₂} (from
our open model of algebraic types in \refsec{iralgmod}) to an
\textit{open} description. Hence, we apply the
interpretation function (\Fun{⟪\_⟫}) to our closed description
(\Data{`Desc}) of natural numbers (\Fun{NatD}), translating it to the
open description (\Data{Desc}) expected by \Data{μ₂}.

\begin{code}
  point : ℕ → ⊤
  point = μ₂ ⟪ NatD ⟫
\end{code}

Defining the constructors for the natural numbers is no different from
the open version in \refsec{iralgtps}. While we encode the closed type
of natural numbers as \Fun{`ℕ}, we also interpret it as the open type
\Fun{ℕ} in our formal model. While we \textit{encode types} in
a closed way, we can \textit{use values} of the underlying open formal
model. That is why constructors (e.g. \Fun{zero} and \Fun{suc}, below)
appear no differently than in \refsec{iralgtps}.

\begin{code}
  zero : ℕ
  zero = init (true , tt)

  suc : ℕ → ℕ
  suc n = init (false , (λ u → n) , tt)
\end{code}

It is worth pointing out that creating named constructor tags, like
the \Data{NatT} below, is no longer possible in our closed universe. Instead,
a choice of constructors is encoded by applying \Con{`σ} to
\Con{`Bool}, in a derived-sum way. Creating named tags like \Data{NatT} requires
extending an \textit{open} theory with the new enumeration type, which
is not possible in a \textit{closed} theory.

\begin{code}
  data NatT : Set where
    zeroT sucT : NatT
\end{code}

\paragraph{Vectors}

Next, we will encode a closed version of the trivially infinitary and
non-trivially inductive-recursive vectors, using the translation from
indexed types to inductive-recursive types
described in \refsec{iralgtps}. We will encode a closed version of the
vector type below.

\AgdaHide{
\begin{code}
module _ where
 open Prim
 open import Data.Nat
 private
\end{code}}

\begin{code}
  mutual
    data Vec₁ (A : Set) : Set where
      nil : Vec₁ A
      cons : (n : ℕ) (a : A) (xs : Vec₁ A) (q : Id ℕ (Vec₂ xs) n) → Vec₁ A

    Vec₂ : {A : Set} → Vec₁ A → ℕ
    Vec₂ nil = zero
    Vec₂ (cons n x xs q) = suc n

  Vec : Set → ℕ → Set
  Vec A n = Σ (Vec₁ A) (λ xs → Id ℕ (Vec₂ xs) n)
\end{code}

\AgdaHide{
\begin{code}
module _ where
 open Nat
 open Prim
 open Alg
 open Closed
 private
\end{code}}

We get the closed description of vectors from the
open description in \refsec{iralgtps} by replacing every instance of
an open type with a closed type. For example, the decoding function
codomain is the natural numbers, as specified by applying the type of
closed descriptions (\Data{`Desc}) to the type of closed natural
numbers (i.e. \Fun{`ℕ}, which we just defined above).
Every first argument to \Con{`σ} and \Con{`δ} is a
closed type (i.e. one with a backtick). The \Var{A} parameter of
\Fun{VecDs} and \Fun{Vec} is also a closed type (\Data{`Set}).

\begin{code}
  VecDs : `Set → Bool → `Desc `ℕ
  VecDs A true = `ι zero
  VecDs A false =
    `σ `ℕ λ n →
    `σ A λ a →
    `δ `⊤ λ xs →
    `σ (`Id `ℕ (xs tt) n) λ q →
    `ι (suc n)

  VecD : `Set → `Desc `ℕ
  VecD A = `σ `Bool (VecDs A)
\end{code}

Next, we define the \textit{codes} for the closed
inductive-recursive vector type (\Fun{`Vec₁}), its decoding function
(\Fun{`Vec₂}), and the indexed vector type (\Fun{`Vec}). Again, this
mostly involves adding backticks to type arguments.

\begin{code}
  `Vec₁ : `Set → `Set
  `Vec₁ A = `μ₁ `ℕ (VecD A)
  
  `Vec₂ : (A : `Set) → ⟦ `Vec₁ A ⟧ → ℕ
  `Vec₂ A = μ₂ ⟪ VecD A ⟫
  
  `Vec : `Set → ℕ → `Set
  `Vec A n = `Σ (`Vec₁ A) (λ xs → `Id `ℕ (`Vec₂ A xs) n)
\end{code}

Above, the
``length'' decoding function (\Fun{`Vec₂}), and the closed indexed
vector type former (\Fun{`Vec}), take interpreted closed codes as
their second arguments. The former does this by applying
the type interpretation function (\Fun{⟦\_⟧}) to closed
inductive-recursive vectors codes (\Fun{`Vec₁}), while the latter
takes closed natural numbers (\Fun{ℕ}), which were also previously
defined by applying the type interpretation function (\Fun{⟦\_⟧}) to
closed natural number codes (\Fun{ℕ₁}).

Additionally, the body of the definition of the closed decoding
function (\Fun{`Vec₂}) must apply the open decoding function fixpoint
component (\Data{μ₂}) to an open description, which it obtains by
applying the description interpretation function (\Fun{⟪\_⟫}) to the
closed description defined by \Fun{VecD}.


Finally, we can define the formal model of closed indexed vectors and
their constructors.

\begin{code}
  Vec : `Set → ℕ → Set
  Vec A n = ⟦ `Vec A n ⟧

  nil : {A : `Set} → Vec A zero
  nil = init (true , tt) , refl
  
  cons : {A : `Set} {n : ℕ} (a : ⟦ A ⟧) (xs : Vec A n) → Vec A (suc n)
  cons {n = n} a (xs , refl) = init (false , n , a , (λ u → xs) , refl , tt) , refl
\end{code}

Above, the types of the vector type former and its
constructors are visually similar to the type \Key{data} declaration
(of \Data{Vec}) presented at the beginning. One key difference is that every open type
(\Data{Set}) is replaced by a closed type (\Data{`Set}). While the
natural number argument (\Fun{ℕ}) is defined as the
\textit{interpretation} of the natural numbers, the type argument
(\Data{`Set}) remains uninterpreted. Keeping the closed type
(\Data{`Set}) argument uninterpreted is the key to writing fully
generic functions (in \refchap{fullyg}), by pattern matching against
closed type codes (i.e. the constructors of \Data{`Set}).

\paragraph{Finite Sets}

Now we the type of finite sets (\Data{Fin})
as another example (in addition to \Data{Vec})
of modeling an open indexed type as an open
inductive-recursive type. First, review the high-level open indexed
type of finite sets.

\AgdaHide{
\begin{code}
module _ where
 open Prim
 open import Data.Nat
 private
\end{code}}

\begin{code}
  data Fin : ℕ → Set where
    here : (n : ℕ) → Fin (suc n)
    there : (n : ℕ) (i : Fin n) → Fin (suc n)
\end{code}

Using the same procedure to derive indexed vectors
from inductive-recursive vectors (in  \refsec{iralgtps}), we derive
indexed finite sets (\Data{Fin}) from the inductive-recursive type of
finite sets (\Data{Fin₁}) and its decoding function (\Data{Fin₂}). The
decoding function computes the index of the codomain of
each constructor, from its arguments.

\AgdaHide{
\begin{code}
module _ where
 open Prim
 open import Data.Nat
 private
\end{code}}

\begin{code}
  mutual
    data Fin₁ : Set where
      here : (n : ℕ) → Fin₁
      there : (n : ℕ) (i : Fin₁) (q : Id ℕ (Fin₂ i) n) → Fin₁

    Fin₂ : Fin₁ → ℕ
    Fin₂ (here n) = suc n
    Fin₂ (there n i q) = suc n

  Fin : ℕ → Set
  Fin n = Σ (Fin₁) (λ i → Id ℕ (Fin₂ i) n)
\end{code}

Converting the open type above to a closed description follows the
same rules that we followed to convert open vectors to a closed
description. The primary difference is that the description of closed
finite sets is not parameterized by a closed type \Var{A}, because the
type of finite sets is not parameterized.

\AgdaHide{
\begin{code}
module Fin where
  open Nat
  open Prim
  open Alg
  open Closed
\end{code}}

\begin{code}
  FinDs : Bool → `Desc `ℕ
  FinDs true = `σ `ℕ λ n → `ι (suc n)
  FinDs false =
    `σ `ℕ λ n →
    `δ `⊤ λ i →
    `σ (`Id `ℕ (i tt) n) λ q →
    `ι (suc n)

  FinD : `Desc `ℕ
  FinD = `σ `Bool FinDs
\end{code}

Finally, we define the closed type code components
(\Fun{`Fin₁}, \Fun{`Fin₂}, and \Fun{`Fin}) of finite sets. We also
define the type former (\Fun{Fin}) and its constructors (\Fun{here} and
\Fun{there}) by interpreting closed codes in our open model.

\begin{code}
  `Fin₁ : `Set
  `Fin₁ = `μ₁ `ℕ FinD
  
  `Fin₂ : ⟦ `Fin₁ ⟧ → ℕ
  `Fin₂ = μ₂ ⟪ FinD ⟫
  
  `Fin : ℕ → `Set
  `Fin n = `Σ `Fin₁ (λ i → `Id `ℕ (`Fin₂ i) n)

  Fin : ℕ → Set
  Fin n = ⟦ `Fin n ⟧

  here : {n : ℕ} → Fin (suc n)
  here {n} = init (true , n , tt) , refl
  
  there : {n : ℕ} (i : Fin n) → Fin (suc n)
  there {n} (i , refl) = init (false , n , (λ u → i) , refl , tt) , refl
\end{code}


Nothing new is required to understand the constructions above.
One minor change, compared to the \Key{data} declaration of indexed
finite sets earlier, is that we expose an \textit{implicit} natural
number (\Var{n}) argument in the \Fun{here} and \Fun{there}
constructors.

We presented the closed type of finite sets for two reasons. First, as
another example of an indexed (but not parameterized)
type derived from an inductive-recursive
type. Second, our next example is defining closed arithmetic
expressions (\Data{Arith}), which depends on closed finite sets as an
argument.

\paragraph{Arithmetic Expressions}

Now we will close the type of arithmetic expressions (\Data{Arith}),
an example of a non-trivially infinitary and non-trivially
inductive-recursive type. All previous examples were trivially
infinitary (\Data{ℕ}, \Data{Fin}, and \Data{Vec}). Additionally,
arithmetic expressions are ``naturally'' inductive-recursive,
whereas \Data{Vec} and \Data{Fin} are indexed types derived from
inductive-recursive encodings. First, review the high-level
declaration of arithmetic expressions.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open import Data.Fin
 private
  postulate prod : (n : ℕ) (f : Fin n → ℕ) → ℕ
\end{code}}

\begin{code}
  mutual
    data Arith : Set where
      Num : ℕ → Arith
      Prod : (a : Arith) (f : Fin (eval a) → Arith) → Arith
  
    eval : Arith → ℕ
    eval (Num n) = n
    eval (Prod a f) = prod (eval a) (λ a → eval (f a))
\end{code}

Below, we define the closed description of arithmetic expressions,
which is quite similar to its open description in \refsec{iralgtps}.
The interesting difference is that the second \Con{`δ} encodes the
infinitary domain of \Var{f} to be a \textit{closed} finite set
(\Fun{`Fin}). Hence, there is no issue defining closed
inductive-recursive types that use closed indexed types derived from
closed inductive-recursive types.

\AgdaHide{
\begin{code}
module _ where
 open Nat
 open Fin
 open Prim
 open Alg
 open Closed
 private
  postulate prod : (n : ℕ) (f : Fin n → ℕ) → ℕ
\end{code}}

\begin{code}
  ArithDs : Bool → `Desc `ℕ
  ArithDs true = `σ `ℕ λ n → `ι n
  ArithDs false =
    `δ `⊤ λ a →
    `δ (`Fin (a tt)) λ f →
    `ι (prod (a tt) f)

  ArithD : `Desc `ℕ
  ArithD = `σ `Bool ArithDs
\end{code}

Now we can define the closed type of (codes for) arithmetic
expressions (\Fun{`Arith}), and its decoding function (\Fun{eval}).

\begin{code}
  `Arith : `Set
  `Arith = `μ₁ `ℕ ArithD
  
  eval : ⟦ `Arith ⟧ → ℕ
  eval = μ₂ ⟪ ArithD ⟫
\end{code}

Finally, we define the type former (\Fun{Arith}) and its constructors (\Fun{Num} and
\Fun{Prod}) by interpreting closed codes in our open model.
In the definition of \Fun{Prod}, we expose a non-infinitary \Var{a}
argument (of type \Fun{Arith}), so its position in the \Con{init}
tuple of arguments is wrapped in a trivially infinitary function that
ignores its \Var{u} argument (of type unit). In contrast, the second
argument \Var{f} is naturally infinitary, hence no such wrapping is
necessary for \Var{f}, within \Con{init}.

\begin{code}
  Arith : Set
  Arith = ⟦ `Arith ⟧

  Num : ℕ → Arith
  Num n = init (true , n , tt)
  
  Prod : (a : Arith) (f : Fin (eval a) → Arith) → Arith
  Prod a f = init (false , (λ u → a) , f , tt)
\end{code}


\subsection{Kind-Generalized Universes}

Because we are claiming that we are formally modeling a closed
\textit{universe} (\refsec{universes}), we must be able to
inhabit the type of \textit{codes} and its
\textit{meaning} function. A universe (\Data{Univ}) can be
\textit{formally} modeled as a dependent record consisting of a \Field{Code} type, and
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

\subsection{Example Procedure Run}

Typically, we are interested
in closing over a universe of types, so our initial \Var{K} will be
the kind of open types (\Data{Set}), and its formation rules will
be some finite collection of \textit{type formers}
(e.g. \Data{Bool}, \Data{Id}, \Data{Σ}, \Data{μ₁}, etc.)
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
our failing attempt of a closed universe (\refsec{naiveclosed}),
because \Data{Desc} in argument \Var{D} of \Con{`μ₁} is not closed yet.

\paragraph{Step 3}

Next, we encounter of the kind of descriptions (\Data{Desc}) in the
\Var{D} argument of the \Con{`μ₁} constructor,
so we must recursively apply the
procedure by choosing \Var{J} to be \Data{Desc}.
For the next part of this this procedure run, we need to start over at
\textbf{Step 1} when recursively closing over the kind \Data{Desc}.
However, we will instead call this \textbf{Step 3.1}, where the
\textbf{3} prefix indicates that the recursion was initiated by
\textbf{Step 3} when closing over the kind \Data{Set}.
For reference,
we present the kind of descriptions (\Data{Desc}) below.

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
\textbf{Step 4.1} and \textbf{Step 4.2} can be completed by changing
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

\section{Types versus Kinds}\label{sec:kinds}

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
due to a \textit{type in type} paradox~\cite{girards,hurkens}.

If \Con{`Desc} should \textit{not} be encoded in our
first universe, then why do we need to close over it when defining our
universe at all? The answer is that the \textit{kind} \Data{Desc}
appears as an argument to the \textit{type} former of \Data{μ₁}. This
is similar to how the \textit{kind} \Data{Set} appears as an argument
to the \textit{type} former of \Data{Vec}. However, this leads us to the
next question, why can a type like \Data{Vec} have a kind-level type
former argument (i.e. its parameter \Var{A} of kind \Data{Set})
while remaining a type itself (rather than being lifted to a
kind)? The answer has to do with both \Data{Vec} and \Data{μ₁} being
defined as \textit{kind-parameterized} types.

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
kind (e.g. \Data{Set}) as a formal argument. Datatype \textit{parameters}
give us a way to refer to \Var{A} (of kind \Data{Set}) in the vector constructors,
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
do not formally store \Var{A} (of kind \Data{Set}) as an argument, that allows 
\Data{Vec} to be a type (\Data{Set}) rather than a kind (\Data{Set₁}).
To see the difference, we define vectors to be indexed by \Var{A},
rather than parameterized \Var{A}, below.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 private
\end{code}}

\begin{code}
  data Vec : (A : Set) → ℕ → Set₁ where
    nil : {A : Set} → Vec A zero
    cons : {A : Set} {n : ℕ} → A → Vec A n → Vec A (suc n)
\end{code}

The type former \Data{Vec} declares \Var{A} to be an index
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
\Con{init} never actually stores a description (i.e. a kind) as a
formal argument.

We discuss the significance of computing over a
\textit{large} (i.e. a \textit{kind}) parameter in a constructor
argument of a \textit{type} in \refchap{future}.
The consequence is that fixpoints can be defined as a
\textit{type}, hence they model algebraic datatypes as types, whose
inhabitants are (small) \textit{values}. It would be inadequate to
model algebraic datatypes (like natural numbers or vectors) at the
level of kinds, because users expect to declare them as types.
Siginficantly, by defining closed descriptions (\Data{`Desc}) mutually
with closed types (\Data{`Set}), we preserve the adequate encoding of
\Con{`μ₁} as a closed \textit{type}, allowing our formal model of
closed algebraic datatypes (like in \Fun{`ℕ} and \Fun{`Vec} in
\refsec{closedeg}) to adequately classify small values
(like \Fun{`zero} and \Fun{`nil}).

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
However, \refchap{hier} defines a closed hierarchy of universes, allowing
kinds to be represented in the next (i.e. second) universe
(i.e. the universe of closed kinds). Further levels of the universe
correspond to closed superkinds (\Data{Set₂}), and so on
(\Data{Set₃}, \Data{Set₄}, ... , \Data{Set$_\omega$}).

