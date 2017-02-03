\AgdaHide{
\begin{code}
module _ where
open import Data.Bool
open import Data.Unit
open import Data.Sum
open import Data.Product
\end{code}}

\section{Dependent Types}

In this section we review the algebraic semantics for
\textit{dependent} types.
We extend our previous \textit{infinitary} and
\textit{non-dependent}
algebraic semantics (\refsec{infalgsem}),
and its model (\refsec{infalgsem}),
to support constructor argument types that depend on previous
constructor arguments.

\subsection{Algebraic Semantics}\label{sec:depalgsem}

Compared to \textit{non-dependent} types, the type signatures of
\textit{pattern functors} ($F : \set \arr \set$)
and
\textit{least fixed points}
($\mu : (\set \arr \set) \arr \set$)
remain unchanged in the setting of \textit{dependent} algebraic
semantics. However, we change the language of
\textit{polynomial set constructions} to be able to describe pattern
functors of types involving dependencies.

We mostly keep the syntax of the non-dependent polynomial set constsructions
1, (+), ($\cdot$), and $X$. However, the meaning of the product of two
sets ($\cdot$) is actually the \textit{dependent} product, and its
syntax is reminiscent of dependent functions except ($\cdot$) takes
the place of ($\arr$). Specifically, the syntax of a dependent product
uses type ascription (e.g. $(x : A) \cdot B~x$), while a non-dependent
product does not (e.g. $A \cdot B$).
For example, dependent product can be used to express the set of pairs of
natural numbers and finite sets (whose size is dependent on the
natural number first component of the pair).
$$
(n : \nat) \cdot \tp{Fin}~n
$$

While we continue to use the sum of two sets operator (+),
it can now be derived using \textit{dependent} ($\cdot$) rather than
be a primitive polynomial set construction.
The definition of (+) is derived as the dependent
product of a boolean (the 2-element set) and a choice of either subterm.
$$
(+) \triangleq \lambda A.~ \lambda B.~ (b : 2) \cdot
\stm{if}~b~\stm{then}~A~\stm{else}~B
$$


We impose an additional restrictions on pattern functors
(which are already restricted to only contain positive inductive
occurrences)
to always end in the unit set 1. That is, pattern functors must take
the form of a (possibly empty) sequence of products (of either
non-dependent or dependent arguments), ending in 1.
\footnote{
  Any set $A$ is isomorphic to $A \cdot 1$. This is analogous
  to any type \AgdaVar{A} being isomorphic to the pair type
  \AgdaVar{A} \AgdaData{×} \AgdaVar{⊤}, as the unit type only adds
  trivial (\AgdaCon{tt}) information.
  }
For example, below is the product of a dependent natural number, a
non-dependent infinitary occurrence, and 1.
$$
F \triangleq \lambda X.~
(n : \nat) \cdot X^{\tp{Fin}~n} \cdot 1
$$

In general, the pattern functor is a (possibly dependent) product of $n$ (possibly
0) sets, ending in a multiplication by the unit set 1. Each
of the $n$ sets (i.e. each $A_i$ below) may dependent on the values of
previous sets (i.e. each $x_i$ below). Additionally, each $A_i$ may
be non-inductive (not using $X$) or infinitary (using $X$).
$$
F \triangleq \lambda X.~
(x_0 : A_0) \cdot
(x_1 : A_1~x_0) \cdot
(x_2 : A_2~x_1~x_2) \cdot ...
\cdot (x_n : A_n ~ x_0 ~...~ x_{n-1}) \cdot 1
$$

The purpose of these additional constraints should \textit{not} be readily
apparent now. However, they allow us to extend
the algebraic semantics of dependent types to include
indices (\refsec{idxalg}) and
induction-recursion (\refsec{iralg})
in the future.

Finally, note that any use of sums (+) obeys our constraint
as long as the
left and right subterms obey the constraint.
This is because the derived definition of (+) expands to a product. 

$$
F \triangleq
(\lambda X.~ 1 + 1)
\triangleq
(b : 2) \cdot
\stm{if}~b~\stm{then}~1~\stm{else}~1
$$

\paragraph{Natural Numbers}

We reuse the infinitary definition of the natural numbers from
\refsec{infalgsem}.

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

Compared to the infinitary and non-dependent (\refsec{idxalg})
natural numbers fixpoint, the only difference in our dependent setting is
that the \AgdaCon{suc} constructor ends by multiplying by 1 (obeying
our constraint).
$$
\nat \triangleq \mu X.~1 + X^1 \cdot 1
$$

Technically, the (+) is just notation so the true fixpoint is the
expanded definition below.
$$
\nat \triangleq \mu X.~
(b : 2) \cdot
\stm{if}~b~\stm{then}~1~\stm{else}~X^1 \cdot 1
$$

\paragraph{Rose Trees}

We use the infinitary definition of finitely branching rose trees from
\refsec{inft}. In this definition of \AgdaData{Rose} the
list of branches argument is isomorphically expressed as
a natural number and an infinitary argument with a finite set
(whose size is equal to the natural number) as its domain.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open import Data.Fin
 private
\end{code}}

\begin{code}
  data Rose (A : Set) : Set where
    rose : A → (n : ℕ) (f : Fin n → Rose A) → Rose A
\end{code}

The algebraic semantics for infinitary rose trees must be defined in
terms of \textit{dependent} product, as the
finite set (\AgdaData{Fin}~\AgdaVar{n})
infinitary domain
is dependent on the natural number
(\AgdaVar{n}) argument.
$$
\dfn{Rose} \lambda A.~ \mu X.~
A \cdot (n : \nat) \cdot X^{\tp{Fin}~n} \cdot 1
$$


\subsection{Algebraic Model}\label{sec:depalgmod}

Our model of the algebraic semantics of least fixed points is
similar to previous versions. However, modeling
\textit{dependencies} in pattern functors requires significant
changes, especially changes to the structure of pattern functor
descriptions.

\paragraph{Descriptions}

Recall from \refsec{depalgsem} that we constrained dependent pattern
functors to be a sequence of products ending in 1. Recall also that
descriptions are the reification (or model) of the language used to
create legal pattern functors.
Hence, we change the type of descriptions to enforce that pattern
functors (representing definitions of datatypes) are sequences of
dependent pairs (\AgdaData{Σ}) ending in the unit type
(\AgdaData{⊤}).

Below, the \AgdaCon{`ι} constructor models the pattern of ending a
functor with the unit type. For now this is simply a renaming
of the former \AgdaCon{`1} constructor.
\footnote{
  However, in future extensions
  supporting indexed types (\refsec{idxalg}) and inductive-recursive
  types (\refsec{iralg})) \AgdaCon{`ι} gains additional arguments.
}
The \AgdaCon{`σ} constructor models a
\textit{dependent} (but non-infinitary) argument.
The \AgdaCon{`δ} constructor models an
\textit{infinitary} (but non-dependent) argument.
\footnote{
  At this point it does not make sense for an infinitary argument
  (\AgdaCon{`δ}) to be dependent.
  At the time a datatype is defined, no functions exist
  that could operate over it. Hence, inductive occurrences need not be
  dependent arguments because there is no way to use the type being
  defined yet. However, once we extend descriptions to model
  inductive-recursive types (\refsec{iralg})
  we will need to add a notion of dependency to \AgdaCon{`δ}.
  }
Thus, while the pattern functor of algebraic semantics uses
a single product ($\cdot$) for any
argument, our new description syntax distinguishes between
dependent (\AgdaCon{`σ}) and
infinitary non-dependent (\AgdaCon{`δ}) arguments. 

\AgdaHide{
\begin{code}
module Desc where
\end{code}}

\begin{code}
  data Desc : Set₁ where
    `ι : Desc
    `σ : (A : Set) (D : A → Desc) → Desc
    `δ : (A : Set) (D : Desc) → Desc
\end{code}

Hence, the non-dependent product (\AgdaCon{`∙}) of the non-dependent
description datatype (\refsec{infalgmod}) is replaced by the
(no longer infix) dependent pair \AgdaCon{`σ} and infinitary
non-dependent pair \AgdaCon{`δ}. As an example,
below (\AgdaFun{RoseD}) is the
description of
\AgdaData{Rose} trees.
\AgdaFun{RoseD} uses \AgdaCon{`σ} to request a dependent
\AgdaVar{A} argument (although the dependency \AgdaVar{a} is not
used), then uses \AgdaCon{`σ} to request a dependent
natural number argument (\AgdaVar{n}), then uses
\AgdaCon{`δ} to request a non-dependent but infinitary argument
(whose domain is \AgdaData{Fin} \AgdaVar{n}),
and finally ends with \AgdaCon{`ι}.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open import Data.Fin
 open Desc
 private
\end{code}}

\begin{code}
  RoseD : Set → Desc
  RoseD A = `σ A (λ a → `σ ℕ (λ n → `δ (Fin n) `ι))
\end{code}

When \AgdaCon{`σ} is used to request
an argument of type \AgdaVar{A}, the rest of the description \AgdaVar{D} may
depend on a value of \AgdaVar{A}. This is modeled by the infinitary
type of \AgdaVar{D}, namely \AgdaVar{A} \arr~\AgdaData{Desc}.
Notice that the first argument of (\AgdaCon{`∙}) is
a description (\AgdaData{Desc}), but the first argument of
\AgdaCon{`σ} is a type (\AgdaData{Set}). Imagine that
\AgdaVar{A} was a
description, and that \AgdaVar{D} could depend on a value of the inductive
type being defined
(as the argument to the infinitary domain of \AgdaVar{D}).
Then, our type of descriptions (\AgdaData{Desc})
would be \textit{negative} (and we could subsequently use it to
model pattern functors of negative types).
Hence, the first component of a dependent pair (\AgdaVar{A})
must be restricted to a type (guaranteed to be non-inductive)
so that the infinitary type \AgdaVar{D}
(representing subsequent arguments in the description) remains
\textit{positive}.

The infinitary pair constructor \AgdaCon{`δ} is like a specialized
combination of the former infinitary constructor \AgdaCon{`X\carot}
and the non-dependent product (or pair) constructor \AgdaCon{`∙}.
The \AgdaVar{A} argument represents the domain of the infinitary
function (like the argument to \AgdaCon{`X\carot}), and the
non-dependent \AgdaVar{D} argument represents the rest of the
description (which cannot depend on the inductive occurrence
because the inductive type has not been defined yet).

\AgdaHide{
\begin{code}
module _ where
 open import Data.Bool
 open Desc
 private
\end{code}}

We can use \AgdaCon{`σ} to derive (\AgdaCon{`+}) as a dependent pair
of a boolean and a choice of branches, similar to how we
derived sums (+)
from dependent products ($\cdot$) for
pattern functors (\refsec{depalgsem}).

\begin{code}
  _`+_ : Desc → Desc → Desc
  D `+ E = `σ Bool (λ b → if b then D else E)
\end{code}

Additionally, we can derive \AgdaCon{`κ} and \AgdaCon{`X\carot} using
\AgdaCon{`σ} and \AgdaCon{`δ} respectfully, then immediately ending
with \AgdaCon{`ι} (as these derived constructors do not require
additional arguments).

\begin{code}
  `κ : Set → Desc
  `κ A  = `σ A (λ a → `ι)

  `X^ : Set → Desc
  `X^ A  = `δ A `ι
\end{code}

Finally, we emphasize that (\AgdaCon{`∙}) \textit{cannot} be derived from
\AgdaCon{`σ} and \AgdaCon{`δ}. It is not clear whether the first
argument (a \AgdaData{Desc}) to (\AgdaCon{`∙}) contains an infinitary
(hence inductive) occurrence, so cannot decide whether to proceed
by using \AgdaCon{`σ} (disallowing inductiveness) or
\AgdaCon{`δ} (allowing inductiveness). Additionally, we would somehow
need to convert the first argument of (\AgdaCon{`∙}),
a \AgdaData{Desc}, to the first argument of \AgdaCon{`σ} or
\AgdaCon{`δ}, a \AgdaData{Set}.

\paragraph{Pattern Functors}

Now we define the interpretation function
(\AgdaFun{⟦\_⟧} : \AgdaData{Desc} \arr~\AgdaData{Set}
\arr~\AgdaData{Set}) that can be partially applied to descriptions of
dependent types to produce models
(\AgdaFun{F} : \AgdaData{Set} \arr~\AgdaData{Set})
of pattern functors
($F : \set \arr \set$)
for dependent types. The type signatures of these
constructions (\AgdaFun{⟦\_⟧} and \AgdaFun{F}) remains the same when
adding dependent arguments, but the implementations change
(because the constructors of \AgdaData{Desc} changed).

\AgdaHide{
\begin{code}
module El where
  open Desc
\end{code}}

\begin{code}
  ⟦_⟧ : Desc → Set → Set
  ⟦ `ι ⟧ X = ⊤
  ⟦ `σ A D ⟧ X = Σ A (λ a → ⟦ D a ⟧ X)
  ⟦ `δ A D ⟧ X = (A → X) × ⟦ D ⟧ X
\end{code}

We interpret the \AgdaCon{`ι} constructor as the unit type
(\AgdaData{⊤}).
We interpret the \AgdaCon{`σ} constructor as a
dependent pair (\AgdaData{Σ}) whose first component is an
\AgdaVar{A}, and whose second component is the interpretation of the
rest of the description (which \textit{may depend} on the first component).
We interpret the \AgdaCon{`δ} constructor as a
non-dependent pair (\AgdaData{×}) whose first component is an
infinitary function from \AgdaVar{A} to \AgdaVar{X} (representing
an inductive occurrence), and whose
second component is the interpretation of the
rest of the description (which \textit{may not depend} on the first
component).

Partially applying \AgdaFun{RoseD} (along with its parameter \AgdaVar{A})
to the interpretation function
results in the following pattern functor for rose trees.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open import Data.Fin
 open Desc
 open El
 open import Relation.Binary.PropositionalEquality
 private
  RoseD : Set → Desc
  RoseD A = `σ A (λ a → `σ ℕ (λ n → `δ (Fin n) `ι))
  _ : {A : Set} →
\end{code}}

\begin{code}
   ⟦ RoseD A ⟧ ≡ (λ X → Σ A (λ a → Σ ℕ (λ n → (Fin n → X) × ⊤)))
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}

Notice how the \AgdaVar{A} and natural number arguments are
interpreted using dependent pairs (\AgdaData{Σ}),
and how the infinitary argument is interpreted using a
non-dependent pair (\AgdaData{×}).

\paragraph{Fixpoints}

The model (\AgdaData{μ} : \AgdaData{Desc} \arr~\AgdaData{Set}) of
the algebraic semantics for least fixed points
($\mu : (\set \arr \set) \arr \set$) of \textit{dependent} types
is unchanged, as is the model (\AgdaCon{init}) of the initial
algebra ($\anit$).

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

As an example, below is the datatype of rose trees defined as a
fixpoint.

\AgdaHide{
\begin{code}
module _ where
 open Desc
 open El
 open Fix
 open import Data.Nat
 open import Data.Fin
 open import Relation.Binary.PropositionalEquality
 private
  RoseD : Set → Desc
  RoseD A = `σ A (λ a → `σ ℕ (λ n → `δ (Fin n) `ι))
\end{code}}

\begin{code}
  Rose : Set → Set
  Rose A = μ (RoseD A)
\end{code}

\AgdaHide{
\begin{code}
  _ : {A : Set} →
\end{code}}

\begin{code}
   ⟦ RoseD A ⟧ (Rose A) ≡ Σ A (λ a → Σ ℕ (λ n → (Fin n → Rose A) × ⊤))
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}


\subsection{Type Model}

Now we model the type formers and constructors of (possibly) dependent
datatypes. The descriptions of these datatypes are interpreted as
models of pattern functors constrained to be
sequences of dependent and non-dependent infinitary pairs, ending
in the unit type.

\paragraph{Rose Trees}

We begin by modeling rose trees, because they demonstrate
dependencies between argument types while also being simple because
they only have a single constructor. First, we repeat the definition
of the rose tree description, its pattern functor, and its type former
as a fixpoint.

\AgdaHide{
\begin{code}
module _ where
 open Desc
 open El
 open Fix
 open import Data.Nat
 open import Data.Fin
 open import Relation.Binary.PropositionalEquality
 private
\end{code}}

\begin{code}
  RoseD : Set → Desc
  RoseD A = `σ A (λ a → `σ ℕ (λ n → `δ (Fin n) `ι))

  Rose : Set → Set
  Rose A = μ (RoseD A)
\end{code}

\AgdaHide{
\begin{code}
  _ : {A : Set} →
\end{code}}

\begin{code}
   ⟦ RoseD A ⟧ (Rose A) ≡ Σ A (λ a → Σ ℕ (λ n → (Fin n → Rose A) × ⊤))
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}

Now we model the single constructor (\AgdaCon{rose}) of
\AgdaData{Rose} trees. Note that we are modeling the infinitary
rose constructor (\refsec{inft}),
rather than its \AgdaData{List} of roses variant, as
indicated by the type signature of our derived \AgdaCon{rose}
constructor. 

\begin{code}
  rose : {A : Set} (a : A) (n : ℕ) (f : Fin n → Rose A) → Rose A
  rose a n f = init (a , (n , (f , tt)))
\end{code}

Because our dependent types are modeled as least fixed points of
functors constrained to be sequences of pair types, values
(e.g. like the \AgdaCon{rose} constructor) are simply the
\AgdaCon{init}ial algebra of a tuple encoded as a sequence of
right-nested pairs (ending in the trivial unit value \AgdaCon{tt}).

\paragraph{Natural Numbers}

Let's encode a model of natural numbers using descriptions for
dependent types. We begin with the pattern functor for a dependent and
infinitary encoding of the natural numbers.
The \AgdaCon{zero} constructor immediately ends with \AgdaCon{`ι}.
The \AgdaCon{suc}
constructor uses \AgdaCon{`δ} to demand a trivial (i.e. where the
domain is the unit type) infinitary argument (similar to
\refsec{infalgtps}), then ends with \AgdaCon{`ι}.

\AgdaHide{
\begin{code}
module _ where
 open Desc
 open El
 open Fix
 private
  _`+_ : Desc → Desc → Desc
  D `+ E = `σ Bool (λ b → if b then D else E)
\end{code}}

\begin{code}
  NatD : Desc
  NatD = `ι `+ `δ ⊤ `ι
\end{code}

Recall from \refsec{depalgmod} that a choice of constructors
(\AgdaCon{`+}) is derived as a dependent pair with a boolean domain
and a choice between descriptions, so the \AgdaFun{NatD} above expands
to the version below.

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
  NatD = `σ Bool (λ b → if b then `ι else `δ ⊤ `ι)
\end{code}

For legibility (especially when types with many different constructors
are involved), we often create a specialized enumeration type in place
of the \AgdaData{Bool}, and define the second argument to \AgdaCon{`σ}
as a pattern matching $\lambda$ rather than an \AgdaFun{if}-like
elimination principle. For example, we can encode the description of
natural numbers by matching on ``tags'' of the enumeration type
\AgdaData{NatT}.

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
  data NatT : Set where
    zeroT sucT : NatT

  NatD : Desc
  NatD = `σ NatT λ where
    zeroT → `ι
    sucT → `δ ⊤ `ι
\end{code}

By convention, names of tags are suffixed with "\AgdaCon{T}". Tags are merely
enumerations and do not have arguments themselves. Rather, we match on
tags in descriptions to declare the descriptions of arguments for each
constructor (where each constructor is represented by a tag
case).

Now let's finish by modeling the type of natural numbers as a
fixpoint, and its constructors as initial algebras of that fixpoint.

\begin{code}
  ℕ : Set
  ℕ = μ NatD

  zero : ℕ
  zero = init (zeroT , tt)

  suc : ℕ → ℕ
  suc n = init (sucT , ((λ u → n) , tt))
\end{code}

Now we are encoding constructor choices as the initial algebra applied
to a dependent pairs whose domain is an enumeration of tags and
codomain is the description of arguments for each constructor
tag. Hence, the first component (e.g. \AgdaCon{zeroT} or
\AgdaCon{sucT}) in the tuple that the initial algebra
is applied to is always the tag name.


\paragraph{$\lambda$-Calculus Terms}

As a final example we model the untyped $\lambda$-calculus terms
introduced in \refsec{nondepalgtps} using descriptions of dependent
types. Compared to the model of natural numbers, no new concepts are
required to encode \AgdaData{Term}s.
The reason for this example is that \AgdaData{Term} has 3
constructors, so we can gain a greater appreciation of the legibility
afforded by constructor tags compared to choice-encoded using
boolans.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 private
\end{code}}

\begin{code}
  data Term : Set where
    var : (n : ℕ) → Term
    lam : (b : Term) → Term
    app : (f : Term) (a : Term) → Term
\end{code}

First, let's describe the 3 constructors as a right-nested tuple of 3
choices using (\AgdaCon{`+}).

\AgdaHide{
\begin{code}
module _ where
 open Desc
 open El
 open Fix
 open import Data.Nat
 private
  _`+_ : Desc → Desc → Desc
  D `+ E = `σ Bool (λ b → if b then D else E)
\end{code}}

\begin{code}
  TermD : Desc
  TermD = `σ ℕ (λ n → `ι) `+ (`δ ⊤ `ι `+ `δ Bool `ι)
\end{code}

Let's expand the definition of (\AgdaCon{`+}) to see the nested
choices.

\AgdaHide{
\begin{code}
module _ where
 open Desc
 open El
 open Fix
 open import Data.Nat
 open import Relation.Binary.PropositionalEquality
 private
\end{code}}

\begin{code}
  TermD : Desc
  TermD = `σ Bool λ b → if b
    then `σ ℕ (λ n → `ι)
    else `σ Bool λ b → if b
      then `δ ⊤ `ι
      else `δ Bool `ι
\end{code}

The \AgdaCon{var} constructor is is encoded in the \AgdaCon{true}
branch of the first choice, and the \AgdaCon{lam} and \AgdaCon{app}
constructors are encoded in a nested choice within the \AgdaCon{false}
branch. Below we model the type former and constructors of
\AgdaData{Term}.

\begin{code}
  Term : Set
  Term = μ TermD

  var : ℕ → Term
  var n = init (true , n , tt)

  lam : Term → Term
  lam b = init (false , true , (λ u → b) , tt)

  app : Term → Term → Term
  app f a = init (false , false , (λ b → if b then f else a) , tt)
\end{code}

Notice how the 2nd and 3rd constructors (\AgdaCon{lam} and
\AgdaCon{app}) are both defined as two nested choices, using
\AgdaCon{false} as the their first pair component, and then another
choice (\AgdaCon{true} and \AgdaCon{false} respectively) as their
second component. Additionally, we expose an inductive
(non-infinitary) model
of \AgdaCon{app} (having two non-infinitary \AgdaData{Term} arguments)
using an \AgdaFun{if} to branch on the infinitary
\AgdaData{Bool} domain (as we did for \AgdaData{Tree} in
\refsec{infalgtps}).

Below we repeat the entire \AgdaData{Term} model, but using
constructor tags instead of nested boolean choices.

\AgdaHide{
\begin{code}
module _ where
 open Desc
 open El
 open Fix
 open import Data.Nat
 open import Relation.Binary.PropositionalEquality
 private
\end{code}}

\begin{code}
  data TermT : Set where
    varT lamT appT : TermT

  TermD : Desc
  TermD = `σ TermT λ where
    varT → `σ ℕ (λ n → `ι)
    lamT → `δ ⊤ `ι
    appT → `δ Bool `ι

  Term : Set
  Term = μ TermD

  var : ℕ → Term
  var n = init (varT , n , tt)

  lam : Term → Term
  lam b = init (lamT , (λ u → b) , tt)

  app : Term → Term → Term
  app f a = init (appT , (λ b → if b then f else a) , tt)
\end{code}

Note how in the tagged construction the first componet of the pair is
always a single tag, hence \AgdaCon{lam} and \AgdaCon{app} are not
defined with nested choices.
