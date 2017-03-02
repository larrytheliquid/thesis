\AgdaHide{
\begin{code}
module _ where
open import Data.Unit
open import Data.Sum
open import Data.Product
\end{code}}

\chapter{Open Non-Dependent Types}\label{sec:nondepalg}

In this section we review the algebraic semantics for
\textit{non-dependent} and potentially
\textit{inductive} (\refsec{ind}) types. Then, we show how to
\textit{model} algebraic semantics within type theory by converting abstract
mathematical constructs to concrete datatypes (analogous to how we model
the abstract notion of a universe as concrete code and meaning
function types in \refsec{umodel}).
\footnote{
  Here the words ``abstract'' and ``concrete'' have their general
  meanings, not the technical meanings we defined in
  \refsec{abscon}.
}

\section{Categorical Model}\label{sec:nondepalgsem}

The algebraic semantics for an inductive datatype is the
\textit{least fixed point} of a polynomial equation
represented as a \textit{pattern functor}
($F : \set \arr \set$).
The input of the pattern functor
(conventionally named $X$)
represents the inductive set being
defined, and its output must be a set formed by
\textit{polynomial} set
constructions. The polynomial set constructions are denoted
1, (+), ($\cdot$),
and $X$, and represent the
unit set, the sum of two sets, the product of two sets, and
inductive occurrences of the set.

\paragraph{Natural Numbers}

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

For example, consider the datatype declaration for the natural numbers.

\begin{code}
  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ
\end{code}

The algebraic semantics of the \AgdaData{ℕ} type is the following
fixpoint equation.
$$
\nat \triangleq \mu X.~1 + X
$$

The plus operator (+) represents a choice between constructors, and is
analogous to
the disjoint union type (\AgdaData{⊎}). Thus, above the left
subexpression ($1$) represents the \AgdaCon{zero} constructor and the
right subexpression ($X$) represents the \AgdaCon{suc}
constructor. A subexpression represents a constructor by representing
the types of arguments that it takes.

The \AgdaCon{zero} constructor is represented by
1 (analogous to the unit type \AgdaData{⊤}) because it lacks
arguments (or isomorphically, it has a single trivial argument).
The \AgdaCon{suc} constructor is represented by the
variable $X$, indicating that it takes an inductive
argument. This is because $\mu$ is binding $X$ so that it may be
used for inductive occurrences of \AgdaData{ℕ}.

The equation used above is
actually a shorthand for explicitly defining a pattern functor
$F : \set \arr \set$ and obtaining its least fixed point by applying
$\mu : (\set \arr \set) \arr \set$.

$$
F \triangleq \lambda X.~1 + X\\
$$
$$
\nat \triangleq \mu~F
$$

Consider the notation using $\mu$ as a binder to be a shorthand for
taking the fixpoint of an anonymous functor obtained by replacing the
binding with a $\lambda$.
$$\mu X.~1 + X \triangleq \mu~(\lambda X.~1 + X)$$

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\paragraph{Binary Trees}

As another example, consider the type of
binary trees (parameterized by \AgdaVar{A} and \AgdaVar{B}) containing
\AgdaVar{A}'s in node positions and \AgdaVar{B}'s in branch positions
(as presented in \refsec{wtypes}).

\begin{code}
  data Tree (A B : Set) : Set where
    leaf : A → Tree A B
    branch : Tree A B → B → Tree A B → Tree A B
\end{code}

The algebraic semantics of the \AgdaData{Tree} type is the following
fixpoint equation.
$$
\dfn{Tree} \lambda A.~ \lambda B.~ \mu X.~ A + X \cdot B \cdot X
$$

The \AgdaCon{leaf} constructor takes a single argument of type
\AgdaVar{A}, so the constructor is represented by $A$ (which is bound
by a $\lambda$). The \AgdaCon{branch} constructor has two inductive
arguments and a non-inductive argument of type \AgdaVar{B}. Thus, its inductive
arguments are represented by $X$ (bound by $\mu$) and its
non-inductive argument is represented by
$B$ (bound by another $\lambda$). The multiplication operator ($\cdot$)
represents multiple arguments of a constructor as a
conjunction, and is analogous to the pair type (\AgdaData{×}).

%% TODO maybe mention similarity to param universe ParStar
\section{Formal Model}\label{sec:nondepalgmod}

To take advantage of algebraic semantics within type theory, we must
\textit{model} its abstract notions using concrete datatypes and
functions. Recall that $\mu$ semantically defines a datatype by taking
the fixpoint (using $\mu$) of a pattern functor $F : \set \arr
\set$. It is called a \textit{pattern} functor because its ``pattern''
must be restricted to using the polynomial set constructions covered in
\refsec{nondepalgsem}.

Informally we can check that a functor is defined under these
restrictions, but in type theory we must formally capture these
restrictions. We model algebraic semantics in type theory by reifying
the \textit{pattern} fragment (enforcing restrictions)
of functors as a datatype (\AgdaData{Desc} below), the actual
pattern \textit{functor}
as a computational type family (\AgdaFun{⟦\_⟧} below),
and the \textit{fixpoint} operator as a datatype (\AgdaData{μ} below).

\paragraph{Descriptions}

The first part of our algebraic model is the type of descriptions
(\AgdaData{Desc}), a syntax for the \textit{pattern} fragment of functors.
A \AgdaData{Desc} is the syntactic reification of
the polynomial expression language that must be used for a functor to
qualify as a \textit{pattern} functor (i.e. a \AgdaData{Desc}
``describes'' a valid, or pattern, functor).
Rather than defining a pattern
\textit{functor} directly, we first \textit{represent} it as a \AgdaData{Desc} such
that any well typed description can be \textit{converted} into a functor
meeting all pattern restrictions.

Below, the \AgdaData{Desc} constructors
\AgdaCon{`1}, \AgdaCon{`X},
(\AgdaCon{`+}), and (\AgdaCon{`∙}) respectively reify a \textit{syntax} for
the 1, $X$, (+), and ($\cdot$) polynomial set constructions.
Of special note is the \AgdaCon{`κ} \textit{constant} constructor.
The \textit{constant} constructor reifies a syntax for injecting
\footnote{
  As is often the case with injections, its syntax is implicit
  (i.e. invisible) when defining pattern functors using polynomial set
  constructions.
  }
\textit{non-inductive} constructor arguments (such as \AgdaVar{A} in the
\AgdaCon{leaf} constructor of \AgdaData{Tree}). 

\AgdaHide{
\begin{code}
module Desc where
\end{code}}

\begin{code}
  data Desc : Set₁ where
    `1 `X : Desc
    _`+_  _`∙_ : Desc → Desc → Desc
    `κ : Set → Desc
\end{code}

For example, below is the description for the natural numbers
datatype.

\AgdaHide{
\begin{code}
module _ where
 open Desc
 private
\end{code}}

\begin{code}
  NatD : Desc
  NatD = `1 `+ `X
\end{code}

Finally, note that we establish another convention of ``quoting''
description constructors with a backtick (e.g. \AgdaCon{`X} for $X$).
This emphasizes that they are the syntactification of polynomial set
constructions. As we will see, quoting \AgdaData{Desc} constructors is
natural as they also act as codes of a universe (\refsec{TODO}).

\paragraph{Pattern Functors}

\AgdaHide{
\begin{code}
module El where
  open Desc
\end{code}}

The next part of our algebraic model is the reification of pattern functors
($F : \set \arr \set$) as \textit{type families} (\refsec{tfam})
with \AgdaData{Set} as their domain
(\AgdaFun{F} : \AgdaData{Set} \arr~\AgdaData{Set}).
Rather than defining \AgdaFun{F} directly, we define a
\textit{computational type family} (\refsec{compu})
to interpret
(\AgdaFun{⟦}\_\AgdaFun{⟧} : \AgdaData{Desc} \arr~\AgdaData{Set}
\arr~\AgdaData{Set})
the language of polynomial set constructions
(\AgdaData{Desc}) as a pattern functor.

\begin{code}
  ⟦_⟧ : Desc → Set → Set
  ⟦ `1 ⟧ X = ⊤
  ⟦ `X ⟧ X = X
  ⟦ A `+ B ⟧ X = ⟦ A ⟧ X ⊎ ⟦ B ⟧ X
  ⟦ A `∙ B ⟧ X = ⟦ A ⟧ X × ⟦ B ⟧ X
  ⟦ `κ A ⟧ X = A
\end{code}

By partially applying the interpretation function to
a description, we get a model of a \textit{pattern} functor
\AgdaFun{F} (rather than an arbitrary non-pattern functor).
$$
\forall \AgdaVar{D}.~  \AgdaFun{⟦}~\AgdaVar{D}~\AgdaFun{⟧} \triangleq \AgdaFun{F}
$$

For example, below we instantiate \AgdaVar{D} to be the description of
natural numbers (\AgdaFun{NatD}), and demonstrate the functor produced
by partially applying the interpretation function to \AgdaFun{NatD}.

\AgdaHide{
\begin{code}
module _ where
 open Desc
 open El
 open import Relation.Binary.PropositionalEquality
 private
  NatD : Desc
  NatD = `1 `+ `X
  _ :
\end{code}}

\begin{code}
   ⟦ NatD ⟧ ≡ (λ X → ⊤ ⊎ X)
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}

Recall that the input to the pattern functor
(\AgdaFun{F} : \AgdaData{Set} \arr~\AgdaData{Set})
represents the inductive occurrences of the datatype being modeled.
A sound model must rule out pattern functors representing
datatypes that are not consistent in type theory, such as
\textit{negative} datatypes like \AgdaData{Neg} of \refsec{inft}.
We could \textit{directly} define the functor for \AgdaData{Neg} to be
(\AgdaFun{F} \AgdaVar{X} = \AgdaVar{X} \arr~\AgdaVar{X}), modeling the
negative inductive occurrence of \AgdaData{Neg} in the argument to
\AgdaCon{neg} by using \AgdaVar{X} in the domain
of the function type.

Instead, we choose to define functors
\textit{indirectly} by partially applying a description
to the interpretation function (rather than defining functors
\textit{directly} like the one for \AgdaData{Neg} above).
In other words, the output \AgdaData{Set} of \AgdaFun{F} is
only composed of type theory equivalents of polynomial set
constructions. For example, the output \AgdaData{Set} may use
disjoint unions (\AgdaData{⊎}), modeling (+), by interpreting the
(\AgdaCon{`+}) description. It may not use other arbitrary
types lacking a polynomial set construction equivalent (because their
is no \AgdaData{Desc} for them), like functions ($\arr$)
with negative occurrences of \AgdaVar{X}.

Finally, note that it may appear that \AgdaCon{`κ} could be used to
inject many non-polynomial types. While this is true, it is not
problematic because the type (\AgdaVar{A}) that \AgdaCon{`κ} injects
must be \textit{non-inductive}. The non-inductivity of \AgdaVar{A} is
enforced because \AgdaVar{A} must be a type defined independently of
\AgdaVar{X} (i.e. the interpretation of \AgdaCon{`κ} does not, for
example, pass \AgdaVar{X} to \AgdaVar{A}).

\paragraph{Fixpoints}

The final part of our algebraic model is the reification of the least
fixed point operator ($\mu : (\set \arr \set) \arr \set$)
for pattern functors. We reify the
least fixed point operator (\AgdaData{μ} : \AgdaData{Desc} \arr~\AgdaData{Set})
as a datatype parameterized by a \textit{description},
rather than a pattern functor ($\set \arr \set$).

While algebraic semantics applies the least fixpoint
operator directly to a pattern functor ($\mu~F$), our model instead
applies it to a description (\AgdaData{μ} \AgdaVar{D}).
The pattern functor ($\set \arr \set$) argument of $\mu$ can
be derived by the model \AgdaData{μ} by partially applying the
interpretation function to the description argument
(\AgdaFun{⟦}~\AgdaVar{D}~\AgdaFun{⟧} : \AgdaData{Set} \arr~\AgdaData{Set}).
Below is the
datatype declaration for the fixpoint operator (\AgdaData{μ}), and
its constructor (\AgdaCon{init}) is declared shortly thereafter.

\AgdaHide{
\begin{code}
module Fix where
  open Desc
  open El
\end{code}}

\begin{code}
  data μ (D : Desc) : Set where
\end{code}

In algebraic semantics the initial algebra
($\anit$) is used to construct values of the fixpoint of a
functor $F$.
$$
\anit : F~(\mu~F) \arr \mu~F
$$

Applying $F$ to its least fixed fixpoint ($\mu~F$)
results in a type isomorphic to its fixpoint. In other words, the $\set$ (or
\AgdaData{Set} in the model case) resulting from $F~(\mu~F)$
represents the types of constructors (and the types of their arguments)
of $\mu~F$.
Therefore, we declare \AgdaData{μ} to have a single constructor named
\AgdaCon{init} (for \textit{initial algebra}) that models
$\anit$.

\begin{code}
    init : ⟦ D ⟧ (μ D) → μ D
\end{code}

Recall that we model the pattern functor ($F$) by partially
applying (\AgdaFun{⟦}~\AgdaVar{D}~\AgdaFun{⟧})
the interpretation function
to the description
of the pattern functor. Additionally, our model of the fixpoint operator
applies (\AgdaData{μ} \AgdaVar{D}) it to a description, rather
than a pattern functor directly. Therefore, the type of the argument
to \AgdaCon{init} represents the types of the constructors (and the
types of their arguments) for \AgdaData{μ} \AgdaVar{D}.

\AgdaHide{
\begin{code}
module _ where
 open Desc
 open El
 open Fix
 open import Relation.Binary.PropositionalEquality
 private
  NatD : Desc
  NatD = `1 `+ `X
\end{code}}

For example, we can define the type of natural numbers as follows.

\begin{code}
  ℕ : Set
  ℕ = μ NatD
\end{code}

Natural numbers are constructed by applying
\AgdaCon{init} to values of the following type.

\AgdaHide{
\begin{code}
  _ :
\end{code}}

\begin{code}
   ⟦ NatD ⟧ ℕ ≡ (⊤ ⊎ ℕ)
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}


%% TODO mention type check failure if El D were negative?

Finally, notice that descriptions and fixpoints
can also be
interpreted as a universe (i.e. the universe of open algebraic types)
by considering them to be
codes (\AgdaData{Desc} : \AgdaData{Set}) and a
meaning function (\AgdaData{μ} : \AgdaData{Desc} \arr~\AgdaData{Set})
respectfully.

\section{Examples}\label{sec:nondepalgtps}

Having modeled \textit{algebraic semantics} by reifying its concepts into
datatypes of type theory (i.e. our \textit{algebraic model}), we now
show how to encode specific types (both their type formers and values)
using our algebraic model.

\paragraph{Natural Numbers}

We have already seen how to encode the type of natural numbers as the
disjunction of the unit type and an inductive occurrence.

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
  NatD = `1 `+ `X

  ℕ : Set
  ℕ = μ NatD
\end{code}

Recall that the type of the argument to the \AgdaCon{init} constructor
represents a choice of which
constructor to use, and the types of the arguments for the chosen
constructor. For the natural numbers, this type specializes as follows.

\AgdaHide{
\begin{code}
  _ :
\end{code}}

\begin{code}
   ⟦ NatD ⟧ ℕ ≡ (⊤ ⊎ ℕ)
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}

To model the \AgdaCon{zero} constructor, we choose the left injection
of the disjoint union type (defined in \refsec{param}), and apply it
to the trivial unit constructor. 

\begin{code}
  zeroArgs : ⊤ ⊎ ℕ
  zeroArgs = inj₁ tt
\end{code}

To construct a value of type \AgdaData{μ}, rather than the meaning
function applied to its fixpoint, we must apply the the initial
algebra (\AgdaCon{init}). We leave out describing this
step explicitly in future exposition.

\begin{code}
  zero : ℕ
  zero = init zeroArgs
\end{code}

To model the \AgdaData{suc} constructor, we apply the right injection
of disjoint union to the previous natural number (\AgdaVar{n}), given
as a function argument.

\begin{code}
  suc : ℕ → ℕ
  suc n = init (inj₂ n)
\end{code}

There is no need to provide examples of using natural
numbers encoded using our algebraic model. Once we
define the type former and constructors according to their standard
interface (i.e. their standard type signatures), their usage is
indistinguishable from using type formers and constructors defined using
datatype declarations (rather than \AgdaData{μ}).

\begin{code}
  two : ℕ
  two = suc (suc zero)
\end{code}

The example above expands to the encoded term below, but by using the
standard interface of type formers and constructors we never need to
manually construct it.

\begin{code}
  two' : μ (`1 `+ `X)
  two' = init (inj₂ (init (inj₂ (init (inj₁ tt)))))
\end{code}

\AgdaHide{
\begin{code}
module _ where
 open Desc
 open El
 open Fix
 open import Relation.Binary.PropositionalEquality
 private
  NatD : Desc
  NatD = `1 `+ `X

  ℕ : Set
  ℕ = μ NatD
\end{code}}

Similarly, any function defined by pattern matching
can retain its standard appearance of pattern matching on declared
constructors by using \textit{pattern synonyms}. Pattern synonyms are
a notational feature of Agda that expands the left hand syntax to the
term on the right hand side. It has the special property that such
expandable text can be used in the pattern matching fragment of the
language. Thus, by defining pattern synonyms for
\AgdaCon{zero} and \AgdaCon{suc} to expand into their \AgdaCon{init}
encodings, we can write functions like \AgdaFun{plus} in a way that is
oblivious to the underlying encoding.

\begin{code}
  pattern zero = init (inj₁ tt)
  pattern suc n = init (inj₂ n)

  plus : ℕ → ℕ → ℕ
  plus zero m = m
  plus (suc n) m = suc (plus n m)
\end{code}

The addition function above expands to the version below, defined by
pattern matching on constructors of our encoding
(\AgdaCon{init} et al.). The encoding also
expands in the body of the function, such as the
\AgdaCon{suc}cessor case of the addition function.

\begin{code}
  plus' : μ (`1 `+ `X) → μ (`1 `+ `X) → μ (`1 `+ `X)
  plus' (init (inj₁ tt)) m = m
  plus' (init (inj₂ n)) m = init (inj₂ (plus' n m))
\end{code}

In future examples we omit examples of values and functions
defined over modeled types. As explained, once we have derived the
type former and constructors of a type using the primitives of our
algebraic model, using the types to define values and function
definitions is indistinguishable from using declared types thanks to
syntactic conveniences afforded by Agda.

\paragraph{Binary Trees}

The type of binary trees (\refsec{nondepalgsem})
is modeled by a function taking its
parameters (\AgdaVar{A} and \AgdaVar{B}), and returning the
description of the disjoint union of \AgdaVar{A} (encoding the
\AgdaCon{leaf} constructor),
and the triple (as 2 right-nested pairs)
consisting of two inductive
occurrences and \AgdaVar{B}
(encoding the \AgdaCon{branch} constructor).

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
  TreeD A B = `κ A `+ (`X `∙ (`κ B `∙ `X))

  Tree : Set → Set → Set
  Tree A B = μ (TreeD A B)
\end{code}

\AgdaHide{
\begin{code}
  _ : {A B : Set} →
\end{code}}

\begin{code}
   ⟦ TreeD A B ⟧ (Tree A B) ≡ (A ⊎ (Tree A B × (B × Tree A B)))
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}

To model the \AgdaCon{leaf} constructor, we apply the left disjoint
union injection to the function argument of type
\AgdaVar{A} (i.e. the node value for the leaf).

\begin{code}
  leaf : {A B : Set} → A → Tree A B
  leaf a = init (inj₁ a)
\end{code}

To model the \AgdaCon{branch} constructor, we apply the right disjoint
union injection to a triple (2 right-nested pairs). The triple consists of
the first inductive function argument (i.e. the left branch),
the function argument of
type \AgdaVar{B} (i.e. the node value for the branch), and the second
inductive function argument (i.e. the right branch).

\begin{code}
  branch : {A B : Set} → Tree A B → B → Tree A B → Tree A B
  branch t₁ b t₂ = init (inj₂ (t₁ , (b , t₂)))
\end{code}

\paragraph{$\lambda$-Calculus Terms}

We introduce the type of
\textit{untyped $\lambda$-calculus terms} (\AgdaData{Term}) as a final
and slightly more complex example
(i.e. modeling a type with more than 2 constructors). We also
define semantics for the untyped lambda calculus in subsequent
sections (using different datatype features), using
\AgdaData{Term} as a running example.
Below we declare the \AgdaData{Term} type, consisting of
variable references (\AgdaCon{var}), lambda abstractions
(\AgdaCon{lam}), and applications (\AgdaCon{app}). 

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

Our untyped lambda calculus terms use a deBruijn~\cite{TODO}
encoding for variables. A deBruijn-encoded term references variables
by a natural number index, where 0 refers to the variable bound by the
most recent $\lambda$ (and 1 refers to the next most recent, and so on). For
example, below is a high-level syntax for the
Church-encoded~\cite{TODO} numeral \textbf{one}, and its deBruijn-encoded
equivalent.

$$
\dfn{one} \lambda f.~ \lambda x.~ f~x \triangleq \lambda~ (\lambda~ 1~0)
$$

As a \AgdaData{Term}, we write the deBruijn-encoded numeral \textbf{one} as
follows. Note the applications of the variable constructor
(\AgdaCon{var}) to natural numbers (\AgdaData{ℕ}) to refer to
variables by their deBruijn index.
\footnote{
  Our \AgdaData{Term} type is not scope safe in the sense that their
  could be natural numbers that are out of bounds with respect to
  the number of \AgdaCon{lam} occurrences. We could index
  \AgdaData{Term} by the natural numbers to enforce scope safety, but
  this additional complexity only makes later examples (of the
  semantics for \AgdaData{Term}, already defined using indexed types)
  harder to read
  without introducing new concepts.
}

\begin{code}
  one : Term
  one = lam (lam (app (var 1) (var 0)))
\end{code}

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

To model \AgdaData{Term}, we describe the disjoint union of the
natural numbers (encoding \AgdaCon{var})
with the disjoint union of an
inductive occurrence (encoding \AgdaCon{lam})
and a pair of inductive occurrences (encoding \AgdaCon{app}). This
models 3 constructors using 2 right-nested
disjoint unions.

\begin{code}
  TermD : Desc
  TermD = `κ ℕ `+ (`X `+ (`X `∙ `X))

  Term : Set
  Term = μ TermD
\end{code}

\AgdaHide{
\begin{code}
  _ :
\end{code}}

\begin{code}
   ⟦ TermD ⟧ Term ≡ (ℕ ⊎ (Term ⊎ (Term × Term)))
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}

To model the \AgdaCon{var} constructor, we apply the left disjoint
union injection to the natural number argument.

\begin{code}
  var : ℕ → Term
  var n = init (inj₁ n)
\end{code}

To model the \AgdaCon{lam} constructor, we apply the left disjoint
union injection to: the right disjoint union injection applied to the
inductive argument.

\begin{code}
  lam : Term → Term
  lam b = init (inj₂ (inj₁ b))
\end{code}

To model the \AgdaCon{app} constructor, we apply the left disjoint
union injection to: another left disjoint union injection but applied
to a pair of inductive arguments.

\begin{code}
  app : Term → Term → Term
  app f a = init (inj₂ (inj₂ (f , a)))
\end{code}


