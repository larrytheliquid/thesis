\AgdaHide{
\begin{code}
module _ where
open import Function
open import Data.Bool
open import Data.Unit
open import Data.Sum
open import Data.Product
\end{code}}

\section{Inductive-Recursive Types}\label{sec:iralg}

In this section we extend the algebraic semantics of
\textit{infinitary} and \textit{dependent} types
(\refsec{depalg})
to \textit{inductive-recursive} types
(\refsec{irtypes}). An inductive-recursive type is mutually defined
with a \textit{decoding} function that may be used in the inductive
definition of the type.

\subsection{Algebraic Semantics}\label{sec:iralgsem}

In all of the previous algebraic semantics we have worked with,
the pattern functors were \textit{endofunctors}
of the category of sets. That is, each functor
($F : \set \arr \set$)
mapped each set to another set.
Consequently, the fixpoint
($\mu : (\set \arr \set) \arr \set$)
of such a functor gave us back a set ($\mu~F : \set$).
Hence, previously each type could be semantically modeled as
a set ($\set$).

In order to model \textit{inductive-recursive} types, we need to model
a type ($X : \set$) along with its mutually defined
\textit{decoding} function ($d : X \arr O$), mapping values of the
type to values of some output type ($O : \set$). For example,
\refsec{irtypes} presents the type of arithmetic expressions
($X \triangleq~$\AgdaData{Arith}) mutually defined with a decoding function
($d \triangleq~$\AgdaFun{eval} : \AgdaData{Arith} \arr~ \AgdaData{ℕ})
that evaluates an
expression to its natural number ($O \triangleq~$\AgdaData{ℕ}) result.
Thus, algebraic semantics models inductive-recursive sets
as the dependent product of a set and its decoding function. Such a
dependent product is called a \textit{slice}, notated as
$\set/O$ (where $O$ is the output set).
$$
\set/O \triangleq (X : \set) \cdot (X \arr O)
$$

Pattern functors for inductive-recursive types are endofunctors
($F : \set/O \arr \set/O$)
of the slice category $\set/O$
\footnote{
  Objects of the slice category $\set/O$ are functions
  $f : X \arr O$ (where $X$ is some object-specific set
  and $O$ is a set fixed for the category). Its morphisms are
  functions $h : X \arr Y$ between objects
  $f : X \arr O$ and $g : Y \arr O$ such that
  $f = g \circ h$.
  
},
and the fixpoint
($\mu : (\set/O \arr \set/O) \arr \set/O$)
of such a pattern functor returns a slice
($\mu F : \set/O$).
It is convenient to separate the definition of $F$ into 2 parts, where
we denote the part by a subscript (i.e. $F_1$ and $F_2$).
$$
F_1 : \set/O \arr \set
$$
$$
F_2 : (R : \set/O) \arr F_1~R \arr O
$$

The first part ($F_1$) maps a slice to a
set (modeling a \textit{type}), similar to the functors
of previous sections. The second part ($F_2$) maps a slice and a
member of the set mapped by $F_1$, to a member of
$O$ (modeling a \textit{decoding} function).
By convention we use the letter $R$ to refer to the \textit{slice}
argument to distinguish it from the contained set $X$ and decoding
function $d$.
We can use put these two components of the functor together as a
dependent pair
to form the actual endofunctor over slices.
$$
F : \set/O \arr \set/O ~\triangleq~ \lambda R.~ (F_1~R ,~ F_2~R)
$$

We can separate the definition of least fixed points to similarly be
defined in terms of a fixed point operator ($\mu_1$, returning a set),
and its decoding function ($\mu_2$, taking an $\mu_1~F$ and returning
an $O$).
$$
\mu_1 : (\set/O \arr \set/O) \arr \set
$$
$$
\mu_2 : (F : \set/O \arr \set/O) \arr \mu_1~F \arr O
$$
$$
\mu : (\set/O \arr \set/O) \arr \set/O ~\triangleq~
\lambda F.~ (\mu_1~F ,~ \mu_2~F)
$$

Recall our restriction of pattern functors as a sequence of dependent
products of non-inductive or infinitary arguments, terminating in 1.
$$
F_1 \triangleq \lambda (X, d).~
(x_0 : A_0) \cdot
(x_1 : A_1~x_0) \cdot
(x_2 : A_2~x_1~x_2) \cdot ...
\cdot (x_n : A_n ~ x_0 ~...~ x_{n-1}) \cdot 1
$$

Before, it only make sense for non-inductive arguments to be
dependent. For example, we could have a functor like the following
(where $A : \set$ and $B : A \arr \set$).
$$
F_1 \triangleq \lambda (X, d).~ (x_1 : A) \cdot (x_2 : B~a) \cdot 1
$$

With the introduction of inductive-recursive types, it is now actually
possible to use an inductive dependent argument by applying the
decoding function ($d$). For example, now we can have a functor like
the following (where $A : \set$ and $B : O \arr \set$).
$$
F_1 \triangleq \lambda (X, d).~ (x_1 : X) \cdot (x_2 : B~(d~x_1)) \cdot 1
$$

Any decoder ($F_2$) of $F_1$ has a tuple of arguments
similar to the dependencies in the sequence of products defined
in $F_1$ (the only difference is that the tuple ends in the unit
argument $\bullet$, corresponding to the unit set 1 that
terminates the product).
For example, below the arguments $x_1$
and $x_2$ in $F_2$ correspond to the dependencies $x_1$ and $x_2$ in
$F_1$ (where $f : (x : X) \arr B~(d~x) \arr O$).
$$
F_2 \triangleq \lambda (X, d).~
\lambda (x_1, x_2, \bullet).~ f~x_1~x_2
$$


Now we finally introduce a new notation that takes advantage of our
structure of pattern functors as a sequence of dependent products
terminating in 1. The new notation gives us a succinct way to
simultaneously define the $F_1$ and $F_2$ parts of the pattern functor
$F$ by exploiting the shared structure between the dependencies in
$F_1$ and arguments in $F_2$. Now we define $F$ by terminating the
sequence of products with $\iota$ (replacing 1) applied to an element
of $O$. Because $\iota$ appears at the end of the sequence, it can be
defined with access to all of the dependencies of the product that
came before it. For example, below we define $F$ directly
(where $f : (x : X) \arr B~(d~x) \arr O$).
$$
F \triangleq
\lambda (X, d).~ (x_1 : X)
\cdot (x_2 : B~(d~x_1))
\cdot \iota~(f~x_1~x_2)
$$

Once again, this is merely notation for directly defining $F$ as a
dependent pair (a member of the slice $\set/O$). Hence, $\iota$ is
also just notation rather than being a primitive set construction.
For example, the notation above expands to the $F$ below.
$$
F ~\triangleq~
\lambda R.~ (F_1~R ,~ F_2~R) ~\triangleq~
\lambda (X, d).~ ((x_1 : X)
\cdot (x_2 : B~(d~x_1)
\cdot 1 ,~ \lambda (x_1, x_2, \bullet).~ f~x_1~x_2))
$$

In general, our new notation for inductive-recursive pattern functors
is a sequence of dependent
products of non-inductive or infinitary arguments,
terminating in $\iota$ applied to an element of $O$,
with dependencies $x_0$ through $x_n$ in scope
(where $n$ is the number of products).
$$
F \triangleq \lambda (X, d).~
(x_0 : A_0) \cdot
(x_1 : A_1~x_0) \cdot ...
\cdot (x_n : A_n ~ x_0 ~...~ x_{n-1}) \cdot
\iota ~(f ~ x_0 ~...~ x_{n})
$$

\paragraph{Natural Numbers}

Any ordinary inductive type can instead be modeled as a trivial
inductive-recursive type by combining the inductive type with a
trivial decoding function from its values to unit.
The inductive type can thus be defined as normally, without referring
to its trivial function.
For example, below we define the
type of natural numbers along with the trivial function
(\AgdaFun{point}) from natural numbers to unit.

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\begin{code}
  data ℕ : Set where
    zero : ℕ
    suc : (⊤ → ℕ) → ℕ

  point : ℕ → ⊤
  point _ = tt
\end{code}

Borrowing from our previous subscript notation for functors and
fixpoints, we can rename the inductive definition of
\AgdaData{ℕ} to \AgdaData{ℕ₁} and its trivial decoding function
\AgdaFun{point} to \AgdaFun{ℕ₂}. Then we can isomorphically model the
natural numbers as an inductive-recursive type by combining the type
and its decoding function using a pair.

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\begin{code}
  data ℕ₁ : Set where
    zero : ℕ₁
    suc : (⊤ → ℕ₁) → ℕ₁

  ℕ₂ : ℕ₁ → ⊤
  ℕ₂ n = tt

  ℕ : Σ Set (λ A → A → ⊤)
  ℕ = ℕ₁ , ℕ₂
\end{code}

First we define the algebraic semantics for this trivially
inductive-recursive type using the componentized definition of $\mu$
in terms of its set ($\mu_1$) and decoding function ($\mu_2$). Below,
1 (similar to \AgdaData{⊤})
is the name of the unit set and $\bullet$ (similar to \AgdaCon{tt})
is the name of its single inhabitant.
$$
\nat_1 \triangleq \mu_1 (X , d).~ 1 + X^1 \cdot 1
$$
$$
\nat_2 \triangleq \mu_2 (X , d).~ \lambda n.~ \bullet
$$
$$
\nat \triangleq \mu R.~ (\mu_1~R , ~\mu_2~R)
$$

Alternatively, we can define $\nat$ directly as a dependent pair where
we inline the definition of $\nat_1$ into the first component, and
inline the definition of $\nat_2$ into the second component.
$$
\nat \triangleq \mu (X, d).~ ((1 + X^1 \cdot 1), (\lambda n.~ \bullet))
$$

Finally, we can define it most succinctly with our $\iota$ notation as
follows. 
$$
\nat \triangleq \mu (X, d).~ \iota \bullet + X^1 \cdot \iota~\bullet
$$

Note that because $\iota~\bullet$ appears twice, once on either side of (+),
technically the $\iota$-based $\nat$ models the decoding function
\AgdaFun{ℕ₂} below that 
matches against \AgdaCon{zero} and \AgdaCon{suc} but returns
\AgdaCon{tt} in either case.

\AgdaHide{
\begin{code}
module _ where
 private
  data ℕ₁ : Set where
    zero : ℕ₁
    suc : (⊤ → ℕ₁) → ℕ₁
\end{code}}

\begin{code}
  ℕ₂ : ℕ₁ → ⊤
  ℕ₂ zero = tt
  ℕ₂ (suc f) = tt
\end{code}

As a final example, consider a pattern functor of the natural numbers
that takes advantage of the decoding function ($d$ below)
and dependency on an infinitary argument ($f$ below).
$$
\nat \triangleq \mu (X, d).~ \iota \bullet + (f : X^1) \cdot
\iota~(d~(f~\bullet))
$$

Above the result of appliyng the decoding function to a successor of a
natural number is specified
to be a \textit{recursive call} of the decoding function $d$ applied to:
the infinitary predecessor $f$
applied to the unit value $\bullet$. Hence, the pattern above is the
algebraic semantics for the decoding function below
(notice the recursive call of decoding function
\AgdaFun{ℕ₂} in the \AgdaCon{suc} case).

\AgdaHide{
\begin{code}
module _ where
 private
  data ℕ₁ : Set where
    zero : ℕ₁
    suc : (⊤ → ℕ₁) → ℕ₁
\end{code}}

\begin{code}
  ℕ₂ : ℕ₁ → ⊤
  ℕ₂ zero = tt
  ℕ₂ (suc f) = ℕ₂ (f tt)
\end{code}

Now we understand the essence of \textit{induction-recursion}:
While the $X$ parameter of the fixpoint operator $\mu$
allows us to construct \textit{inductive} arguments,
the $d$ parameter allows us to perform
\textit{recursive} calls of the decoding function. 


\subsection{Algebraic Model}\label{sec:iralgmod}

In this section we extend the model of algebraic semantics of
dependent types (\refsec{depalgmod}) to support inductive-recursive
types. The previous description type (\AgdaData{Desc}), interpretation
function (\AgdaFun{⟦\_⟧}) and least fixed point operator \AgdaData{μ}
are all modfied to be parameterized over an output type
(\AgdaVar{O} : \AgdaData{Set}), the codomain of the decoding function.

\paragraph{Descriptions}

Descriptions (of \refsec{depalgmod}) must be modified to be
parameterized over an output type \AgdaVar{O}.
Recall that descriptions are the syntactic reification of legal
pattern functors. In \refsec{iralgsem} we presented 3 different ways
to define pattern functors for inductive-recursive types.
\begin{enumerate}
  \item Single pattern functors ($F$) as a dependent pair.
  \item Two-part pattern functors ($F_1$ and $F_2$).
  \item Single pattern functors ($F$) using $\iota$.
\end{enumerate}

Our descriptions model the syntax of the 3rd ($\iota$) version of
legal pattern functors. Recall that $\iota$ is applied to an $O$,
hence we had an argument \AgdaVar{o} of type
\AgdaVar{O} to the
\AgdaCon{`ι} constructor. However, we also change \AgdaCon{`δ} in
a more subtle way.

\AgdaHide{
\begin{code}
module De where
\end{code}}

\begin{code}
  data Desc (O : Set) : Set₁ where
    `ι : (o : O) → Desc O
    `σ : (A : Set) (D : A → Desc O) → Desc O
    `δ : (A : Set) (D : (A → O) → Desc O) → Desc O
\end{code}

Recall that \AgdaCon{`σ} denotes a dependent
\textit{non-inductive} argument (of type \AgdaVar{A})
that subsequent arguments may depend on in \AgdaVar{D}.
With inductive-recursion, \AgdaCon{`δ} denotes an
infinitary (hence \textit{inductive}) argument
(whose domain is \AgdaVar{A}) that subsequent arguments may depend on in
\AgdaVar{D}. However, subsequent arguments in \AgdaVar{D} do not
depend directly on an infinitary argument
(i.e. \AgdaVar{A} \arr~\AgdaVar{X}). Instead, \AgdaVar{D} depends on
a function (i.e. \AgdaVar{A} \arr~\AgdaVar{O}) that is an implicit
\textit{composition} of the decoding function and the infinitary function.
This implicit composition hides the underlying infinitary argument,
preventing an inductive argument (\AgdaVar{X}) from
appearing negatively in the domain of the infinitary argument
\AgdaVar{D} (instead, \AgdaVar{O} appears).
Below is an example of the natural numbers encoded as a
trivial (i.e. where the codomain of the decoding function
\AgdaVar{O} is the unit type \AgdaData{⊤})
inductive-recursive description.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Unit
 open import Data.Bool
 open De
 private
\end{code}}

\begin{code}
  NatD : Desc ⊤
  NatD = `σ Bool (λ b → if b then `ι tt else `δ ⊤ (λ f → `ι (f tt)))
\end{code}

In the example above \AgdaCon{`ι} \AgdaCon{tt} is returned in the
\AgdaCon{zero} branch. The \AgdaCon{suc} branch returns
the result of applying the composition (\AgdaVar{f}) of the decoding function
and the infinitary function to \AgdaCon{tt}. This describes
the definition of natural numbers below.

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\begin{code}
  data ℕ₁ : Set where
    zero : ℕ₁
    suc : (⊤ → ℕ₁) → ℕ₁

  ℕ₂ : ℕ₁ → ⊤
  ℕ₂ zero = tt
  ℕ₂ (suc n) = ℕ₂ (n tt)

  ℕ : Σ Set (λ A → A → ⊤)
  ℕ = ℕ₁ , ℕ₂
\end{code}

To understand where the implicit composition of the decoding
function and the infinitary function is happening,
recognize that in successor case of
the definitions of \AgdaFun{NatD} and \AgdaFun{ℕ₂} above,
\AgdaVar{f} $=$ \AgdaFun{ℕ₂} \AgdaFun{∘} \AgdaVar{n}.


\paragraph{Pattern Functors}

Now we turn to the task of modeling pattern functors
($F : \set/O \arr \set/O$) of
inductive-recursive sets in type theory.
Before we can even consider doing so, we must model the
concept of a slice $\set/O$.
A slice is modeled as a dependent pair
type (\AgdaData{Σ})
parameterized by an output type (\AgdaVar{O}).
The first component of the pair is a type and the second
component is its decoding function.

\begin{code}
Set/ : Set → Set₁
Set/ O = Σ Set (λ A → (A → O))
\end{code}

We model pattern functors
($F : \set/O \arr \set/O$) as the functor
(\AgdaFun{F} : \AgdaFun{Set/} \AgdaVar{O} \arr~\AgdaFun{Set/} \AgdaVar{O})
resulting from the partial application of a description
to the interpretation function
(\AgdaFun{⟦\_⟧} : \{\AgdaVar{O} : \AgdaData{Set}\}
\arr~\AgdaData{Desc} \AgdaVar{O} \arr~\AgdaFun{Set/} \AgdaVar{O} \arr~\AgdaFun{Set/} \AgdaVar{O}).
In \refsec{iralgsem}
we showed how to define $F$ in terms of a component mapping slices to sets
($F_1$) and a component mapping slices to a decoding function ($F_2$). Our
type theoretic model similarly defines the interpretation function
(\AgdaFun{⟦\_⟧}) in terms of a type component (\AgdaFun{⟦\_⟧₁})
and a decoding function component (\AgdaFun{⟦\_⟧₂}),
which also result in the pattern functor components
(\AgdaFun{F₁} and \AgdaFun{F₂}) when partially applied to a description.

\AgdaHide{
\begin{code}
module _ where
 open De
 private
  postulate
   ⟦_⟧₁ : {O : Set} (D : Desc O) (R : Set/ O) → Set
   ⟦_⟧₂ : {O : Set} (D : Desc O) (R : Set/ O) (xs : ⟦ D ⟧₁ R) → O
\end{code}}

\begin{code}
  ⟦_⟧ : {O : Set} → Desc O → Set/ O → Set/ O
  ⟦ D ⟧ R = ⟦ D ⟧₁ R , ⟦ D ⟧₂ R
\end{code}

\AgdaHide{
\begin{code}
module El1 where
  open De
\end{code}}

First consider the interpretation function component (\AgdaFun{⟦\_⟧₁})
mapping slices to types. The \AgdaCon{`ι} and \AgdaCon{`σ} cases are
much like they were for the interpretation function of dependent types
in \refsec{depalgmod}.

\begin{code}
  ⟦_⟧₁ : {O : Set} → Desc O → Set/ O → Set
  ⟦ `ι o ⟧₁ R = ⊤
  ⟦ `σ A D ⟧₁ R = Σ A (λ a → ⟦ D a ⟧₁ R)
  ⟦ `δ A D ⟧₁ R@(X , d) = Σ (A → X) λ f → ⟦ D (d ∘ f) ⟧₁ R
\end{code}

The infinitary \AgdaCon{`δ} case now needs to be interpreted as a
\textit{dependent} pair type. The left component of the pair is the
infinitary argument
(\AgdaVar{f} : \AgdaVar{A} \arr~\AgdaVar{X}).
The right component is the interpretation of the description
\AgdaVar{D} applied to the \textit{composition} of the decoding
function (\AgdaVar{d}) and the \textit{dependent}
infinitary argument (\AgdaVar{f}).
Thus the subsequent argument types contained in \AgdaVar{D} can
depend on the the composed function (returning an \AgdaVar{O}), but
cannot directly depend the infinitary function
(returning an inductive \AgdaVar{X}).

Before providing an example, we redefine the description of natural
numbers by extracting the ``if-statement'' component into a separate
definition. This separate definition (\AgdaFun{NatDs}) returns the
description of a particular constructor when applied to the
appropriate boolean branch.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Unit
 open import Data.Bool
 open import Relation.Binary.PropositionalEquality
 open De
 open El1
 private
\end{code}}

\begin{code}
  NatDs : Bool → Desc ⊤
  NatDs b = if b then `ι tt else `δ ⊤ (λ f → `ι (f tt))

  NatD : Desc ⊤
  NatD = `σ Bool NatDs
\end{code}

\AgdaHide{
\begin{code}
  _ :
\end{code}}

To keep the example simple, we look at the result of applying the type
component of the interpretation function to the description of the
successor constructor (rather than the entire natural numbers
description).

\begin{code}
   ⟦ NatDs false ⟧₁ ≡ λ { (X , d) → Σ (⊤ → X) (λ f → ⊤) }
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}

The left component of the pair type is the infinitary argument of
\AgdaCon{suc}. The right component is just the unit type that
terminates every sequence of dependent arguments,
ignoring \AgdaVar{f} (the composition of the decoding function and
infinitary argument).


\AgdaHide{
\begin{code}
module El2 where
  open De
  open El1
\end{code}}

Second consider the interpretation function component (\AgdaFun{⟦\_⟧₂})
mapping slices to decoding functions. The decoding
function works by consuming the arguments
(of type \AgdaFun{⟦} \AgdaVar{D} \AgdaFun{⟧₁} \AgdaVar{R}) while
recursing down to the \AgdaCon{`ι} base case and returning
the \AgdaVar{o} it contains.

\begin{code}
  ⟦_⟧₂ : {O : Set} (D : Desc O) (R : Set/ O) → ⟦ D ⟧₁ R → O
  ⟦ `ι o ⟧₂ R tt = o
  ⟦ `σ A D ⟧₂ R (a , xs) = ⟦ D a ⟧₂ R xs
  ⟦ `δ A D ⟧₂ R@(X , d) (f , xs) = ⟦ D (d ∘ f) ⟧₂ R xs
\end{code}

The arguments are consumed by applying
dependent descriptions (\AgdaVar{D}) to the head argument
(a non-inductive \AgdaVar{a} or infinitary \AgdaVar{f}), and
recursively consuming the tail (\AgdaVar{xs}).
The \AgdaCon{`σ} case recursively searches the subsequent arguments
\AgdaVar{xs}, which are described by the dependent description
(\AgdaVar{D}) applied to the non-inductive first component
(\AgdaVar{a}). The \AgdaCon{`δ} case also searches the subsequent
arguments (\AgdaVar{xs}), but they are described by the dependent
description (\AgdaVar{D}) applied to the \textit{composition} of the
decoding function (\AgdaVar{d}) and the infinitary argument
\AgdaVar{f}.

\paragraph{Fixpoints}

The fixpoint operator ($\mu : (\set/O \arr \set/O) \arr \set/O$)
of inductive-recursive types is reified as
a \textit{derived} function
(\AgdaFun{μ} : \{\AgdaVar{O} : \AgdaData{Set}\}
\arr~\AgdaData{Desc} \AgdaVar{O}
\arr~\AgdaFun{Set/} \AgdaVar{O}),
parameterized by the output type \AgdaVar{O} and producing slices from
descriptions.
The pattern functor argument ($\set/O \arr \set/O$) of $\mu$ can be
derived by the model \AgdaFun{μ} by partially applying the
interpretation function to the
description argument
(\AgdaFun{⟦}~\AgdaVar{D}~\AgdaFun{⟧} :
\AgdaFun{Set/} \AgdaVar{O} \arr~\AgdaFun{Set/} \AgdaVar{O}).

In \refsec{iralgsem} we showed how the fixpoint
operator $\mu$ of algebraic semantics can be defined in terms of a
set component ($\mu_1$) and a decoding function component
($\mu_2$). Our type theoretic model similarly \textit{derives}
the fixpoint (\AgdaFun{μ}) as a dependent pair consisting of a
type component (\AgdaData{μ₁}) and a decoding function
component (\AgdaFun{μ₂}).

\AgdaHide{
\begin{code}
module _ where
 open De
 private
  data μ₁ : {O : Set} → Desc O → Set where
  postulate
   μ₂ : {O : Set} (D : Desc O) → μ₁ D → O
\end{code}}

\begin{code}
  μ : {O : Set} → Desc O → Set/ O
  μ D = μ₁ D , μ₂ D
\end{code}

Foo

\AgdaHide{
\begin{code}
module Fix where
  open De
  open El1
  open El2
  {-# TERMINATING #-}
  {-# NO_POSITIVITY_CHECK #-}
\end{code}}

\begin{code}
  mutual
    data μ₁ {O : Set} (D : Desc O) : Set where
      init : ⟦ D ⟧₁ (μ D) → μ₁ D
\end{code}

\AgdaHide{
\begin{code}
    μ : {O : Set} → Desc O → Set/ O
    μ D = μ₁ D , μ₂ D
\end{code}}

\begin{code}
    μ₂ : {O : Set} (D : Desc O) → μ₁ D → O
    μ₂ D (init xs) = ⟦ D ⟧₂ (μ D) xs
\end{code}

