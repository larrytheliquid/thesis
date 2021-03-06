\AgdaHide{
\begin{code}
module _ where
open import Function
open import Data.Bool
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality
\end{code}}

\section{Open Inductive-Recursive Types}\label{sec:iralg}

In this section, we extend the initial algebra semantics of
\textit{infinitary} and \textit{dependent} types
(\refsec{depalg})
to \textit{inductive-recursive} types
(\refsec{irtypes}). An inductive-recursive type is mutually defined
with a \textit{decoding} function that may be used in the inductive
definition of the type.

\subsection{Categorical Model}\label{sec:iralgsem}

In all of the previous categorical models we have worked with,
the pattern functors were \textit{endofunctors}
between the category of sets. That is, each functor
($F : \set \arr \set$)
mapped each set to another set.
Consequently, the fixpoint
($\mu : (\set \arr \set) \arr \set$)
of such a functor gave us back a set ($\mu~F : \set$).
Hence, previously each type could be semantically modeled as
a set ($\set$).

To define a categorical model of
\textit{inductive-recursive} types, we need to model
a type ($X : \set$) along with its mutually defined
\textit{decoding} function ($d : X \arr O$), mapping values of the
type to values of some output type ($O : \set$). For example,
\refsec{irtypes} presents the type of arithmetic expressions
($X \triangleq~$\AgdaData{Arith}) mutually defined with a decoding function
($d \triangleq~$\AgdaFun{eval} : \AgdaData{Arith} \arr~ \AgdaData{ℕ})
that evaluates an
expression to its natural number ($O \triangleq~$\AgdaData{ℕ}) result.
Thus, the categorical model of inductive-recursive sets
involves the dependent product of a set and its decoding function. Such a
dependent product is called a \textit{slice}, notated as
$\set/O$ (where $O$ is the output set).
$$
\set/O \triangleq (X : \set) \cdot (X \arr O)
$$

Pattern functors for inductive-recursive types are endofunctors
($F : \set/O \arr \set/O$)
of the slice category $\set/O$\footnote{
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
we denote the part by a subscript (i.e., $F_1$ and $F_2$).
$$
F_1 : \set/O \arr \set
$$
$$
F_2 : (R : \set/O) \arr F_1~R \arr O
$$

The first part ($F_1$) maps a slice to a
set (modeling a \textit{type}), similar to the functors
of previous subsections. The second part ($F_2$) maps a slice and a
member of the set mapped by $F_1$, to a member of
$O$ (modeling a \textit{decoding} function).
By convention we use the letter $R$ to refer to the \textit{slice}
argument to distinguish it from the contained set $X$ and decoding
function $d$.
We can put these two components of the functor together as a
dependent pair
to form the actual endofunctor over slices.
$$
F : \set/O \arr \set/O ~\triangleq~ \lambda R.~ (F_1~R ,~ F_2~R)
$$

We can separate the definition of least fixed points to be
defined similarly in terms of a fixed point operator ($\mu_1$, returning a set),
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

Recall our restriction of pattern functors to a sequence of dependent
products of non-inductive or infinitary arguments, terminating in 1.
$$
F_1 \triangleq \lambda (X, d).~
(x_0 : A_0) \cdot
(x_1 : A_1~x_0) \cdot
(x_2 : A_2~x_1~x_2) \cdot ...
\cdot (x_n : A_n ~ x_0 ~...~ x_{n-1}) \cdot 1
$$

Before, it only made sense for non-inductive arguments to be
dependent. For example, we could have a functor like the following
(where $A : \set$ and $B : A \arr \set$).
$$
F_1 \triangleq \lambda (X, d).~ (x_1 : A) \cdot (x_2 : B~a) \cdot 1
$$

With the introduction of inductive-recursive types, it is now actually
possible to use an inductive dependent argument by applying the
decoding function ($d$).
Below, we define functors like $F$ in 2 parts,
where $F_1$ defines the first (set) part
and $F_2$ is defines the second (decoding function) part.
For example, now we can have a functor like
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
For example, the notation above expands to the $F$ below
(first in terms of $F_1$ and $F_2$, and second once the definitions of
$F_1$ and $F_2$ have been expanded).
$$
F ~\triangleq~
\lambda (X, d).~ (F_1~(X, d) ,~ F_2~(X, d))
$$
$$
F ~\triangleq~
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
The inductive type can thus be defined normally, without referring
to its trivial function.
For example, below we define the
type of natural numbers along with the trivial function
(\AgdaFun{point}) from natural numbers to unit.\footnote{
  The intuition behind the name of the decoding function, \Fun{point},
  is that any inhabitant of the function is forced to eventually
  return \Con{tt}, the sole inhabitant of the unit type
  (\Data{⊤}). Hence, all \Fun{point} functions are extensionally
  equivalent, as they all ``point'' to \Con{tt}. Additionally, the
  single inhabitant \Con{tt} of \Data{⊤} can be considered a
  ``point''.
}

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

First we define the categorical model for this trivially
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

Because $\iota~\bullet$ appears twice, once on either side of (+),
the $\iota$-based $\nat$ technically  models the decoding function
\AgdaFun{ℕ₂} below, which
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

Above the result of applying the decoding function to a successor of a
natural number is specified
to be a \textit{recursive call} of the decoding function $d$ applied to:
the infinitary predecessor $f$
applied to the unit value $\bullet$. Hence, the pattern above is the
categorical model of the decoding function below
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


\subsection{Formal Model}\label{sec:iralgmod}

In this section we extend the formal model of
dependent types (\refsec{depalgmod}) to support inductive-recursive
types. The previous description type (\AgdaData{Desc}), interpretation
function (\AgdaFun{⟦\_⟧}) and least fixed point operator \AgdaData{μ}
are all modified to be parameterized over an output type
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

Our descriptions formally model the syntax of the 3rd ($\iota$) version of
legal pattern functors. Recall that $\iota$ is applied to an $O$,
hence we had an argument \AgdaVar{o} of type
\AgdaVar{O} to the
\AgdaCon{`ι} constructor. However, we also change \AgdaCon{`δ} in
a more subtle way (from \refsec{depalgmod}).

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
that subsequent arguments, encoded by \AgdaVar{D}, may depend on in.
With induction-recursion, \AgdaCon{`δ} denotes an
infinitary (hence \textit{inductive}) argument
(whose domain is \AgdaVar{A}) that subsequent arguments (\Var{D})
may depend on. However, subsequent arguments in \AgdaVar{D} do not
depend directly on an infinitary argument
(i.e., \AgdaVar{A} \arr~\AgdaVar{X}). Instead, \AgdaVar{D} depends on
a function (i.e., \AgdaVar{A} \arr~\AgdaVar{O}) that is an implicit
\textit{composition} of the decoding function and the infinitary function.
This implicit composition hides the underlying infinitary argument,
preventing an inductive argument (\AgdaVar{X}) from
appearing negatively in the domain of the infinitary argument
\AgdaVar{D} (instead, \AgdaVar{O} appears).
Below is an example of the natural numbers encoded as a
trivially (i.e., where the codomain of the decoding function
\AgdaVar{O} is the unit type \AgdaData{⊤})
inductive-recursive description.\footnote{
  It also happens to be a trivially infinitary type,
  because \Con{`δ} is applied to \AgdaData{⊤}, encoding a trivial
  infinitary domain.
  }

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
recognize that in the successor case of
the definitions of \AgdaFun{NatD} and \AgdaFun{ℕ₂} above,
\AgdaVar{f} $=$ \AgdaFun{ℕ₂} \AgdaFun{∘} \AgdaVar{n}.


\paragraph{Pattern Functors}

Now we turn to the task of formally modeling pattern functors
($F : \set/O \arr \set/O$) of
inductive-recursive types.
Before we can even consider doing so, we must formally model the
concept of a slice $\set/O$.
A slice is formally modeled as a dependent pair
type (\AgdaData{Σ})
parameterized by an output type (\AgdaVar{O}).
The first component of the pair is a type and the second
component is its decoding function.

\begin{code}
Set/ : Set → Set₁
Set/ O = Σ Set (λ A → (A → O))
\end{code}

We formally model pattern functors
($F : \set/O \arr \set/O$) as the functor
(\AgdaFun{F} : \AgdaFun{Set/} \AgdaVar{O} \arr~\AgdaFun{Set/} \AgdaVar{O})
resulting from the partial application of a description
to the interpretation function
(\AgdaFun{⟦\_⟧} : \{\AgdaVar{O} : \AgdaData{Set}\}
\arr~\AgdaData{Desc} \AgdaVar{O} \arr~\AgdaFun{Set/} \AgdaVar{O} \arr~\AgdaFun{Set/} \AgdaVar{O}).
In \refsec{iralgsem}
we showed the categorical model of $F$ in terms of a component mapping slices to sets
($F_1$) and a component mapping slices to a decoding function ($F_2$). Our
formal model similarly defines the interpretation function
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

\textit{First}, consider the interpretation function component (\AgdaFun{⟦\_⟧₁})
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
depend on the composed function (returning an \AgdaVar{O}), but
cannot directly depend on the infinitary function
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

\textit{Second}, consider the interpretation function component (\AgdaFun{⟦\_⟧₂})
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
derived by the formal model of \AgdaFun{μ} by partially applying the
interpretation function to the
description argument
(\AgdaFun{⟦}~\AgdaVar{D}~\AgdaFun{⟧} :
\AgdaFun{Set/} \AgdaVar{O} \arr~\AgdaFun{Set/} \AgdaVar{O}).

In \refsec{iralgsem} we showed the categorical model of the fixpoint
operator $\mu$, defining it in terms of a
set component ($\mu_1$) and a decoding function component
($\mu_2$). Our formal model similarly \textit{derives}
the fixpoint (\AgdaFun{μ}) as a dependent pair consisting of a
type component (\AgdaData{μ₁}) and a decoding function
component (\AgdaFun{μ₂}). We define these 3 constructions
(a type synonym \AgdaFun{μ}, a datatype \AgdaData{μ₁}, and
a function \AgdaFun{μ₂}) mutually below.\footnote{
  The type \Data{μ₁} and the function
  \Fun{μ₂} in this section can only be defined by disabling Agda's
  positivity and termination checkers. In \refsec{iralgagda}, we
  present an alternative model that need not disable any
  Agda checkers.
  }

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
    μ : {O : Set} → Desc O → Set/ O
    μ D = μ₁ D , μ₂ D

    data μ₁ {O : Set} (D : Desc O) : Set where
      init : ⟦ D ⟧₁ (μ D) → μ₁ D

    μ₂ : {O : Set} (D : Desc O) → μ₁ D → O
    μ₂ D (init xs) = ⟦ D ⟧₂ (μ D) xs
\end{code}

The argument to the \AgdaCon{init}ial algebra needs to be a type
representing constructors (of \AgdaData{μ₁}, and their arguments).
This type is computed by applying the first component
(\AgdaFun{⟦\_⟧₁}) of the interpretation function to the
description (\AgdaVar{D}) and its fixpoint (\AgdaData{μ} \AgdaVar{D}).
The output of the
decoding function (\AgdaFun{μ₂}) is
computed by applying the description (\AgdaVar{D}),
its fixpoint (\AgdaData{μ} \AgdaVar{D}),
and the argument of
the initial algebra (\AgdaVar{xs}) to the
second component (\AgdaFun{⟦\_⟧₂}) of the interpretation function.


\subsection{Examples}\label{sec:iralgtps}

Now we formally model the type formers and constructors of
\textit{inductive-recursive} datatypes.
Typically inductive-recursive datatypes are defined mutually
in terms of a type and its decoding function.
In our formal model, a single
description captures definition of \textit{both} the type and its
decoding function.

\paragraph{Natural Numbers}

Let's refamiliarize ourselves with the definition of natural
numbers as a trivially inductive-recursive datatype.
We use the variant of the inductive-recursive natural numbers where
the \AgdaCon{suc} case of decoding function (\AgdaFun{point}) is defined
recursively (rather than constantly returning \AgdaCon{tt}).

\AgdaHide{
\begin{code}
module _ where
 open import Data.Unit
 open import Data.Bool
 private
\end{code}}

\begin{code}
  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

  point : ℕ → ⊤
  point zero = tt
  point (suc n) = point n
\end{code}

We expose the formal model of the \textit{non-infinitary} natural
numbers presented above.
As in \refsec{depalgtps}, this means our type former
and constructors will have the \textit{names} and \textit{types}
corresponding to the ones above. However, our underlying pattern
functor formally models the \textit{infinitary} and \textit{slice-based}
definition of natural numbers below.

The non-infinitary type \AgdaData{ℕ} above corresponds to infinitary
type \AgdaData{ℕ₁} below. The
decoding function \AgdaFun{point} above corresponds to \AgdaFun{ℕ₂}
below. Finally, the slice \AgdaFun{ℕ} below does not correspond to
anything above.
While slices are commonly used to describe the
semantics of inductive-recursive types, they are rarely used in
conventional programming with inductive-recursive types.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Unit
 open import Data.Bool
 private
\end{code}}

\begin{code}
  data ℕ₁ : Set where
    zero : ℕ₁
    suc : (⊤ → ℕ₁) → ℕ₁

  ℕ₂ : ℕ₁ → ⊤
  ℕ₂ zero = tt
  ℕ₂ (suc n) = ℕ₂ (n tt)

  ℕ : Set/ ⊤
  ℕ = ℕ₁ , ℕ₂
\end{code}

Now we specify the pattern functor of the datatype as an inductive-recursive
description. We use a datatype of tags (\AgdaData{NatT}), representing
each constructor (as in \refsec{depalgmod}). We also explicitly define
the function (\AgdaFun{NatDs}) taking tags to the description of
arguments for the constructor that each tag represents.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Unit
 open import Data.Bool
 open import Relation.Binary.PropositionalEquality
 open De
 open El1
 open El2
 open Fix
 private
\end{code}}

\begin{code}
  data NatT : Set where
    zeroT sucT : NatT

  NatDs : NatT → Desc ⊤
  NatDs zeroT = `ι tt
  NatDs sucT = `δ ⊤ (λ f → `ι (f tt))

  NatD : Desc ⊤
  NatD = `σ NatT NatDs
\end{code}

We model the type (\AgdaData{ℕ})
and decoding function (\AgdaFun{point}) by applying the
type component (\AgdaData{μ₁}) and decoding function component
(\AgdaFun{μ₂}) of the fixpoint operator to the description
(\AgdaFun{NatD}).
Once again, we are modeling
the \textit{non-infinitary} and \textit{slice-less} type of natural
numbers in terms of its underlying
\textit{infinitary} and \textit{slice-based} pattern functor.

\begin{code}
  ℕ : Set
  ℕ = μ₁ NatD

  point : ℕ → ⊤
  point = μ₂ NatD
\end{code}

Finally, we model the constructors. As done previously, the
\AgdaCon{suc} constructor creates an infinitary argument as a function
ignoring the infinitary domain value (\AgdaVar{u}), and constantly returning
the non-infinitary predecessor (\AgdaVar{n}).

\begin{code}
  zero : ℕ
  zero = init (zeroT , tt)

  suc : ℕ → ℕ
  suc n = init (sucT , (λ u → n) , tt)
\end{code}

\paragraph{Arithmetic Expressions}

Now we model a non-trivially inductive-recursive and
non-trivially infinitary type, namely the
type of arithmetic expressions (\AgdaData{Arith}).
You may wish to revisit \refsec{irtypes} for
examples of what arithmetic expressions represent.
An \AgdaData{Arith} can be evaluated to the natural
number that the arithmetic expression represents, using the
\AgdaFun{eval} decoding function.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Unit
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
    eval (Prod a f) = prod (eval a) (λ i → eval (f i))
\end{code}

Our pattern functor models the \textit{slice-based} and
\textit{infinitary} version of the arithmetic expressions below.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Unit
 open import Data.Nat
 open import Data.Fin
 private
  postulate prod : (n : ℕ) (f : Fin n → ℕ) → ℕ
\end{code}}

\begin{code}
  mutual
    data Arith₁ : Set where
      Num : ℕ → Arith₁
      Prod : (a : ⊤ → Arith₁) (f : Fin (Arith₂ (a tt)) → Arith₁) → Arith₁
  
    Arith₂ : Arith₁ → ℕ
    Arith₂ (Num n) = n
    Arith₂ (Prod a f) = prod (Arith₂ (a tt)) (λ i → Arith₂ (f i))

  Arith : Set/ ℕ
  Arith = Arith₁ , Arith₂
\end{code}

The description of the \textit{slice-based} pattern functor is defined
in terms of a function (\AgdaFun{ArithDs}) taking arithmetic
expression constructor tags (\AgdaData{ArithT}) to descriptions of the
arguments for the constructor that each tag represents.

Compare the index that \AgdaData{Fin} is applied to in the type
\AgdaData{Arith₁} above and description \AgdaFun{ArithDs} below.
Notice that
the dependent infinitary \AgdaVar{a} in the description below
represents the composition of the decoding function \AgdaFun{Arith₂}
and the infinitary \AgdaVar{a} above.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open import Data.Fin
 open De
 open El1
 open El2
 open Fix
 private
  postulate prod : (n : ℕ) (f : Fin n → ℕ) → ℕ
\end{code}}

\begin{code}
  data ArithT : Set where
    NumT ProdT : ArithT

  ArithDs : ArithT → Desc ℕ
  ArithDs NumT = `σ ℕ λ n → `ι n
  ArithDs ProdT =
    `δ ⊤ λ a →
    `δ (Fin (a tt)) λ f →
    `ι (prod (a tt) f)

  ArithD : Desc ℕ
  ArithD = `σ ArithT ArithDs
\end{code}

Also notice how each description, in the \AgdaCon{NumT} and
\AgdaCon{ProdT} cases of \AgdaFun{ArithDs}, ends in
\AgdaCon{`ι}. The description prior to
\AgdaCon{`ι} represents the type \AgdaData{Arith₁} above, and the
natural number contained in \AgdaCon{`ι} represents the
output of the decoding function \AgdaFun{Arith₂} above.
Finally, the arguments
of the decoding function cases are represented by the
non-inductive (\AgdaCon{`σ}) and infinitary (\AgdaCon{`δ})
dependencies of the description prior to \AgdaCon{`ι}.

We model the type (\AgdaFun{Arith})
and decoding function (\AgdaFun{eval}) by applying the
type component (\AgdaData{μ₁}) and decoding function component
(\AgdaFun{μ₂}) of the fixpoint operator to the description
(\AgdaFun{ArithD}).

\begin{code}
  Arith : Set
  Arith = μ₁ ArithD

  eval : Arith → ℕ
  eval = μ₂ ArithD
\end{code}

The same techniques used to model the
\textit{non-infinitary} and \textit{slice-less} 
constructors of the \AgdaData{ℕ} type are used to model the
constructors of the \AgdaData{Arith} type.

\begin{code}
  Num : ℕ → Arith
  Num n = init (NumT , n , tt)

  Prod : (a : Arith) (f : Fin (eval a) → Arith) → Arith
  Prod a f = init (ProdT , (λ u → a) , f , tt)
\end{code}


\paragraph{Vectors}

Now we show how to \textit{derive} an \textit{indexed} type, like
vectors, from a non-trivially \textit{inductive-recursive} type.
But first, let's refamiliarize ourselves with the high-level indexed
vector definition we wish to derive.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 private
\end{code}}

\begin{code}
  data Vec (A : Set) : ℕ → Set where
    nil : Vec A zero
    cons : (n : ℕ) (a : A) (xs : Vec A n) → Vec A (suc n)
\end{code}

Before describing the transformation~\cite{smallir} to turn this indexed type into an
isomorphic type using induction-recursion, we describe the intuition
behind the transformation. A well-known derived (isomorphic)
representation of vectors is the dependent pair (\Data{Σ})
of a \Data{List} and a constraint on its \Fun{length}, using the
equality type (\Data{≡}).

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 private
\end{code}}

\begin{code}
  data List (A : Set) : Set where
    nil : List A
    cons : (a : A) (xs : List A) → List A

  length : {A : Set} → List A → ℕ
  length nil = zero
  length (cons a xs) = suc (length xs)

  Vec : Set → ℕ → Set
  Vec A n = Σ (List A) (λ xs → length xs ≡ n)
\end{code}

While this is a nice and simple translation, it doesn't capture the
notion of a vector as intensionally as we would like. Specifically,
the \Con{cons} constructor of \Data{List} does not a contain the
non-inductive natural number argument (\Var{n}). Additionally, while
the outermost derived \Fun{Vec} contains
the index constraint (\Data{≡}), the inductive \Data{List} argument
(\Var{xs}) of \Con{cons} does not.

Instead of deriving \Fun{Vec} from \Data{List} and \Fun{length} like
above, we can use induction-recursion to \textit{mutually} define these 3
components. Induction-recursion allows us to derive an inductive
datatype (\Data{Vec₁}, analogous to \Data{List})
with the same collection of non-inductive constructor
arguments as our high-level indexed \Data{Vec}, and adds index
constraints to go along with every inductive-argument.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 private
\end{code}}

\begin{code}
  mutual
    data Vec₁ (A : Set) : Set where
      nil : Vec₁ A
      cons : (n : ℕ) (a : A) (xsq : Vec A n) → Vec₁ A

    Vec₂ : {A : Set} → Vec₁ A → ℕ
    Vec₂ nil = zero
    Vec₂ (cons n x xsq) = suc n

    Vec : Set → ℕ → Set
    Vec A n = Σ (Vec₁ A) (λ xs → Vec₂ xs ≡ n)
\end{code}

We transform (as above) a high-level indexed type
(like \Data{Vec}) into a derived
version (like \Fun{Vec}), using induction-recursion, by changing 3 things:

\begin{enumerate}
\item
  The original indexed type (\Data{Vec}) becomes an inductive-recursive
  type (\Data{Vec₁}), with a decoding function (\Fun{Vec₂}).
  The inductive-recursive type (\Data{Vec₁}) still contains all
  non-inductive arguments (like \Var{n} of \Con{cons}).

\item
  Original inductive arguments (\Var{xs}) of the
  indexed type are replaced by a value (\Var{xsq}) of a derived dependent pair
  type (\Fun{Vec}). The first component of the dependent pair is the
  inductive-recursive type \Data{Vec₁}, and the second component
  constrains the index of the original inductive argument (\Var{n})
  to equal what the decoding function (\Fun{Vec₂}) returns.

\item
  The decoding function (\Fun{Vec₂}) is defined by matching on
  the constructors of the inductive-recursive type (\Data{Vec₁}), and
  returning what the original high-level indexed type (\Data{Vec}) had
  in the index position of the codomain for the corresponding constructor.

\end{enumerate}

Finally, we make one last change, allowing us to formally model the indexed
type of vectors using our initial algebra semantics of inductive-recursive
types. The inductive-recursive type \Data{Vec₁} curries inductive
occurrences of the derived dependent pair (\Data{Vec}) as 2 separate
arguments. Below, \Var{xsq} is replaced by \Var{xs} (the inductive
argument of \Data{Vec₁}) and \Var{q} (the constraint). By consequence,
the dependent pair \Fun{Vec} no longer needs to be defined mutually.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 private
\end{code}}

\begin{code}
  mutual
    data Vec₁ (A : Set) : Set where
      nil : Vec₁ A
      cons : (n : ℕ) (a : A) (xs : Vec₁ A) (q : Vec₂ xs ≡ n) → Vec₁ A

    Vec₂ : {A : Set} → Vec₁ A → ℕ
    Vec₂ nil = zero
    Vec₂ (cons n x xs q) = suc n

  Vec : Set → ℕ → Set
  Vec A n = Σ (Vec₁ A) (λ xs → Vec₂ xs ≡ n)
\end{code}

%% Above, we also changed the \Con{cons} case of the decoding
%% function (\Fun{Vec₂}) to make a recursive call instead of immediately
%% returning \Var{n}. This change is not necessary
%% (but it is still isomorphic to the high-level indexed \Data{Vec}),
%% and we only do it to make
%% the inductive-recursive definition more pedagogically interesting.

Now we formally model the \textit{slice-based} pattern functor of the
inductive-recursive \Data{Vec₁} type.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open import Relation.Binary.PropositionalEquality
 open De
 open El1
 open El2
 open Fix
 private
\end{code}}

\begin{code}
  data VecT : Set where
    nilT consT : VecT

  VecDs : Set → VecT → Desc ℕ
  VecDs A nilT = `ι zero
  VecDs A consT =
    `σ ℕ λ n →
    `σ A λ a →
    `δ ⊤ λ xs →
    `σ (xs tt ≡ n) λ q →
    `ι (suc n)

  VecD : Set → Desc ℕ
  VecD A = `σ VecT (VecDs A)
\end{code}

We model the inductive-recursive type (\Data{Vec₁})
and decoding function (\Fun{Vec₂}) by applying the
type component (\Data{μ₁}) and decoding function component
(\Fun{μ₂}) of the fixpoint operator to the description
(\Fun{VecD}).

\begin{code}
  Vec₁ : Set → Set
  Vec₁ A = μ₁ (VecD A)

  Vec₂ : (A : Set) → Vec₁ A → ℕ
  Vec₂ A = μ₂ (VecD A)
\end{code}

Finally, we model the indexed type (\Fun{Vec}) as a dependent pair, derived in
terms of the inductive-recursive type (\Fun{Vec₁})
and an index constraint using the decoding function (\Fun{Vec₂}).

\begin{code}
  Vec : Set → ℕ → Set
  Vec A n = Σ (Vec₁ A) (λ xs → Vec₂ A xs ≡ n)
\end{code}

The main thing to notice about the way we model the constructors is
that our model of indexed vectors (\Fun{Vec}) is in terms of a
dependent pair. 

\begin{code}
  nil : {A : Set} → Vec A zero
  nil = init (nilT , tt) , refl

  cons : {A : Set} → (n : ℕ) (a : A) (xs : Vec A n) → Vec A (suc n)
  cons n a (xs , q) = init (consT , n , a , (λ u → xs) , q , tt) , refl
\end{code}

Both \Con{nil} and \Con{cons} return an
inductive-recursive \Fun{Vec₁} in the first component of the pair, and
an index constraint proof (in terms of \Fun{Vec₂}) in the second
component of the pair. Additionally, \Con{cons} destructs its
``inductive'' \Fun{Vec} arguments in terms of the underlying pair
components \Var{xs} and \Var{q}.

\subsection{Agda Model}\label{sec:iralgagda}

In previous sections on
non-dependent types (\refsec{nondepalgmod}),
infinitary types (\refsec{infalgmod}),
and dependent types (\refsec{depalgmod}),
the formal model (i.e., a model in type theory)
corresponded to the Agda model (i.e., a model in an implementation of type
theory).
Unfortunately, this is not the case for the formal model
presented for inductive-recursive types in \refsec{iralgmod}.

Although we used Agda syntax in the formal model of \refsec{iralgmod},
we had to turn off the positivity and termination checkers when
inductive-recursively defining the fixpoint datatype (\Data{μ₁}) and
its decoding function (\Fun{μ₂}). Even though Agda (the
implementation of type theory that we are using) cannot confirm that
this definition preserves consistency, Dybjer and Setzer have proven
the consistency of the construction in a model of set theory (extended
by the Mahlo cardinal)~\cite{inductionrecursion1}.

To pass Agda's positivity and termination checkers,
we define the following
Agda model as an alternative to the formal model in \refsec{iralgmod}.
Our Agda model mutually defines the pattern functor
interpretation functions (\Fun{⟦\_⟧₁} for the interpretation of types,
and \Fun{⟦\_⟧₂} for the interpretation of decoding functions),
along with the inductive-recursive fixpoint type \Data{μ₁}
and fixpoint decoding function (\Fun{μ₂}).

\AgdaHide{
\begin{code}
module _ where
 open De
 private
\end{code}}

\begin{code}
  mutual
    ⟦_⟧₁ : {O : Set} (D R : Desc O) → Set
    ⟦ `ι o ⟧₁ R = ⊤
    ⟦ `σ A D ⟧₁ R = Σ A (λ a → ⟦ D a ⟧₁ R)
    ⟦ `δ A D ⟧₁ R = Σ (A → μ₁ R) λ f → ⟦ D (λ a → μ₂ R (f a)) ⟧₁ R
  
    ⟦_⟧₂ : {O : Set} (D R : Desc O) → ⟦ D ⟧₁ R → O
    ⟦ `ι o ⟧₂ R tt = o
    ⟦ `σ A D ⟧₂ R (a , xs) = ⟦ D a ⟧₂ R xs
    ⟦ `δ A D ⟧₂ R (f , xs) = ⟦ D (λ a → μ₂ R (f a)) ⟧₂ R xs
 
    data μ₁ {O : Set} (D : Desc O) : Set where
      init : ⟦ D ⟧₁ D → μ₁ D
 
    μ₂ : {O : Set} (D : Desc O) → μ₁ D → O
    μ₂ D (init xs) = ⟦ D ⟧₂ D xs
\end{code}

Notice that the types of the pattern functor interpretation
functions (\Fun{⟦\_⟧₁} and \Fun{⟦\_⟧₂}) have changed.
In the type of the interpretation functions,
the \Var{R} argument is now
a description (\Data{Desc} \Var{O}),
instead of a slice (\Fun{Set/} \Var{O}).
Because \Var{R} is now a description (rather than a slice),
partially applying a description \Var{D} to the
interpretation function (\Fun{⟦\_⟧}, defined as the dependent pair
of \Fun{⟦\_⟧₁} and \Fun{⟦\_⟧₂} in \refsec{iralgmod})
no longer results in a pattern endofunctor on
slices. While we lose some of the beautiful correspondence with our
categorical model, we have effectively inlined a specialized version
of the interpretation functions that allows Agda to confirm that
the type fixpoint component (\Data{μ₁})
is positive and that the decoding function fixpoint component
(\Fun{μ₂}) terminates.

All of our earlier examples of inductive-recursive type encodings
(\refsec{iralgtps}) still work.
This is because our examples of type formers and constructors only
rely on the interfaces exposed by \Data{μ₁} and \Fun{μ₂},
so changing their implementations to mutually
be defined in terms of \Fun{⟦\_⟧₁} and \Fun{⟦\_⟧₂} does not break
anything. 

Finally, this construction of open algebraic types
can also be found in \refapen{openalg}.
In the Appendix, we remove backticks from the \Data{Desc}
constructor names, so that we may distinguish open descriptions
from closed descriptions in \refchap{closed}.
We also change the \Var{O} parameter
of \Data{μ₁} to be an explicit argument.
The primitive types assumed in the
construction of \refapen{openalg}
are defined in \refapen{openprim}.

