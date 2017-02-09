\AgdaHide{
\begin{code}
module _ where
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
Thus, algebraic semantics models inductive-recursive types
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
sequence of prodcts with $\iota$ (replacing 1) applied to an element
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



%% $$
%% \nat \triangleq \mu (X, d).~ (\iota \bullet + X^1 \cdot \iota \bullet)
%% $$


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



