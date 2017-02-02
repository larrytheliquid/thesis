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
0) sets, ending in a multiplication by the unite set 1. Each
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

Recall from \refsec{depalgsem} that we constraint dependent pattern
functors to a sequence of products ending in 1. Recall also that
descriptions are the reification (or model) of the language used to
create legal pattern functors.
Hence, we change the type of descriptions to enforce that pattern
functors (representing definitions of datatypes) are sequences of
dependent pairs (\AgdaData{Σ}) ending in the unit type
(\AgdaData{⊤}).

Below, we model the pattern of ending (with the unit type) a functor
with the \AgdaCon{`ι} constructor. For now this is simply a renaming
of the former \AgdaCon{`1} constructor.
\footnote{
  However, in future extensions
  supporting indexed types (\refsec{idxalg}) and inductive-recursive
  types (\refsec{iralg})) \AgdaCon{`ι} gains additional arguments.
}
A \textit{dependent} (but non-infinitary)
argument is modeled by the \AgdaCon{`σ} constructor. An
\textit{infinitary} (but non-dependent) argument is modeled by the
\AgdaCon{`δ} constructor.
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
a single product ($\cdot$) for both dependent and infinitary
arguments, our new description syntax distinguishes between
dependent (\AgdaCon{`σ}) and infinitary (\AgdaCon{`δ}) arguments. 

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
non-dependent pair \AgdaCon{`δ}. When \AgdaCon{`σ} is used to request
an argument \AgdaVar{A}, the rest of the description \AgdaVar{D} may
depend on a value of \AgdaVar{A}. This is modeled by the infinitary
type of \AgdaVar{D}, namely \AgdaVar{A} \arr~
\AgdaData{Desc}. Notice that the left component of (\AgdaCon{`∙}) is
a description (\AgdaData{Desc}), but the left component of
\AgdaCon{`σ} is a type (\AgdaData{Set}). If \AgdaVar{A} were a
description, and \AgdaVar{D} could depend on a value of the inductive
type being defined, then our type of descriptions (\AgdaData{Desc})
would be \textit{negative} (and we could subsequently use it to
model pattern functors of negative types).
Hence, the first component of a dependent pair (\AgdaVar{A})
must be restricted to a type (guaranteed to be non-inductive)
so that the infinitary type \AgdaVar{D}
(representing subsequent arguments in the description) remains
\textit{positive}.


\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open import Data.Fin
 open Desc
 private
\end{code}}

\begin{code}
  _`+_ : Desc → Desc → Desc
  D `+ E = `σ Bool (λ b → if b then D else E)

  `κ : Set → Desc
  `κ A  = `σ A (λ a → `ι)

  `X^ : Set → Desc
  `X^ A  = `δ A `ι

  postulate _`∙_ : Desc → Desc → Desc
\end{code}


\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open import Data.Fin
 open Desc
 private
\end{code}}

\begin{code}
  RoseD : Desc
  RoseD = `σ ℕ (λ n → `δ (Fin n) `ι)

  NatD : Desc
  NatD = `σ Bool (λ b → if b then `ι else `δ ⊤ `ι)
\end{code}


