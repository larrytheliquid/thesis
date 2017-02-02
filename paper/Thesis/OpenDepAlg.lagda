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

\subsection{Algebraic Semantics}

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
the place of ($\arr$).
For example, product can be used to express dependencies as follows.
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
\key{if}~b~\key{then}~A~\key{else}~B
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
For example, below is the product of a natural number, an
infinitary occurrence, and 1.
$$
F \triangleq \lambda X.~
(n : \nat) \cdot X^{\tp{Fin}~n} \cdot 1
$$

The purpose of these additional constraints should not be readily
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
\key{if}~b~\key{then}~1~\key{else}~1
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
\key{if}~b~\key{then}~1~\key{else}~X^1 \cdot 1
$$

