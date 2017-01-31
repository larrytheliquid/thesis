\AgdaHide{
\begin{code}
module _ where
open import Data.Unit
open import Data.Sum
open import Data.Product
\end{code}}

\section{Infinitary Types}

In this section we review the algebraic semantics for
\textit{infinitary} (\refsec{inft}) non-dependent types.
We extend our previous algebraic semantics, algebraic model
within type theory,
and examples of modeled types to support \textit{infinitary}
constructor arguments.

\subsection{Algebraic Semantics}\label{sec:infalgsem}

The algebraic semantics for \textit{infinitary} inductive datatypes
reuses the 1, (+) and ($\cdot$) polynomial set construtions. However,
the inductive occurrences construction $X$ is subsumed by the
\textit{infinitary} occurrences construction $X^A$. Functions are the
type theoretic equivalent of exponential terms, where $X$ raised to
the power of $A$ is equivalent to a function with domain $A$ and
codomain $X$.
\footnote{
  If $A$ and $X$ are finite sets, then the cardinality of $X^A$ is
  equal to the cardinality of the graph of the function $A \arr X$.
  }
$$
X^A \triangleq (A \arr X)
$$

Therefore, $X^A$ is notation for an infinitary polynomial set
construction whose domain is $A$ and whose codomain is an inductive
occurrence.
Any non-infinitary inductive argument $X$ can be isomorphically expressed
as an infinitary argument by raising $X$ to the power of 1 (or equivalently,
a function whose domain is 1 and whose codomain is $X$).

$$
X \cong (X^1 \triangleq 1 \arr X)
$$

\paragraph{Natural Numbers}

\AgdaHide{
\begin{code}
module _ where
 open import Data.Unit
 private
\end{code}}

For example, consider the infinitary (but isomorphic) declaration of
the natural numbers below. The inductive argument to the
\AgdaCon{suc} constructor has been replaced with
the infinitary argument \AgdaVar{f}, using the unit type as its
domain.

\begin{code}
  data ℕ : Set where
    zero : ℕ
    suc : (f : ⊤ → ℕ) → ℕ
\end{code}

The algebraic semantics for infinitary \AgdaData{ℕ} is the fixpoint
equation below.
$$
\nat \triangleq \mu X.~1 + X^1
$$

The only difference between the non-infinitary and infinitary
\AgdaData{ℕ} is that constructing it with \AgdaCon{suc} must supply a
function ignoring a \AgdaData{⊤} argument, and destructing
\AgdaCon{suc} requires applying \AgdaVar{f} to the trivial value
\AgdaCon{tt} to access the inductive value in the body of
\AgdaVar{f}.

\paragraph{Binary Trees}

Below is a straightforward infinitary encoding of binary trees,
replacing both inductive arguments of \AgdaCon{branch} with infinitary
ones by using the unit type as the domain.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Unit
 private
\end{code}}

\begin{code}
  data Tree (A B : Set) : Set where
    leaf : A → Tree A B
    branch : (f : ⊤ → Tree A B) (b : B) (g : ⊤ → Tree A B) → Tree A B
\end{code}

This translates to the the algebraic semantics for infinitary binary
trees below without any surprises.
$$
\dfn{Tree} \lambda A.~ \lambda B.~ \mu X.~ A + X^1 \cdot B \cdot X^1
$$

However, recall our series of isomorphic translations of the binary
tree declaration used to model \AgdaData{Tree} via \AgdaData{W}
types (\refsec{wtypes}). We can borrow two of those isomorphisms to
reorder the \AgdaVar{B} argument to the front via symmetry
(\texttt{A × B ≅ B × A}), causing both inductive arguments to appear
at the end of \AgdaCon{branch}.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Bool
 private
\end{code}}

\begin{code}
  data Tree (A B : Set) : Set where
    leaf : A → Tree A B
    branch : (b : B) (t₁ : Tree A B) (t₂ : Tree A B) → Tree A B
\end{code}

Then, we can appeal to the isomorphism that defines a non-dependent
pair as a dependent function from \AgdaData{Bool} to each component of
the pair (\texttt{A × B ≅ Π Bool (λ b → if b then A else B)}).

\AgdaHide{
\begin{code}
module _ where
 open import Data.Bool
 private
\end{code}}

\begin{code}
  data Tree (A B : Set) : Set where
    leaf : A → Tree A B
    branch : (b : B) (f : Bool → Tree A B) → Tree A B
\end{code}

This translates both inductive arguments into a \textit{single}
infinitary argument, where the domain is now \AgdaData{Bool} instead
of \AgdaData{⊤}. It makes sense for the domain (i.e. branching factor)
to be \AgdaData{Bool}, as we are defining \textit{binary} trees.
Given that the cardinality of \AgdaData{Bool} is 2, we use
algebraic semantics to define infinitary binary
trees by raising $X$ to the power of 2 in the encoding of the
\AgdaCon{branch} constructor.
$$
\dfn{Tree} \lambda A.~ \lambda B.~ \mu X.~ A + B \cdot X^2
$$


\section{Dependent Types}
\section{Indexed Types}
\section{Inductive-Recursive Types}
\section{Indexed Inductive-Recursive Types}


