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

\section{Dependent Types}
\section{Indexed Types}
\section{Inductive-Recursive Types}
\section{Indexed Inductive-Recursive Types}


