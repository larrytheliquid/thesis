\AgdaHide{
\begin{code}
module _ where
\end{code}}

\section{Non-Dependent Types}\label{sec:nondepalg}

In this section we review the algebraic semantics for
\textit{non-dependent} and potentially
\textit{inductive} (\refsec{ind}) types. Then, we show how to
\textit{model} algebraic semantics within type theory by converting abstract
mathematical constructs to concrete datatypes (analogous to how we model
the abstract notion of a universe as concrete code and meaning
function types in \refsec{umodel}).

\subsection{Algebraic Semantics}

The algebraic semantics for an inductive datatype is the
\textit{least fixed point} of a polynomial equation
represented as a \textit{pattern functor}.

\paragraph{Natural Numbers}

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

The plus operator (+) represents a choice between constructors (analogous to
the disjoint union type \AgdaData{\_⊎\_}). Thus, above the left
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
\mathrm{Tree} \triangleq \lambda A.~ \lambda B.~ \mu X.~ A + X \cdot B \cdot X
$$

The \AgdaCon{leaf} constructor takes a single argument of type
\AgdaVar{A}, so the constructor is represented by $A$ (which is bound
by a $\lambda$). The \AgdaCon{branch} constructor has two inductive
arguments and an argument of type \AgdaVar{B}. Thus, its inductive
arguments are represented by $X$ (bound by $\mu$) and its other argument is represented by
$B$ (bound by another $\lambda$). The multiplication operator ($\cdot$)
represents multiple arguments of a constructor as a
conjunction (analogous to the pair type \AgdaData{\_×\_}).

\subsection{Algebraic Model}

\section{Infinitary Types}
\section{Dependent Types}
\section{Indexed Types}
\section{Inductive-Recursive Types}
\section{Indexed Inductive-Recursive Types}



