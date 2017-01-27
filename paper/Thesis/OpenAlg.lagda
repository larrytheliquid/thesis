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

\subsection{Algebraic Semantics}\label{sec:nondepalgsem}

The algebraic semantics for an inductive datatype is the
\textit{least fixed point} of a polynomial equation
represented as a \textit{pattern functor}.
The input of the pattern functor represents the inductive set being
defined ($X$), and its output must be a set formed by
\textit{polynomial} set
constructions (namely 1, +, $\cdot$, and $X$, representing the
unit set, the sum of two sets, the product of two sets, and
inductive occurrences of the set).

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
the disjoint union type \AgdaData{⊎}). Thus, above the left
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
arguments and a non-inductive argument of type \AgdaVar{B}. Thus, its inductive
arguments are represented by $X$ (bound by $\mu$) and its
non-inductive argument is represented by
$B$ (bound by another $\lambda$). The multiplication operator ($\cdot$)
represents multiple arguments of a constructor as a
conjunction (analogous to the pair type \AgdaData{×}).

%% TODO maybe mention similarity to param universe ParStar
\subsection{Algebraic Model}

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
the pattern functor \textit{restrictions} as a datatype, the
pattern \textit{functor}
as a computational type family (\refsec{compu}), and the \textit{fixpoint}
operator as a datatype.

\paragraph{Descriptions}

The first part of our algebraic model is the type of descriptions
(\AgdaData{Desc}). A \AgdaData{Desc} is the syntactic reification of
the polynomial expression language that must be used for a functor to
qualify as a \textit{pattern} functor. Rather than defining a pattern
functor directly, we first represent it as a \AgdaData{Desc} such
that any well typed description can be converted into a functor
meeting all pattern restrictions.

Below, the \AgdaData{Desc} constructors
\AgdaCon{`1}, \AgdaCon{`X},
(\AgdaCon{`+}), and (\AgdaCon{`∙}) respectively reify a \textit{syntax} for
the 1, $X$, (+), and ($\cdot$) polynomial set constructions.
Of special note is the \AgdaCon{`κ} \textit{constant} constructor.
The \textit{constant} constructor reifies a syntax for injecting
\footnote{
  As is often the case with injections, its syntax is implicit when
  defining pattern functors using polynomial set constructions.
  }
\textit{non-inductive} constructor arguments (such as \AgdaVar{A} in the
\AgdaCon{leaf} constructor of \AgdaData{Tree}). 

\AgdaHide{
\begin{code}
module Desc where
 open import Data.Unit
 open import Data.Sum
 open import Data.Product
 private
\end{code}}

\begin{code}
  data Desc : Set₁ where
    `1 `X : Desc
    _`+_  _`∙_ : Desc → Desc → Desc
    `κ : Set → Desc
\end{code}

Finally, note that we establish another convention of ``quoting''
description constructors with a backtick (e.g. \AgdaCon{`X} for $X$).
This emphasizes that they are the syntactification of polynomial set
constructions. As we will see, quoting \AgdaData{Desc} constructors is
natural as they also act as codes of a universe (\refsec{TODO}).

\paragraph{Pattern Functors}

The next part of our algebraic model is the reification of pattern functors
($F : \set \arr \set$) as \textit{type families} (\refsec{tfam})
with \AgdaData{Set} as their domain
(\AgdaFun{F} : \AgdaData{Set} \arr~\AgdaData{Set}).
We define a
\textit{computational type family}
(\AgdaFun{⟦}\_\AgdaFun{⟧} : \AgdaData{Desc} \arr~\AgdaData{Set} \arr~\AgdaData{Set})
to interpret a
\AgdaData{Desc} (the language of polynomial expressions) as a
pattern functor.

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
\forall \AgdaVar{D}.~ \AgdaFun{F} \triangleq \AgdaFun{⟦}~\AgdaVar{D}~\AgdaFun{⟧}
$$

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
(\AgdaData{⊎}), modeling (+), by interpreting the
(\AgdaCon{`+}) description. It may not use other arbitrary
types lacking a polynomial set construction equivalent (because their
is no \AgdaData{Desc} for them), like ($\arr$)
with negative occurrences of \AgdaVar{X}.

Finally, note that it may appear that \AgdaCon{`κ} could be used to
inject many non-polynomial types. While this is true, it is not
problematic because the type (\AgdaVar{A}) that \AgdaCon{`κ} injects
must be \textit{non-inductive}. The non-inductivity of \AgdaVar{A} is
enforced because \AgdaVar{A} must be a type defined independently of
\AgdaVar{X} (i.e. the interpretation of \AgdaCon{`κ} does not, for
example, pass \AgdaVar{X} to \AgdaVar{A}).

\subsection{Models of Types}

\section{Infinitary Types}
\section{Dependent Types}
\section{Indexed Types}
\section{Inductive-Recursive Types}
\section{Indexed Inductive-Recursive Types}



