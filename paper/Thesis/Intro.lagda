\AgdaHide{
\begin{code}
open import Data.Empty
open import Data.Unit
open import Data.Bool hiding ( not )
open import Data.Product
module _ where
\end{code}}

\section{Dependently Typed Languages}\label{sec:deplang}

A standard dependently typed language is
\textit{purely functional} (meaning the absence of side effects),
\textit{total}
(meaning all inductively defined functions
terminate and cover all possible inputs), and has a
type system that captures the notion of \textit{dependency}.

A single term language is used to write programs at the value and type
level. The combination of total programming at the type level and a
notion of dependency betweeen types allows any proposition of
intuitionistic logic to be expressed as a type.
A value (or equivalently, a total program) inhabiting a
type encoding a proposition serves as its intuitionistic proof. This
correspondence between values \& types and proofs \& propositions is known
as the \textit{Curry-Howard Isomorphism}~\cite{TODO}.
For example, below we compare universally quantified
propositions to dependent function types, and existentially
propositions to dependent pair types.
$$
\forall x.~ \mrm{P}(x) \approx (x : \Var{A}) \arr \Fun{P}~\Var{x}
$$
$$
\exists x.~ \mrm{Q}(x) \approx \Data{Σ}~\Var{A}~(\lambda~\Var{x} \arr \Fun{Q}~\Var{x})
$$

\paragraph{Motivation}
To extend fully generic programming over a limited collection of types
to all possible types of a depdently typed language.

\section{A Taste of Fully Generic Programming}\label{sec:fullyeg}

\section{Class of Supported Datatypes}\label{sec:algclass}

\section{Thesis \& Contributions}\label{sec:thesis}



