\AgdaHide{
\begin{code}
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Bool
open import Data.Nat
open import Data.List
open import Data.Fin hiding ( _+_ ; _<_ )
open import Data.Vec hiding ( lookup )
open import Relation.Binary.PropositionalEquality
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
levels. The combination of total programming at the type level and a
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
\forall x.~ \mrm{P}(x) \approx (\Var{x} : \Var{A}) \arr \Fun{P}~\Var{x}
$$
$$
\exists x.~ \mrm{Q}(x) \approx \Data{Σ}~\Var{A}~(\lambda~\Var{x} \arr \Fun{Q}~\Var{x})
$$

  \AgdaHide{
\begin{code}
module _ {A : Set} where
 private
  postulate
\end{code}}

Thanks to the Curry-Howard Isomorphism, we can encode logical
\textit{preconditions} and \textit{postconditions} at the type level.
For example, below
we give the type for a \Fun{lookup} function for lists with a
\textit{precondition} constraining the natural number (\Var{n}) index
to be less than the length of the list (\Var{xs}) being looked
up. This allows an otherwise partial lookup function to be defined
totally by preventing out-of-bounds indexing.

\begin{code}
   lookup : (n : ℕ) (xs : List A) → n < length xs → A
\end{code}

As another example, we give the type for an \Fun{append} function over lists with
a \textit{postcondition} constraining the length of the output list
(\Var{zs}) to be equal to the sum of the lengths of the input lists
(\Var{xs} and \Var{ys}).

\begin{code}
   append : (xs ys : List A) → Σ (List A) (λ zs → length zs ≡ length xs + length ys)
\end{code}

The types of \Fun{append} and \Fun{lookup} correspond to the following
two logical propositions respectively.
$$
\forall n, xs.~ n < \card{xs} \imp \exists x
$$
$$
\forall xs, ys.~ \exists zs.~ \card{zs} = \card{xs} + \card{ys}
$$

\paragraph{Motivation}
To extend fully generic programming over a limited collection of types
to all possible types of a depdently typed language.

\section{A Taste of Fully Generic Programming}\label{sec:fullyeg}

\section{Class of Supported Datatypes}\label{sec:algclass}

\paragraph{Algebraic Types}

Like \Data{List}

\AgdaHide{
\begin{code}
module _ {A : Set} where
 private
  postulate
\end{code}}

\begin{code}
   lookup : (n : ℕ) (xs : List A) → n < length xs → A
   append : (xs ys : List A) → Σ (List A) (λ zs → length zs ≡ length xs + length ys)
\end{code}

\paragraph{Indexed Types}

The less-than (\AgdaData{<}) precondition and equality
(\AgdaData{≡}) postcondition in the examples above are examples of the
type-theory equivalents of the logical notion of \textit{relations},
named \textit{indexed types}. Rather than constraining a datatype like
lists using relations after-the-fact, we can create more specific
variants of lists that encoded certain properties before-the-fact.
For example, the type of vectors (\Data{Vec}) is like a length-indexed
version of lists. Compared to lists, the type former of vectors gains
an additional natural number parameter constraining its length.

\AgdaHide{
\begin{code}
module _ {A : Set} where
 private
  postulate
\end{code}}

\begin{code}
   lookup : (n : ℕ) (xs : Vec A n) (i : Fin n) → A
   append : (m n : ℕ) (xs : Vec A m) (ys : Vec A n) → Vec A (m + n)
\end{code}


\section{Thesis \& Contributions}\label{sec:thesis}



