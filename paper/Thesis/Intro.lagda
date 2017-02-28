\AgdaHide{
\begin{code}
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Bool
open import Data.Nat
open import Data.List renaming ( [] to nil ; _∷_ to cons )
open import Data.Fin hiding ( _+_ ; _<_ )
open import Data.Vec hiding ( lookup )
open import Relation.Binary.PropositionalEquality
module _ where
\end{code}}

\section{Dependently Typed Languages \& Motivation}\label{sec:deplang}

A standard dependently typed language is
\textit{purely functional} (meaning the absence of side effects),
\textit{total}
(meaning all inductively defined functions
terminate and cover all possible inputs), and has a
type system that captures the notion of \textit{dependency}.

\subsection{Curry-Howard Isomorphism}

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

\subsection{Indexed Types}

The less-than (\AgdaData{<}) precondition and equality
(\AgdaData{≡}) postcondition in the examples above
are \textit{relations} in the language of logic,
and are called \textit{indexed types} in the language of dependent
types.
Rather than constraining a datatype like
lists using relations after-the-fact, we can create
more specific (i.e. \textit{indexed})
variants of datatypes that encode certain
properties before-the-fact.

\AgdaHide{
\begin{code}
module _ {A : Set} where
 private
  postulate
\end{code}}

For example, the type of vectors (\Data{Vec} \Var{A} \Var{n})
is like a length-indexed version of lists. Compared to lists, the type
former of vectors gains an additional natural number parameter (\Var{n})
constraining its length. Because the property of of lengths of vectors
is encoded at the type level, we can write a variant of \Fun{append}
where calls to \Fun{length} have been replaced by an index.

\begin{code}
   append : (m n : ℕ) (xs : Vec A m) (ys : Vec A n) → Vec A (m + n)
\end{code}

Additionally, the explicit equality proof
(\Data{≡}) postcondition can be dropped in favor of expressing the
postcondition directly in the index position of the output vector.
In other words, the \textit{explicit} equality postcondition has been
dropped in favor of an \textit{implicit} property about the codomain
of \Fun{append}.

Another example of an indexed type is the type of finite sets
(\Data{Fin} \Var{n}), indexed by a natural number constraining
the size of the finite set. A finite set
is like a subset of the of the natural numbers from 0 to \Var{n} - 1. 
This subset property
(whose maximum value is \Var{n} - 1) is the perfect datatype to act as
an \textit{implicit} version of the \textit{explicit} less-than
(\Data{<}) precondition of \Fun{lookup}. Hence, we can rewrite an
implicit-precondition version of \Fun{lookup} using vectors and finite sets
as follows.

\begin{code}
   lookup : (n : ℕ) (xs : Vec A n) (i : Fin n) → A
\end{code}

\subsection{Motivation}

Programmers of non-dependently typed languages already struggle with the
issue of needing to define logically similar versions of functions
(like \Fun{count}, \Fun{lookup}, \Fun{update}, etc.)
for their various algebraic types
(e.g. natural numbers, lists, binary trees, etc.).
This problem is more pronounced in a dependently typed language, where
programmers also define indexed variants of types
(e.g. finite sets, vectors, balanced binary trees, etc.)
to implicitly capture preconditions and postconditions.

Rather than punishing programmers for creating new datatypes,
our \textbf{motivation} is to reward them with
\textit{fully generic functions}
(like \Fun{count}, \Fun{lookup}, \Fun{update}, etc.), which are new
mechanisms for \textit{code reuse}.
Fully generic functions are predefined once-and-for-all to work with
any datatype of the language, whether it is defined now or will be
defined in the future.
Programmers defining new types should be able to \textit{apply} fully generic
functions to them, and programmers should also be able to
\textit{define} fully generic functions themselves.

\section{A Taste of Fully Generic Programming}\label{sec:fullyeg}

Ordinary generic programming in dependently typed languages is
accomplished using a construction known as a universe
(\refsec{universes}). Rather than explaining how universes work in
detail (which we do in \refsec{universes}) in this introduction,
we develop our dependently typed Agda examples using
universes in parallel with examples in Haskell using
type classes~\ref{TODO}. Later we learn why our analogy with Haskell
type classes makes sense, as
\textit{ad hoc polymorphism} (\refsec{adhoc}) is a
form of generic programming.

Below we first develop the \Fun{size} function using generic
programming, and then develop the \Fun{count} function using
\textit{fully} generic programming
(albeit over a fixed and small language),
both described in the introduction (\refsec{intro}).

\subsection{Generic Programming}

Recall that \Fun{size} should return the sum of
\textit{all nodes traversed} by recursing into the \textit{inductive} ones.

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\begin{code}
  data Size : Set₁ where
    `Bool : Size
    `Pair : (A B : Set) → Size
    `List : (A : Set) → Size

  ⟦_⟧ : Size → Set
  ⟦ `Bool ⟧ = Bool
  ⟦ `Pair A B ⟧ = A × B
  ⟦ `List A ⟧ = List A

  size : (A : Size) → ⟦ A ⟧ → ℕ
  size `Bool b = 1
  size (`Pair A B) (a , b) = 3
  size (`List A) nil = 1
  size (`List A) (cons x xs) = 2 + size (`List A) xs
\end{code}

\subsection{Fully Generic Programming}

Recall that \Fun{count} should return the sum of
\textit{all nodes} by
recursing into the \textit{inductive} and
\textit{non-inductive} ones.

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\begin{code}
  data Count : Set where
    `Bool : Count
    `Pair : (A B : Count) → Count
    `List : (A : Count) → Count

  ⟦_⟧ : Count → Set
  ⟦ `Bool ⟧ = Bool
  ⟦ `Pair A B ⟧ = ⟦ A ⟧ × ⟦ B ⟧
  ⟦ `List A ⟧ = List ⟦ A ⟧

  count : (A : Count) → ⟦ A ⟧ → ℕ
  count `Bool b = 1
  count (`Pair A B) (a , b) = 1 + count A a + count B b
  count (`List A) nil = 1
  count (`List A) (cons x xs) = 1 + count A x + count (`List A) xs
\end{code}

\section{Class of Supported Datatypes}\label{sec:algclass}

\subsection{Algebraic Types}

\subsection{Indexed Types}

\section{Thesis \& Contributions}\label{sec:thesis}



