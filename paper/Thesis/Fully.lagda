\AgdaHide{
\begin{code}
open import Data.Empty
open import Data.Unit
open import Data.Bool hiding ( not )
open import Data.Product
module _ where
\end{code}}

\section{Abstractness \& Concreteness}\label{sec:abscon}

In this section we define additional non-standard terminology for
types and universes, namely \textit{abstractness} and
\textit{concreteness}. We cover these properties here rather than in
\refsec{types} on types and \refsec{universes} on universes because
the terminology (as it is used) and our emphasis on it is unique to
this thesis.

\subsection{Abstract Types}\label{sec:abstract}

An \textit{abstract} type is any type that does not have an
elimination principle. For example, \textit{open} types (\refsec{open})
mentioning \AgdaData{Set} are abstract because you cannot pattern
match on values of \AgdaData{Set}
(or otherwise eliminate \AgdaData{Set}).

Types mentioning \AgdaData{Level}
(used to indicate which level in a hierarchy a type inhabits)
are also abstract.
Once again, Agda types are arranged in a hierarchy, where
base types are classified by \AgdaData{Set0}, kinds are classified by
\AgdaData{Set1}, superkinds are classified by \AgdaData{Set2}, and so
on. Rather than defining different datatypes inhabiting each of these
levels, we can define a single datatype that can be instantiated at
any level.

\AgdaHide{
\begin{code}
module _ where
 open import Level
 private
\end{code}}

In the example below, we define parameterized lists that can be
instantiated at any level in the type hierarchy.
The definition also enforces the constraint that a list
must inhabit the same level as its type parameter.

\begin{code}
  data List {ℓ : Level} (A : Set ℓ) : Set ℓ where
    nil : List A
    cons : A → List A → List A
\end{code}

Just like \AgdaData{Set}, Agda does not expose an elimination
principle for \AgdaData{Level} (thus you cannot, for example, pattern
match on levels in a function definition).\footnote{
  Nevertheless, we can write parametrically
  level-polymorphic functions over \AgdaData{List} as in
  \refsec{levelpoly}.
}

\subsection{Concrete Types}\label{sec:concrete}

A \textit{concrete} type is any type that does have an elimination
principle. For the purpose of this thesis, this will mean any type
that does not mention \AgdaData{Set} or \AgdaData{Level}.
Therefore, concrete types have the special properties that all of its
values and subvalues may be eliminated. Algebraic datatypes are
concrete and they may be eliminated by pattern matching.
Function types are
concrete and they may be eliminated by application.

\subsection{Abstract Data Types}\label{sec:adt}

This thesis does not consider abstract data types (ADT's), but we
touch upon them briefly here to relate them to our terminology of
abstract and concrete types.

An ADT allows the user to expose a type
former, constructors, and elimination principles while hiding their
implementation. For example, a dictionary may be exposed as a list of
key/value pairs but internally be implemented as a balanced binary
search tree. Therefore, an ADT defined to expose its type former and
constructors, but not its elimination principle, is \textit{abstract}
by our definition. However, if such an ADT also exposed its elimination
principle we would call it \textit{concrete} (despite the fact that
the ADT would be hiding its true implementation).

\subsection{Fully Generic Programming}\label{sec:fullygeneric}

We call a universe abstract if at least one of the types it contains is
abstract. We call a universe concrete if all of the types it contains
are concrete.
This brings us to the primary ambition of this thesis, which we call
\textit{fully generic programming}.
A fully generic function is a special kind of ad hoc polymorphic
function by coercion (\refsec{coercion}) with the additional property
that the universe is concrete. By consequence, fully generic functions
can eliminate any value or subvalue and recurse on any code or
interpretation.

\AgdaHide{
\begin{code}
module _ where
 open import Data.List hiding ( concat ) renaming ( [] to nil ; _∷_ to cons )
 private
  data BoolStar : Set where
    `Bool : BoolStar
    `List : BoolStar → BoolStar
  
  ⟦_⟧ : BoolStar → Set
  ⟦ `Bool ⟧ = Bool
  ⟦ `List A ⟧ = List ⟦ A ⟧
\end{code}}

For example, the \AgdaData{BoolStar} universe
(\refsec{umodel}) allows us to define
\AgdaFun{nor} as a fully generic function
(returning \AgdaCon{true} if all values and subvalues contain
\AgdaCon{false}).

\begin{code}
  nor : (A : BoolStar) → ⟦ A ⟧ → Bool
  nor `Bool true = false
  nor `Bool false = true
  nor (`List A) nil = true
  nor (`List A) (cons x xs) = nor A x ∧ nor (`List A) xs
\end{code}

In addition to making recursive calls on codes and interpretations
(thanks to an algebraic, inductive, and autonomous universe)
for the \AgdaCon{`List} cases, we can also pattern match
on all [sub]codes and all [sub]values (thanks to concreteness). Compare this
to \AgdaFun{concat} for \AgdaData{DynStar} in \refsec{coercion}. The
\AgdaFun{concat} function cannot pattern match on the interpretation
of the \AgdaCon{`Dyn}
base case because the type is \AgdaData{Set} (the source of
abstractness). By contrast, \AgdaFun{nor} can match on the
interpretation of \AgdaCon{`Bool} by distinguishing between
\AgdaCon{true} and \AgdaCon{false} (because \AgdaData{Bool} is a
concrete type).


