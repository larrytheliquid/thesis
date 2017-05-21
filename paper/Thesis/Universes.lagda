\AgdaHide{
\begin{code}
open import Data.Bool
open import Data.Product hiding ( map )
module _ where
open import Data.List hiding ( concat ; all ) renaming ( [] to nil ; _∷_ to cons )
\end{code}}

\section{Universes}\label{sec:universes}

A \textit{universe} is a collection of \textit{types}, possibly closed
under certain type formers. Just as we accompanied types with example
functions operating over them in \refsec{types}, we accompany
universes with example \textit{generic functions} in this section. A
\textit{generic function} is any function defined over multiple types.

\subsection{Universe Model}\label{sec:umodel}

In a dependently typed language, a universe can be modeled as a
type of codes (\textit{representing} the actual types of the universe), and a
meaning function (mapping each code to its actual type).

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

For example the \AgdaData{BoolStar} universe is comprised of the type of booleans,
lists of booleans, lists of lists of booleans, and so on.
In other words, it is the Kleene star version of \AgdaData{Bits}
(non-nested lists of booleans) from \refsec{closedt}.
The type of codes is \AgdaData{BoolStar}, and its meaning function is
\AgdaFun{⟦\_⟧}. As a convention, we prefix constructors of the code
type with a backtick to emphasize the distinction between a code
(e.g. \AgdaCon{`Bool}) and the actual type it denotes
(e.g. \AgdaData{Bool}).

\begin{code}
  data BoolStar : Set where
    `Bool : BoolStar
    `List : BoolStar → BoolStar
  
  ⟦_⟧ : BoolStar → Set
  ⟦ `Bool ⟧ = Bool
  ⟦ `List A ⟧ = List ⟦ A ⟧
\end{code}

To get the actual universe type, apply the dependent pair type
former (\AgdaData{Σ}) to the codes and meaning function. Therefore,
values of the universe are dependent pairs whose first component is
a code and second component is a value (the type of the value is the
meaning function applied to the code).

\begin{code}
  BoolStarU : Set
  BoolStarU = Σ BoolStar ⟦_⟧
\end{code}

As a convention, we append the letter \AgdaFun{U} to the type of codes
to define the universe type.
Our first example member of this universe represents the list of
booleans \texttt{[true, false]}.

\begin{code}
  bits₁ : BoolStarU
  bits₁ = `List `Bool , cons true (cons false nil)
\end{code}

Our second example universe value represents the list of lists of
booleans \texttt{[[true], [false]]}.

\begin{code}
  bits₂ : BoolStarU
  bits₂ = `List (`List `Bool) , cons (cons true nil) (cons (cons false nil) nil)
\end{code}

Our example generic function over this universe is \AgdaFun{all}, which
returns \AgdaCon{true} if all the booleans in any potential list and
nested sublists are \AgdaCon{true}.

\begin{code}
  all : (A : BoolStar) → ⟦ A ⟧ → Bool
  all `Bool b = b
  all (`List A) nil = true
  all (`List A) (cons x xs) = all A x ∧ all (`List A) xs
\end{code}

\subsection{Open Universes}\label{sec:openu}

An \textit{open} universe mentions \AgdaData{Set} in its type of
codes or meaning function. Just as open types grow their collection of
values when new types are declared, open universes grow their
collection of types when new types are declared.

An example open universe is \AgdaData{DynStar}, the universe of
dynamic lists closed under list formation.
A dynamic list may contain values
of any type, but the type must be shared by all values.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 private
\end{code}}

\begin{code}
  data DynStar : Set₁ where
    `Dyn : Set → DynStar
    `List : DynStar → DynStar
  
  ⟦_⟧ : DynStar → Set
  ⟦ `Dyn A ⟧ = A
  ⟦ `List A ⟧ = List ⟦ A ⟧
\end{code}

Again, we can encode the actual Kleene star of dynamic types
universe (rather than just its codes or meaning function) using a
dependent pair.

\begin{code}
  DynStarU : Set₁
  DynStarU = Σ DynStar ⟦_⟧
\end{code}

In our first example, we represent the list of booleans
\texttt{[true, false]}. The \AgdaCon{`Dyn} part of the first component
of the pair indicates the type of values contained in our list, namely
\AgdaData{Bool}.

\begin{code}
  bits₁ : DynStarU
  bits₁ = `List (`Dyn Bool) , cons true (cons false nil)
\end{code}

Our second example represents the list of lists of
natural numbers \texttt{[[1], [2]]}. This time,
\AgdaCon{`Dyn} is applied to the type of natural numbers
(\AgdaData{ℕ}).

\begin{code}
  nums₂ : DynStarU
  nums₂ = `List (`List (`Dyn ℕ)) , cons (cons 1 nil) (cons (cons 2 nil) nil)
\end{code}

A common function to define over parameterized lists is ``concat'',
which flattens a list of lists to a single list. Ordinarily we might
define multiple versions of this function, each flattening an
increasing number of outer lists.

\AgdaHide{
\begin{code}
  postulate
   append : {A : Set} → List A → List A → List A
\end{code}}

\begin{code}
   concat1 : {A : Set} → List (List A) → List A
   concat2 : {A : Set} → List (List (List A)) → List A
   concat3 : {A : Set} → List (List (List (List A))) → List A
\end{code}

Using the \AgdaData{DynStar} universe, we can define a generic
\AgdaFun{concat} function that flattens any number of outer lists.
The return type of this function should be a \AgdaData{List} of
\AgdaVar{A}s, where \AgdaVar{A} is the dynamic type for the dynamic
lists to be flattened. Thus, we first define a function \AgdaFun{Dyn} to
extract the dynamic type from a \AgdaData{DynStar} code by recursing
down to the base case \AgdaCon{`Dyn}.

\begin{code}
  Dyn : (A : DynStar) → Set
  Dyn (`Dyn A) = A
  Dyn (`List A) = Dyn A
\end{code}

Note that \AgdaFun{Dyn} is a \textit{computational family}
(\refsec{compu}). Later in the thesis we introduce more specific
terminology, calling \AgdaFun{Dyn} a
\textit{computational argument family} (\refsec{comparg})
that serves as a \textit{domain supplement} (\refsec{domsup}).
Having defined \AgdaFun{Dyn}, we can define a generic
\AgdaFun{concat} function to return a flattened list of dynamic universe
values. 

\begin{code}
  concat : (A : DynStar) → ⟦ A ⟧ → List (Dyn A)
  concat (`Dyn A) x = cons x nil
  concat (`List A) nil = nil
  concat (`List A) (cons x xs) = append (concat A x) (concat (`List A) xs)
\end{code}

Note that a dynamic \AgdaCon{`Dyn} value is flattened by turning it
into a single-element list.

\subsection{Closed Universes}\label{sec:closedu}

A \textit{closed} universe does not mention \AgdaData{Set} in its type of
codes or meaning function. The \AgdaData{BoolStar} universe of
\refsec{umodel} is an example of a closed universe.

As an edge case, consider the universe (\AgdaData{HListStar}) of
heterogenous lists closed under list formation below.

\AgdaHide{
\begin{code}
module _ where
 private
  data HList : Set₁ where
   nil : HList
   cons : {A : Set} → A → HList → HList
  postulate append : HList → HList → HList
\end{code}}

\begin{code}
  data HListStar : Set where
    `HList : HListStar
    `List : HListStar → HListStar
  
  ⟦_⟧ : HListStar → Set₁
  ⟦ `HList ⟧ = HList
  ⟦ `List A ⟧ = List ⟦ A ⟧
\end{code}

Even though \AgdaData{HListStar} does not mention \AgdaData{Set}
\textit{directly} in its codes or meaning function, it does mention it
\textit{indirectly} because the \AgdaCon{`HList} code maps to the open
type \AgdaData{HList} (which mentions \AgdaData{Set}). Therefore,
the \AgdaData{HListStar} universe is \textit{open}!

\subsection{Inductive Universes}\label{sec:indu}

We call a universe \textit{inductive} if its types are closed over one
or more type formers. For example, the \AgdaData{BoolStar},
\AgdaData{DynStar}, and \AgdaData{HListStar} universes above are
inductive because they are closed under \AgdaData{List} formation (via
the inductive \AgdaCon{`List} code constructor).

\subsection{Non-Inductive Universes}\label{sec:noninductive}

A universe is \textit{non-inductive} if its types are not closed under
any type formers. For example, the \AgdaData{Truthy} universe
below represents types that we want to consider as boolean
conditional values.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 private
\end{code}}

\begin{code}
  data Truthy : Set where
    `Bool `ℕ `Bits : Truthy
  
  ⟦_⟧ : Truthy → Set
  ⟦ `Bool ⟧ = Bool
  ⟦ `ℕ ⟧ = ℕ
  ⟦ `Bits ⟧ = List Bool
\end{code}

Below we define the \AgdaData{isTrue} operation, allowing us to
consider any value of the universe as being true or false.

\begin{code}
  isTrue : (A : Truthy) → ⟦ A ⟧ → Bool
  isTrue `Bool b = b
  isTrue `ℕ zero = false
  isTrue `ℕ (suc n) = true
  isTrue `Bits nil = true
  isTrue `Bits (cons false xs) = false
  isTrue `Bits (cons true xs) = isTrue `Bits xs
\end{code}


\subsection{Subordinate Universes}\label{sec:subord}

A universe is \textit{subordinate} if one of its types contains a
nested type that is not a member of the universe. Hence, a universe is
subordinate if one of its types has a constructor with an argument whose
type is not a member of the universe.

For example, the open \AgdaData{HListStar} universe from
\refsec{closedu} is subordinate because it contains \AgdaData{HList},
which has a \AgdaData{Set} argument in the \AgdaCon{cons} constructor,
and \AgdaData{Set} is not a member of \AgdaData{HListStar}.

Closed universes can be subordinate too, for example the universe
\AgdaData{BitsStar} contains lists of booleans closed under list
formation. The \AgdaCon{`Bits} values of this universe contain
booleans in \AgdaCon{cons} positions, but booleans are not
members of the universe.

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\begin{code}
  data BitsStar : Set where
    `Bits : BitsStar
    `List : BitsStar → BitsStar
  
  ⟦_⟧ : BitsStar → Set
  ⟦ `Bits ⟧ = List Bool
  ⟦ `List A ⟧ = List ⟦ A ⟧
\end{code}


\subsection{Autonomous Universes}\label{sec:autonomous}

A universe is \textit{autonomous} if all nested types of its types
are also types in the universe. Hence, the type of every argument to
every constructor of a universe type must also be a type in the
universe.

For example, the closed \AgdaData{BoolStar} universe of \refsec{umodel} is
closed because \AgdaCon{Bool} does not have constructor arguments,
and because the universe is closed under \AgdaData{List} formation
(thus any sublist only contains types also in the universe).

Note that open universes can be autonomous. For example,
\AgdaData{DynStar} from \refsec{openu} includes all types
\AgdaVar{A} (of type \AgdaData{Set}) via the \AgdaCon{`Dyn}
constructor. Regardless of any other types (such as lists) in the
universe, \AgdaData{DynStar} is autonomous because any type can be
injected using \AgdaCon{`Dyn}.

\subsection{Derived Universes}\label{sec:famu}

Thus far we have constructed universes with certain properties from
scratch, extending the \textit{primitive} types of our language with a
\textit{primitive} universe. However, we can also \textit{derive} a
universe from any \textit{type family} by
considering the type of its indices as the codes and the type
family itself as the meaning function. If we do this for the indexed type of
finite sets (\AgdaData{Fin}), we get a universe (\AgdaFun{Pow}) like powerset but
without the empty set (because \AgdaData{Fin} \AgdaCon{zero} is not inhabited).

\AgdaHide{
\begin{code}
module _ where
 open import Data.Bool
 open import Data.Nat
 open import Data.Fin renaming ( zero to here ; suc to there )
 private
\end{code}}

\begin{code}
  Pow : Set
  Pow = Σ ℕ Fin

  one₁ : Pow
  one₁ = 1 , here

  one₂ : Pow
  one₂ = 2 , here

  two₂ : Pow
  two₂ = 2 , there here
\end{code}

That is, for every natural number (each \AgdaData{ℕ} code) we get the subset of the
natural numbers from zero  to that number minus one
(the \AgdaData{Fin}ite set).

We can use the same method to derive
type of \textit{dynamic} lists (\AgdaFun{DList})
from the type of parameterized lists. Note that this is the type
of dynamic lists, rather than the Kleene star of dynamic values
(\AgdaData{DynStar} from \refsec{openu}).

\begin{code}
  DList : Set₁
  DList = Σ Set List

  bits : DList
  bits = Bool , cons true (cons false nil)

  nums : DList
  nums = ℕ , cons 1 (cons 2 nil)
\end{code}

Reflect on the fact that universes are modeled in type theory as a dependent pair
consisting of codes and a meaning function. This pair is just
another type, therefore whether we consider \AgdaFun{Pow} and
\AgdaFun{DList} to be derived types (\refsec{derived}) or derived
universes is merely a matter of perspective.

\subsection{Parameterized Universes}\label{sec:paru}

A \textit{parameterized} universe is a collection of universes, parameterized
by some type \AgdaVar{A}, such that the collection is
uniformly defined for each universe regardless of what \AgdaVar{A} is.

The model of a parameterized universe (i.e. its representation in type
theory) may depend on its parameter
in its codes, meaning function, or both. The Kleene star universes of booleans
(\AgdaData{BoolStar}), heterogenous lists (\AgdaData{HListStar}) and
bits (\AgdaData{BitsStar}) all have a similar structure, namely a
specialized base type closed under list formation.
Our example parameterized universe abstracts out the
base type as a parameter.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 private
  postulate append : {A : Set} → List A → List A → List A
\end{code}}

\begin{code}
  data ParStar : Set where
    `Par : ParStar
    `List : ParStar → ParStar
  
  ⟦_⟧ : ParStar → Set → Set
  ⟦ `Par ⟧ X = X
  ⟦ `List A ⟧ X = List (⟦ A ⟧ X)
\end{code}

The \AgdaCon{`Par} code represents the parameterized type, and is
interpreted as the second argument to the meaning function.
To more easily see how this is a ``parameterized'' universe, we give the type
of the universe as a parameterized dependent pair below.

\begin{code}
  ParStarU : Set → Set
  ParStarU X = Σ ParStar (λ A → ⟦ A ⟧ X)

  bits₁ : ParStarU Bool
  bits₁ = `List `Par , cons true (cons false nil)

  bits₂ : ParStarU Bool
  bits₂ = `List (`List `Par) , cons (cons true nil) (cons (cons false nil) nil)
\end{code}


We can still write \AgdaFun{concat} by injecting values of the
parameterized type into a singleton list as with \AgdaData{DynStar}
(\refsec{openu}). Recall that \AgdaFun{concat} for \AgdaData{DynStar}
required a special function \AgdaFun{Dyn} to extract the base
type. When defining \AgdaFun{concat} for \AgdaData{ParStar}, the base
type is already an explicit parameter that we can refer to in the
return type.

\begin{code}
  concat : ∀{X} (A : ParStar) → ⟦ A ⟧ X → List X
  concat `Par x = cons x nil
  concat (`List A) nil = nil
  concat (`List A) (cons x xs) = append (concat A x) (concat (`List A) xs)
\end{code}

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 private
  postulate append : {A : Set} → List A → List A → List A
  data ParStar : Set where
    `Par : ParStar
    `List : ParStar → ParStar
  
  ⟦_⟧ : ParStar → Set → Set
  ⟦ `Par ⟧ X = X
  ⟦ `List A ⟧ X = List (⟦ A ⟧ X)
\end{code}}

We've seen how to derive a universe from a \textit{type family}
in \refsec{famu}, but we can also derive a universe from a
\textit{universe family}. As an example, we derive the
\AgdaFun{DynStar} universe from the \AgdaData{ParStar} universe.
In \refsec{openu} we defined the type of \AgdaData{DynStar}
codes as a primitive, whereas below we derive \AgdaFun{DynStar} codes
as the pair of \AgdaData{ParStar} and \AgdaData{Set} (the parameter
type of \AgdaFun{ParStarU}).

\begin{code}
  DynStarU : Set₁
  DynStarU = Σ (ParStar × Set) (λ { (A , X) → ⟦ A ⟧ X })

  bits₁ : DynStarU
  bits₁ = (`List `Par , Bool) , cons true (cons false nil)

  bits₂ : DynStarU
  bits₂ = (`List (`List `Par) , Bool) , cons (cons true nil) (cons (cons false nil) nil)
\end{code}


%% List A = Pair Nat (Vec A)
