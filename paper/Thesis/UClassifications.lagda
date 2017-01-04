\AgdaHide{
\begin{code}
open import Data.Bool
open import Data.Product hiding ( map )
module _ where
 open import Data.List hiding ( concat ; all ) renaming ( [] to nil ; _∷_ to cons )
\end{code}}

\section{Classifications of Universes}\label{sec:bitsstar}

A \textit{universe} is a collection of \textit{types}, possibly closed
under certain type formers. Just as we accompanied types with example
functions operating over them in \refsec{types}, we accompany
universes with example \textit{generic functions} in this section. A
\textit{generic function} is any function defined over multiple types.

\subsection{Universe Model}

In a dependently typed language, a universe can be modelled as a
type of codes (representing the actual types of the universe), and a
meaning function (mapping each code to its actual type).

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

For example the \AgdaData{BitsStar} universe is comprised of the type of booleans,
lists of boolesns, lists of lists of booleans, and so on. Its type of
codes is \AgdaData{BitsStar}, and its meaning function is
\AgdaFun{⟦\_⟧}. As a convention, we prefix constructors of the code
type with a backtick to emphasize the distinction betwee a code
(e.g. \AgdaCon{`Bool}) and the actual type it denotes
(e.g. \AgdaData{Bool}).

\begin{code}
  data BitsStar : Set where
    `Bool : BitsStar
    `List : BitsStar → BitsStar
  
  ⟦_⟧ : BitsStar → Set
  ⟦ `Bool ⟧ = Bool
  ⟦ `List A ⟧ = List ⟦ A ⟧
\end{code}

Our generic function over this universe is \AgdaFun{all}, which
returns \AgdaCon{true} if all the booleans in any potential list and
nested sublists are \AgdaCon{true}.

\begin{code}
  all : (A : BitsStar) → ⟦ A ⟧ → Bool
  all `Bool b = b
  all (`List A) nil = true
  all (`List A) (cons x xs) = all A x ∧ all (`List A) xs
\end{code}

\subsection{Open Universes}\label{sec:openu}

An \textit{open} universe mentions \AgdaData{Set} in its type of
codes or meaning function. Just as open types grow their collection of
values when new types are declared, open universes grow their
collection of types when new types are declared.

An example open universe is \AgdaData{ListStarH}, the universe of all
base types closed under list formation. The ``H'' in the name stands
for ``heterogenous'', as this universe is similar to the type of
heterogenous lists (except each position contains either a heterogenous value,
or a possibly nested list containing heterogenous values).

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

%% TODO rename to DListStar
\begin{code}
  data ListStarH : Set₁ where
    `Base : Set → ListStarH
    `List : ListStarH → ListStarH
  
  ⟦_⟧ : ListStarH → Set
  ⟦ `Base A ⟧ = A
  ⟦ `List A ⟧ = List ⟦ A ⟧
\end{code}

A commmon function to define over parameterized lists is ``concat'',
which flattens a list of lists to a single list. Ordinarilly we might
define multiple versions of this function, each flattening an
increasing number of outer lists.

\AgdaHide{
\begin{code}
  data HList : Set₁ where
    nil : HList
    cons : {A : Set} → A → HList → HList
  postulate
   append : HList → HList → HList
\end{code}}

\begin{code}
   concat1 : {A : Set} → List (List A) → List A
   concat2 : {A : Set} → List (List (List A)) → List A
   concat3 : {A : Set} → List (List (List (List A))) → List A
\end{code}

Using the \AgdaData{ListStarH} universe, we can define a generic
function that flattens any number of outer lists. Of course, the
output must be a heterogenous list because the \AgdaCon{`Base} values
of the universe are heterogenous.

\begin{code}
  concat : (A : ListStarH) → ⟦ A ⟧ → HList
  concat (`Base A) x = cons x nil
  concat (`List A) nil = nil
  concat (`List A) (cons x xs) = append (concat A x) (concat (`List A) xs)
\end{code}

In the \AgdaCon{`Base} case, we cast the heterogenous value of type
\AgdaVar{A} to a single-element heterogenous list.

\subsection{Closed Universes}\label{sec:closedu}

A \textit{closed} universe does not mention \AgdaData{Set} in its type of
codes or meaning function. The \AgdaData{BitsStar} universe of
\refsec{bitsstar} is an example of a closed universe.

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

\begin{code}
  concat : (A : HListStar) → ⟦ A ⟧ → HList
  concat `HList xs = xs
  concat (`List A) nil = nil
  concat (`List A) (cons x xs) = append (concat A x) (concat (`List A) xs)
\end{code}

For completeness, above is the generic \AgdaFun{concat} for
\AgdaData{HListStar}. The \AgdaCon{`Base} case need not cast its
result to a heterogenous list, as the base case
values of this universe are already heterogenous lists.

\subsection{Inductive Universes}

We call a universe \textit{inductive} if its type are closed over one
or more type formers. For example, the \AgdaData{BitsStar},
\AgdaData{ListStarH}, and \AgdaData{HListStar} universes above are
inductive because they are closed under \AgdaData{List} formation (via
the inductive \AgdaCon{`List} code constructor).

\subsection{Non-Inductive Universes}

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


\subsection{Subordinate Universes}

A universe is \textit{subordinate} if one of its types contains a
nested type that is not a member of the universe. Hence, a universe is
subordinate if one of its types has a constructor with an argument whose
type is not a member of the universe.

For example, the open \AgdaData{HListStar} universe from
\refsec{closedu} is subordinate because it contains \AgdaData{HList},
which has a \AgdaData{Set} argument in the \AgdaCon{cons} constructor,
and \AgdaData{Set} is not a member of \AgdaData{HListStar}.

\subsection{Autonomous Universes}

A universe is \textit{autonomous} if all nested types of its types
are also types in the universe. Hence, the type of every argument to
every constructor of a universe type must also be a type in the
universe.

For example, the closed \AgdaData{BitsStar} universe of \refsec{bitsstar} is
closed because \AgdaCon{Bool} does not have constructor arguments,
and because the universe is closed under \AgdaData{List} formation
(thus any sublist only contains types also in the universe).

Note that open universes can be autonomous. For example,
\AgdaData{ListStarH} from \refsec{openu} includes all types
\AgdaVar{A} (of type \AgdaData{Set}) via the \AgdaCon{`Base}
constructor. Regardless of any other types in the universe,
\AgdaData{ListStarH} is autonomous because any type can be injected
using \AgdaCon{`Base}.

\subsection{Type Families as Universes}\label{sec:famu}

Recall from \refsec{bitsstar} that a universe is modelled as a type of
codes \textit{and} a meaning function. Therefore, a value in this
universe can be captured as a dependent pair, where the first
component specifies the code and the second component specifies the
type returned by the meaning function applied to the first component.
For example, we might refer to values of the \AgdaData{BitsStar}
universe (rather than just codes) as follows. 

\AgdaHide{
\begin{code}
module _ where
 private
  data BitsStar : Set where
    `Bool : BitsStar
    `List : BitsStar → BitsStar
  
  ⟦_⟧ : BitsStar → Set
  ⟦ `Bool ⟧ = Bool
  ⟦ `List A ⟧ = List ⟦ A ⟧
\end{code}}

\begin{code}
  BitsStarU : Set
  BitsStarU = Σ BitsStar ⟦_⟧

  bits₁ : BitsStarU
  bits₁ = `List `Bool , cons true (cons false nil)

  bits₂ : BitsStarU
  bits₂ = `List (`List `Bool) , cons (cons true nil) (cons (cons false nil) nil)
\end{code}

Thus far we have constructed universes with certain properties from
scratch. However, we can also turn any \textit{type family} into a
universe by considering the type of its indices the codes and the type
family itself the meaning function. If we do this for the indexed type of
finite sets (\AgdaData{Fin}), we get a universe (\AgdaFun{Pow}) like powerset but
without the empty set.

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

We can use the same method to transform the parameterized type of lists
into a type of \textit{dynamic} lists
(\AgdaFun{DList}). A dynamic list may contain values
of any type, but the type must be shared by all values.

\begin{code}
  DList : Set₁
  DList = Σ Set List

  blist : DList
  blist = Bool , cons true (cons false nil)

  nlist : DList
  nlist = ℕ , cons 1 (cons 2 nil)
\end{code}

\subsection{Parameterized Universes}

A \textit{parameterized} universe is a collection of universes, parameterized
by some type \AgdaVar{A}, such that the collection is
uniformly defined for each universe regardless of what \AgdaVar{A} is.

The model of a parameterized universe depends on its parameter
in its codes, meaning function, or both. Recall
\AgdaData{BitsStar} (\refsec{bitsstar}) and
\AgdaData{HListStar} (\refsec{bitsstar}), universe closed under list
formation with booleans and heterogenous lists as base types
respectively. Our example parameterized universe abstracts out the
base type as a parameter.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 private
  postulate append : {A : Set} → List A → List A → List A
\end{code}}

\begin{code}
  data ListStar : Set where
    `Param : ListStar
    `List : ListStar → ListStar
  
  ⟦_⟧ : ListStar → Set → Set
  ⟦ `Param ⟧ X = X
  ⟦ `List A ⟧ X = List (⟦ A ⟧ X)
\end{code}

The \AgdaCon{`Param} code represents the parameterized type, and is
interpreted as the second argument to the meaning function.
To more easily see how this is a ``parameterized'' universe, we give the type
of the universe as a dependent pair below.

\begin{code}
  ListStarU : Set → Set
  ListStarU X = Σ ListStar (λ A → ⟦ A ⟧ X)

  bits₁ : ListStarU Bool
  bits₁ = `List `Param , cons true (cons false nil)

  bits₂ : ListStarU Bool
  bits₂ = `List (`List `Param) , cons (cons true nil) (cons (cons false nil) nil)
\end{code}


We can still write \AgdaFun{concat}, by injecting values of the
parameterized type into a singleton list as with \AgdaData{DListStar}
(\refsec{openu}). The type signature of \AgdaFun{concat} for
\AgdaData{ListStar} tells us more than \AgdaFun{concat} for
\AgdaData{DListStar}, as the output is a list containing values whose type
is the parameter \AgdaVar{X} (rather than an arbitary \AgdaData{HList}).

\begin{code}
  concat : ∀{X} (A : ListStar) → ⟦ A ⟧ X → List X
  concat `Param x = cons x nil
  concat (`List A) nil = nil
  concat (`List A) (cons x xs) = append (concat A x) (concat (`List A) xs)
\end{code}

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 private
  postulate append : {A : Set} → List A → List A → List A
  data ListStar : Set where
    `Param : ListStar
    `List : ListStar → ListStar
  
  ⟦_⟧ : ListStar → Set → Set
  ⟦ `Param ⟧ X = X
  ⟦ `List A ⟧ X = List (⟦ A ⟧ X)
\end{code}}

\begin{code}
  DListStarU : Set₁
  DListStarU = Σ (ListStar × Set) (λ { (A , X) → ⟦ A ⟧ X })

  bits₁ : DListStarU
  bits₁ = (`List `Param , Bool) , cons true (cons false nil)

  bits₂ : DListStarU
  bits₂ = (`List (`List `Param) , Bool) , cons (cons true nil) (cons (cons false nil) nil)
\end{code}


%% List A = Pair Nat (Vec A)
