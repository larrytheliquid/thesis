\AgdaHide{
\begin{code}
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product
module _ where
 data List {ℓ} (A : Set ℓ) : Set ℓ where
   nil : List A
   cons : A → List A → List A
\end{code}}

\section{Parametric Polymorphism}

A \textit{parametrically polymorphic} function is defined uniformly
over its codes and their meanings. That is, the function does not inspect the
type of codes and therefore does not behave differently for any code
or its \textit{interpretation} (i.e. it does not behave differently for
different values in the type returned by the meaning function applied
to a code).

\subsection{Parametric over Types}

A common form of parametric polymorphism is over types, i.e. where
\AgdaFun{Code} is defined to be \AgdaData{Set}.

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\begin{code}
  append : {A : Set} → List A → List A → List A
  append nil ys = ys
  append (cons x xs) ys = cons x (append xs ys)
\end{code}

Notice that \AgdaFun{append} over lists behaves the same way for any
type \AgdaVar{A} it gets applied to.

\subsection{Parametric over Levels}\label{sec:levelpoly}

Functions can also be defined parametrically over universe
\AgdaData{Level}s. Types in Agda are arranged in a hierarchy, where
base types are classified by \AgdaData{Set0}, kinds are classified by
\AgdaData{Set1}, superkinds are classified by \AgdaData{Set2}, and so
on. Rather than defining different functions operating over types in
each of these levels, we can define a single function level-polymorphically.

\AgdaHide{
\begin{code}
module _ where
 open import Level
 private
\end{code}}

\begin{code}
  append : {ℓ : Level} {A : Set ℓ} → List A → List A → List A
  append nil ys = ys
  append (cons x xs) ys = cons x (append xs ys)
\end{code}

Note that \AgdaFun{append} now behaves the same way for
any type at any level that it is applied to.

\section{Ad hoc Polymorphism}

An \textit{ad hoc polymorphic} function is defined non-uniformly
over its codes or their meanings. That is, the function may inspect
codes and its interpretation (the values in the type returned by the
meaning function applied to a code).

\subsection{Ad hoc by Overloading}

If the type of \AgdaFun{Code}s for our universe is \textit{algebraic} and
\textit{non-inductive}, then generic functions over the universe amount to a
kind of syntactic overloading of function names.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 private
  data Truthy : Set where
    `Bool `ℕ `Bits : Truthy
  
  ⟦_⟧ : Truthy → Set
  ⟦ `Bool ⟧ = Bool
  ⟦ `ℕ ⟧ = ℕ
  ⟦ `Bits ⟧ = List Bool
\end{code}}

For example, consider the \AgdaFun{isTrue} function from
\refsec{noninductive} over the \AgdaData{Truthy} universe.
Before defining \AgdaFun{isTrue} for the
universe, we can define versions of the function for each type in the
universe. 

\begin{code}
  isTrueBool : Bool → Bool
  isTrueBool b = b

  isTrueℕ : ℕ → Bool
  isTrueℕ zero = false
  isTrueℕ (suc n) = true

  isTrueBits : List Bool → Bool
  isTrueBits nil = true
  isTrueBits (cons false xs) = false
  isTrueBits (cons true xs) = isTrueBits xs
\end{code}

Now can define \AgdaFun{isTrue} by matching on
each type code, and returning the appropriate function specialized to
that type.

\begin{code}
  isTrue : (A : Truthy) → ⟦ A ⟧ → Bool
  isTrue `Bool = isTrueBool
  isTrue `ℕ = isTrueℕ
  isTrue `Bits = isTrueBits
\end{code}

Another way to say this is that we can make recursive calls on
interpretations, but not codes. For example, below we inline the
specialized functions as is done in \refsec{noninductive}.
The \AgdaCon{`Bits} cases make recursive calls on inductive values,
but the codes stay constant in recursive calls.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 private
  data Truthy : Set where
    `Bool `ℕ `Bits : Truthy
  
  ⟦_⟧ : Truthy → Set
  ⟦ `Bool ⟧ = Bool
  ⟦ `ℕ ⟧ = ℕ
  ⟦ `Bits ⟧ = List Bool
\end{code}}

\begin{code}
  isTrue : (A : Truthy) → ⟦ A ⟧ → Bool
  isTrue `Bool b = b
  isTrue `ℕ zero = false
  isTrue `ℕ (suc n) = true
  isTrue `Bits nil = true
  isTrue `Bits (cons false xs) = false
  isTrue `Bits (cons true xs) = isTrue `Bits xs
\end{code}


\subsection{Ad hoc by Coercion}\label{sec:coercion}

If the type of \AgdaFun{Code}s for our universe is
\textit{algebraic}, \textit{inductive}, and \textit{autonomous},
then generic functions over the universe can make recursive
calls on both codes and their interpretions. Because we can make recursive
calls on types of our universe, we can effectively
\textit{coerce} recursive values of our universe to an appropriate
output type.

For example, consider the \AgdaFun{concat} function from
\refsec{openu} over the \AgdaData{DynStar} universe. Each value and
subvalue of this dynamic Kleene star universe can be coerced to a
dynamic list.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 private
  data DynStar : Set₁ where
    `Dyn : Set → DynStar
    `List : DynStar → DynStar
  
  ⟦_⟧ : DynStar → Set
  ⟦ `Dyn A ⟧ = A
  ⟦ `List A ⟧ = List ⟦ A ⟧
  Dyn : (A : DynStar) → Set
  Dyn (`Dyn A) = A
  Dyn (`List A) = Dyn A
  postulate
   append : {A : Set} → List A → List A → List A
\end{code}}

\begin{code}
  concat : (A : DynStar) → ⟦ A ⟧ → List (Dyn A)
  concat (`Dyn A) x = cons x nil
  concat (`List A) nil = nil
  concat (`List A) (cons x xs) = append (concat A x) (concat (`List A) xs)
\end{code}

\subsection{Ad hoc by Overloading \& Coercion}

Ad hoc polymorphic functions may also be a hybrid of
the overloading and coercion styles.
For example, if universe \AgdaFun{Code}s are
\textit{algebraic}, \textit{inductive}, and \textit{subordinate} then
we can recurse on the codes and interpretations for the autonmous
types in the universe (coercion), but can only recurse on
the interpretations of the subordinate types (overloading).
For example, consider the \AgdaFun{all} function for the
\AgdaData{BitsStar} universe of \refsec{subord}.

\AgdaHide{
\begin{code}
module _ where
 private
  data BitsStar : Set where
    `Bits : BitsStar
    `List : BitsStar → BitsStar
  
  ⟦_⟧ : BitsStar → Set
  ⟦ `Bits ⟧ = List Bool
  ⟦ `List A ⟧ = List ⟦ A ⟧
\end{code}}

\begin{code}
  all : (A : BitsStar) → ⟦ A ⟧ → Bool
  all `Bits nil = true
  all `Bits (cons false xs) = false
  all `Bits (cons true xs) = all `Bits xs
  all (`List A) nil = true
  all (`List A) (cons x xs) = all A x ∧ all (`List A) xs
\end{code}

The \AgdaCon{`Bits} cases only recurse over the interpretation
(keeping the code constant), hence they are defined by overloading.
The \AgdaCon{`List} cases recurse both
over the codes and the interpretation, hence they are defined by
coercion.


