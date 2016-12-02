\AgdaHide{
\begin{code}
module _ where
\end{code}}

\section{Classifications of Types}

In programming languages, a \textit{type} is a construct used to capture the
notion of a collection of \textit{values}.
In this section we introduce many different properties of types so
that we may precisely describe types in future parts of this thesis.
As the primary motivation of a functional programming language is
writing functions, we also accompany datatype definitions with example
functions operating over said types.

\subsection{Function Types}

Dependently typed functional languages include dependent functions
as a primitive. Below we define the type former \AgdaFun{Π}
as a type synonym for function types. This type former is occasionally
used in later parts of the thesis (because its application is syntactially similar
to the application of the dependent pair type former \AgdaData{Σ}), but mostly we
use Agda's primitive syntax for forming function types (demonstrated
below in the definition of the \AgdaFun{Π} type former and in the type of the
identify function \AgdaFun{id}).

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\begin{code}
  Π : (A : Set) (B : A → Set) → Set
  Π A B = (a : A) → B a

  id : {A : Set} → A → A
  id a = a
\end{code}


\subsection{Non-Inductive Types}

A \textit{non-inductive} type is any type that is not recursively
defined. In particular, the definition of a non-inductive type does
not mention itself in the types of any of the arguments to its
constructors. Functions are one example of non-inductive types,
and booleans are another (defined with the negation function
\AgdaFun{not} as an example).

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\begin{code}
  data Bool : Set where
    false true : Bool

  not : Bool → Bool
  not false = true
  not true = false
\end{code}

An even simpler example is the unit type, which only has a
single constructor without any arguments.

\begin{code}
  data ⊤ : Set where
    tt : ⊤
\end{code}


\subsection{Inductive Types}

An \textit{inductive} type mentions itself in its definition. That is,
at least one constructor has one argument whose type is the type being
defined. For example, below is the type of natural numbers (defined
with the addition function \AgdaFun{+} as an example). The
successor constructor of the type of natural
numbers takes a natural number argument, making it inductive.

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\begin{code}
  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

  _+_ : ℕ → ℕ → ℕ
  zero + m = m
  suc n + m = suc (n + m)
\end{code}

\subsection{Parameterized Types}

A \textit{parameterized} type is a collection of types, parameterized
by some type \AgdaVar{A}, such that the collection is
uniformly defined for each of its types regardless of what \AgdaVar{A}
is. For example, below the type of disjoin unions (\AgdaData{⊎}) is
non-dependent, non-inductive, and parameterized by two types
\AgdaVar{A} and \AgdaVar{B}. We define the type of disjoint unions
along with a function to \AgdaFun{case}-analyze them.

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\begin{code}
  data _⊎_ (A B : Set) : Set where
    inj₁ : A → A ⊎ B
    inj₂ : B → A ⊎ B

  case : {A B C : Set} → A ⊎ B → C → C → C
  case (inj₁ a) ca cb = ca
  case (inj₂ b) ca cb = cb
\end{code}

Dependent pairs (\AgdaData{Σ}) are another example, albeit dependent, also
non-inductive, and parameterized by a type \AgdaVar{A} and a function
type \AgdaVar{B} (whose domain is \AgdaVar{A} and codomain is
\AgdaData{Set}). We define the type of dependents product along with
its dependent projections.

\begin{code}
  data Σ (A : Set) (B : A → Set) : Set where
    _,_ : (a : A) (b : B a) → Σ A B

  proj₁ : ∀{A B} → Σ A B → A
  proj₁ (a , b) = a

  proj₂ : ∀{A B} (ab : Σ A B) → B (proj₁ ab)
  proj₂ (a , b) = b
\end{code}

A third example, this time inductive, is the type of polymorphic lists
parameterized by some type \AgdaVar{A}. The example function
\AgdaFun{append} combines two lists into a single list.

\begin{code}
  data List (A : Set) : Set where
    nil : List A
    cons : A → List A → List A

  append : ∀{A} → List A → List A → List A
  append nil ys = ys
  append (cons x xs) ys = cons x (append xs ys)
\end{code}


\subsection{Indexed Types}\label{sec:prod}

An \textit{indexed} type is a collection of types, indexed
by some type \AgdaVar{I}, such that each type in the collection may
vary for any particular value of \AgdaVar{I}.
One example is the type of finite sets (\AgdaData{Fin}), indexed by
the natural numbers. For each natural number \AgdaVar{n}, the type
\AgdaData{Fin} \AgdaVar{n} represents the subset of natural numbers
from zero to \AgdaVar{n} minus one.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open import Function
 private
\end{code}}

\begin{code}
  data Fin : ℕ → Set where
    here : ∀{n} → Fin (suc n)
    there : ∀{n} → Fin n → Fin (suc n)
\end{code}

The example function \AgdaFun{prod} below computes the product of a
list of \AgdaVar{n} natural numbers (represented as a function
from \AgdaData{Fin} \AgdaVar{n} to \AgdaData{ℕ}). The base case
represents the empty list, for which we return the number one (the
identify of the product operation).
The recursive case multiplies the current number at the
head position of the list (accessed by applying \AgdaVar{f} to the
\AgdaCon{here} constructor of finite sets) with the recursive call on the tail of the
list (we compute the tail of a list represented as a function by
composing the function with the \AgdaCon{there} constructor of finite
sets). 

\begin{code}
  prod : (n : ℕ) (f : Fin n → ℕ) → ℕ
  prod zero f = suc zero
  prod (suc n) f = f here * prod n (f ∘ there)
\end{code}

Another classic indexed datatype is vectors. Vectors are parameterized
by some type \AgdaVar{A}, indexed by a natural number \AgdaVar{n},
and represents lists of length \AgdaVar{n}. The example function
\AgdaFun{append} ensures that the length of the output vector is the
sum of the lengths of the input vectors.

\begin{code}
  data Vec (A : Set) : ℕ → Set where
    nil : Vec A zero
    cons : ∀{n} → A → Vec A n → Vec A (suc n)

  append : ∀{A n m} → Vec A n → Vec A m → Vec A (n + m)
  append nil ys = ys
  append (cons x xs) ys = cons x (append xs ys)
\end{code}

\subsection{Derived Types}

Thus far we have only seen \textit{primitive} types. The type of
functions already existed as a primitive in the language. We defined
each other type using a \AgdaKeyword{data}type
declaration, extending our language with a new primitive type.
Alternatively, many types can be \textit{derived} from existing
types. A derived datatype should be isomorphic to the type we have in
mind. Rather than writing a function for each derived type, we derive
its constructors as examples of how the derived type is used.
For example, we can drive the type of booleans as the disjoint
union of two unit types.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Empty
 open import Data.Unit
 open import Data.Sum
 open import Data.Product
 open import Data.Nat
 private
\end{code}}

\begin{code}
  Bool : Set
  Bool = ⊤ ⊎ ⊤

  false : Bool
  false = inj₁ tt

  true : Bool
  true = inj₂ tt
\end{code}

Notice that the type former of an indexed type (such as the type of
finite sets) is a function. Thus, we can derive an indexed type by
\textit{computing} the appropriate type for the input index. For example, the
type of finite sets can be derived as a right-nested tuple of disjoint unions of
unit types, ending with a bottom type (\AgdaVar{⊥}, the type without
any constructors). This makes sense because the finite set of zero
elements should be uninhabited, and the finite set of any other number
\AgdaVar{n} should offer a choice up to that number (representing a
subset of natural numbers bounded by \AgdaVar{n} minus one).

\begin{code}
  Fin : ℕ → Set
  Fin zero = ⊥
  Fin (suc n) = ⊤ ⊎ Fin n

  here : ∀{n} → Fin (suc n)
  here = inj₁ tt

  there : ∀{n} → Fin n → Fin (suc n)
  there p = inj₂ p
\end{code}

Similarly, we can derive the indexed type of vectors of length
\AgdaVar{n} as a right-nested tuple of pairs containing \AgdaVar{n} values of
type \AgdaVar{A} (each \AgdaVar{A} instance represents a \AgdaFun{cons}),
ending in the type of unit (representing \AgdaFun{nil}).

\begin{code}
  Vec : Set → ℕ → Set
  Vec A zero = ⊤
  Vec A (suc n) = A × Vec A n

  nil : ∀{A} → Vec A zero
  nil = tt

  cons : ∀{A n} → A → Vec A n → Vec A (suc n)
  cons x xs = x , xs
\end{code}

\AgdaHide{
\begin{code}
module _ where
 open import Data.Empty
 open import Data.Unit
 open import Data.Sum
 open import Data.Product
 open import Data.Nat
 open import Data.Fin renaming ( zero to here ; suc to there )
 private
\end{code}}

Vectors are a special case of a class of datatypes called
\textit{containers}~\ref{TODO}. Because of this, we can represent a
vector as a type synonym (a constant function) rather than a
computation. Below, the type of vectors is represented as a function
whose domain is a finite set of \AgdaVar{n} elements, and whose
codomain is \AgdaVar{A}. Think of the function as an \AgdaVar{n}-ary
projection for each \AgdaVar{A} value in the vector.

\begin{code}
  Vec : Set → ℕ → Set
  Vec A n = Fin n → A

  nil : ∀{A} → Vec A zero
  nil ()

  cons : ∀{A n} → A → Vec A n → Vec A (suc n)
  cons x f here = x
  cons x f (there p) = f p
\end{code}

Above, the \AgdaFun{nil} function receives bottom (\AgdaData{⊥}) as an
argument, so we need not define it.
The \AgdaFun{cons} function ``extends'' the function
\AgdaVar{f} by returning \AgdaVar{x} if the finite set points to the
head of the vector, and otherwise calls the ``tail'' by applying
\AgdaVar{f} to the sub-index \AgdaVar{p}. Notice that in
\refsec{prod} the ``list'' argument was actually
this functional vector representation, so it could have been written like:

\AgdaHide{
\begin{code}
  postulate
\end{code}}

\begin{code}
   prod : (n : ℕ) (f : Vec ℕ n) → ℕ
\end{code}

Finally, we can derive non-indexed from indexed types by using a
dependent pair. The dependent pair acts like an existential, where the
first component is a value from the the index domain and acts as a
witness, and the second component is the indexed type former applied
to the witness and acts like a predicate. For example, we can derive
the type of lists from the type of vectors as follows.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Product
 open import Data.Nat
 open import Data.Vec renaming ([] to vnil ; _∷_ to vcons)
 private
\end{code}}

\begin{code}
  List : Set → Set
  List A = Σ ℕ (λ n → Vec A n)

  nil : {A : Set} → List A
  nil = zero , vnil

  cons : {A : Set} → A → List A → List A
  cons x (n , xs) = suc n , vcons x xs
\end{code}

The first component is zero for the \AgdaCons{nil} constructor. For
the \AgdaCons{cons} constuctor, the first component is the successor
of the natural number \AgdaVar{n} contained within the list being
extended (the second argument to \AgdaCons{cons}) represented as a
pair.
