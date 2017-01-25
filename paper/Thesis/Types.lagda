\AgdaHide{
\begin{code}
module _ where
\end{code}}

\section{Types}\label{sec:types}

In programming languages, a \textit{type} is a construct used to capture the
notion of a collection of \textit{values}.
In this section we introduce many different properties of types so
that we may precisely describe types in future parts of this thesis.
As the primary motivation of a functional programming language is
writing functions, we also accompany datatype definitions with example
functions operating over said types.

\subsection{Function Types}

Dependently typed functional languages include dependent functions
as a primitive. The codomain of a dependent function type may
dependent on a value of its domain.
$$
(\AgdaVar{a} : \AgdaFun{A}) → \AgdaFun{B}~\AgdaVar{a}
$$

Values of function types are lambda expressions, for example the lambda
expression in the body of the identify function (\AgdaVar{id}) below.

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\begin{code}
  id : (A : Set) → A → A
  id = λ A → λ a → a
\end{code}


\subsection{Non-Inductive Types}\label{sec:nonind}

A \textit{non-inductive} type is any type that is not recursively
defined.
A type can have one or more constructors used to introduce its
values. The definition of a non-inductive type does
not mention itself in the types of any of the arguments to its
constructors.

Functions are an example of a non-inductive type,
because the domain and codomain of a $\lambda$ does not
recursively mention the function type.
Booleans are another example, because the \AgdaCon{true} and
\AgdaCon{false} constructors do not have arguments.
Below is the type of booleans, defined with the negation function
\AgdaFun{not} as an example.

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

A non-trivial example is the ``maybe'' type specialized to
booleans (\AgdaData{MaybeBool}).
The \AgdaCon{just} constructor has an argument, but its type is
\AgdaData{Bool} rather than the type being defined
(\AgdaData{MaybeBool}).

\begin{code}
  data MaybeBool : Set where
    nothing : MaybeBool
    just : Bool → MaybeBool
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

An alternative definition of an inductive type is a collection of
values closed under certain value constructors (e.g. \AgdaData{ℕ} as
\AgdaCon{zero} closed under \AgdaCon{suc}).

\subsection{Parameterized Types}\label{sec:param}

A \textit{parameterized} type is a collection of types, parameterized
by some type \AgdaVar{A}, such that the collection is
uniformly defined for each of its types regardless of what \AgdaVar{A}
is.

For example, below the type of disjoin unions (\AgdaData{⊎}) is
\textit{non-dependent}, \textit{non-inductive}, and parameterized by two types
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

  case : {A B C : Set} → A ⊎ B → (A → C) → (B → C) → C
  case (inj₁ a) f g = f a
  case (inj₂ b) f g = g b
\end{code}

Dependent pairs (\AgdaData{Σ}) are another example.
They are \textit{dependent},
\textit{non-inductive}, and parameterized by a type \AgdaVar{A} and a function
type \AgdaVar{B} (whose domain is \AgdaVar{A} and codomain is
\AgdaData{Set}). We define the type of dependents pairs along with
its dependent projections.

\begin{code}
  data Σ (A : Set) (B : A → Set) : Set where
    _,_ : (a : A) (b : B a) → Σ A B

  proj₁ : ∀{A B} → Σ A B → A
  proj₁ (a , b) = a

  proj₂ : ∀{A B} (ab : Σ A B) → B (proj₁ ab)
  proj₂ (a , b) = b
\end{code}

A third example is the type of polymorphic lists.
They are \textit{non-dependent}, \textit{inductive}, and
parameterized by some type \AgdaVar{A}.
The example function
\AgdaFun{append} combines two lists into a single list.

\begin{code}
  data List (A : Set) : Set where
    nil : List A
    cons : A → List A → List A

  append : ∀{A} → List A → List A → List A
  append nil ys = ys
  append (cons x xs) ys = cons x (append xs ys)
\end{code}


\subsection{Indexed Types}\label{sec:indx}

\AgdaHide{
\begin{code}
module _ where
 open import Data.Bool
 open import Data.Nat
 open import Function
 private
\end{code}}

An \textit{indexed} type is a collection of types, indexed
by some type \AgdaVar{I}, such that each type in the collection may
vary for any particular value of \AgdaVar{I}.
For example, the type of vectors (\AgdaData{Vec}), or length-indexed
lists. 
Vectors are \textit{indexed} by a natural number \AgdaVar{n}
(representing their length) and also \textit{parameterized} by some
type \AgdaVar{A}.

\begin{code}
  data Vec (A : Set) : ℕ → Set where
    nil : Vec A zero
    cons : ∀{n} → A → Vec A n → Vec A (suc n)
\end{code}

Below we encode the 2-length vector of booleans \texttt{[true,false]}
and the 3-length vector of natural numbers \texttt{[1,2,3]}
using \AgdaData{Vec}.

\begin{code}
  bits : Vec Bool 2
  bits = cons true (cons false nil)

  nums : Vec ℕ 3
  nums = cons 1 (cons 2 (cons 3 nil))
\end{code}

The example function
\AgdaFun{append} ensures that the length of the output vector is the
sum of the lengths of the input vectors.

\begin{code}
  append : ∀{A n m} → Vec A n → Vec A m → Vec A (n + m)
  append nil ys = ys
  append (cons x xs) ys = cons x (append xs ys)
\end{code}

\AgdaHide{
\begin{code}
module _ where
 open import Data.Bool
 open import Data.Nat
 open import Function
 private
\end{code}}

Another example is the type of finite sets (\AgdaData{Fin}), indexed by
the natural numbers. For each natural number \AgdaVar{n}, the type
\AgdaData{Fin} \AgdaVar{n} represents the subset of natural numbers
from 1 to \AgdaVar{n}.
\footnote{
  Note that the finite set \AgdaData{Fin}~\AgdaNum{0} is
  uninhabited, as the subset of natural numbers from 1 to 0 does not
  make sense.
}

\begin{code}
  data Fin : ℕ → Set where
    here : ∀{n} → Fin (suc n)
    there : ∀{n} → Fin n → Fin (suc n)
\end{code}

The type \AgdaData{Fin}~\AgdaNum{3} encodes the finite set
\texttt{\{1,2,3\}}. Below we construct the numbers 1, 2, and 3 as
values of the \AgdaData{Fin}~\AgdaNum{3} type.

\begin{code}
  one : Fin 3
  one = here

  two : Fin 3
  two = there here

  three : Fin 3
  three = there (there here)
\end{code}

Our example function using finite sets, named \AgdaFun{prod}, computes
the product of a list of \AgdaVar{n} natural numbers. However, we
represent a list of numbers as a function from \AgdaData{Fin}
\AgdaVar{n} to \AgdaData{ℕ}. The idea is that each member of the
finite set maps to a number (a member of our ``list'').
For example, the list \texttt{[1,2,3]} is represented as
the function below.
\footnote{
  Technically this is a length-3 vector rather than a list. However,
  \AgdaFun{prod} also takes a natural number argument, and a dependent
  pair consisting of a number \AgdaVar{n} and a vector of length
  \AgdaVar{n} is isomorphic to a list. See
  \refsec{derived} on derived types for more discussion.
  }

\begin{code}
  nums : Fin 3 → ℕ
  nums here = 1
  nums (there here) = 2
  nums (there (there here)) = 3
  nums (there (there (there ())))
\end{code}

Once again, \AgdaFun{prod} takes this functional list representation
as an input and returns the the mathematical product of all members of
the ``list''. 

The base case
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

Hence, \AgdaFun{prod} applied to \AgdaNum{3} and \AgdaFun{nums}
produces \AgdaNum{6}. This is the result of reducing the expression
$1\cdot1\cdot2\cdot3$. Note that the first 1 is from the
\AgdaCon{zero} case of \AgdaFun{prod}, and the second 1 is the first
element of \AgdaFun{nums}.

\subsection{Type Families}

A \textit{type family} is a collection of types, represented as a
function from some domain \AgdaVar{A} to the codomain \AgdaData{Set}.
$$
\AgdaVar{A} → \AgdaData{Set}
$$

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 private
  postulate
\end{code}}

\noindent
Any parameterized datatype is a type family, for example the type of
lists.

\begin{code}
   List : Set → Set
\end{code}

\noindent
Any indexed type is also a type family, for example the type of vectors.

\begin{code}
   Vec : Set → ℕ → Set
\end{code}

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open import Data.Product
 private
  postulate
\end{code}}

\noindent
Although the type of vectors contains two arguments rather than one,
it is isomorphic to an uncurried version with a single argument:

\begin{code}
   Vec : Set × ℕ → Set
\end{code}

\subsection{Derived Types}\label{sec:derived}

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

An \textit{indexed type} can be derived as a function by
\textit{computing} an appropriate existing type from its index.
This is because the type former of an indexed type (such as the type of
vectors or finite sets) is a function.

For example, we can derive the indexed type of vectors of length
\AgdaVar{n} as a right-nested tuple of pairs containing \AgdaVar{n} values of
type \AgdaVar{A}. Each occurrence of \AgdaVar{A} represents a
\AgdaFun{cons}). The tuple terminates in the unit type,
representing \AgdaFun{nil}.

\begin{code}
  Vec : Set → ℕ → Set
  Vec A zero = ⊤
  Vec A (suc n) = A × Vec A n

  nil : ∀{A} → Vec A zero
  nil = tt

  cons : ∀{A n} → A → Vec A n → Vec A (suc n)
  cons x xs = x , xs
\end{code}

As another example, consider the type of finite sets.
The finite set type can be derived as a right-nested tuple of disjoint unions of
unit types, ending with a bottom type (\AgdaVar{⊥}, the type without
any constructors). This makes sense because the finite set of zero
elements is uninhabited, and the finite set of any other number
\AgdaVar{n} offers a choice (of \AgdaCon{here}s and \AgdaCon{there}s)
to index any subnumber of \AgdaVar{n}. Here ``choice'' is interpreted
as disjoint union.

\begin{code}
  Fin : ℕ → Set
  Fin zero = ⊥
  Fin (suc n) = ⊤ ⊎ Fin n

  here : ∀{n} → Fin (suc n)
  here = inj₁ tt

  there : ∀{n} → Fin n → Fin (suc n)
  there p = inj₂ p
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

Besides deriving vectors as a function whose type is \textit{computed}
from its index, we can also derive the type of vectors as a
\textit{constant} function.
Vectors are a special case of a class of datatypes called
\textit{containers}~\ref{TODO}, which are functions from datatype
positions to contained values. Below, the type of vectors is
represented as a
\textit{constant} function (i.e. one that does not vary for \AgdaVar{n})
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
\refsec{indx} the ``list'' argument to \AgdaFun{prod} was actually
this functional vector representation, so it could have been written like:

\AgdaHide{
\begin{code}
  postulate
\end{code}}

\begin{code}
   prod : (n : ℕ) (f : Vec ℕ n) → ℕ
\end{code}

Finally, we can derive \textit{non-indexed} types from indexed types by using a
\textit{dependent pair}. The dependent pair acts like an existential, where the
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

The first component is zero for the \AgdaCon{nil} constructor. For
the \AgdaCon{cons} constuctor, the first component is the successor
of the natural number \AgdaVar{n} contained within the list being
extended (the second argument to \AgdaCon{cons}) represented as a
pair.

\subsection{Infinitary Types}

\AgdaHide{
\begin{code}
module _ where
 open import Data.List
 private
\end{code}}

An \textit{infinitary} type is an inductive type where at least one
constructor has one function argument whose codomain is the type being
defined. The domain can never be the
type being defined, because negative datatypes~\ref{TODO} make type
theory inconsistent.
Consider the type of rose trees, containing values in node positions
and allowing each node to have any finite number of branches.

\begin{code}
  data Rose (A : Set) : Set where
    rose : A → List (Rose A) → Rose A
\end{code}

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open import Data.Fin
 open import Data.Product
 private
\end{code}}

Now recall the derived definitions of vectors and lists from
\refsec{derived}.

\begin{code}
  Vec : Set → ℕ → Set
  Vec A n = Fin n → A

  List : Set → Set
  List A = Σ ℕ (λ n → Vec A n)
\end{code}

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open import Data.Fin
 private
\end{code}}

If we expand this derived definition of lists (and the inner derived
definition of vectors) in the definition of \AgdaData{Rose} above,
we arrive at an alternative but isomorphic definition of rose trees.

\begin{code}
  data Rose (A : Set) : Set where
    rose : A → (n : ℕ) (f : Fin n → Rose A) → Rose A
\end{code}

Our new definition of rose trees is an example of an infinitary type,
as it contains an argument (\AgdaVar{f}) whose domain is a finite set but whose
codomain is the type being defined (\AgdaData{Rose}).

\subsection{Inductive-Recursive Types}\label{sec:irtypes}

\AgdaHide{
\begin{code}
module _ where
 open import Data.Product
 open import Data.Nat
 open import Data.Fin
 open import Data.Vec hiding ( sum )
 private
  postulate sum prod : (n : ℕ) (f : Fin n → ℕ) → ℕ
\end{code}}

An \textit{inductive-recursive} type is a collection of values
mutually defined with a function parameterized by said type.
An example of an inductive-recursive type is the type of arithmetic
expressions \AgdaData{Arith}.
Values of type \AgdaData{Arith} encode ``Big Pi''
mathematical arithmetic product equations up to some finite
bound, such as the one below.
\begin{equation*}
  \prod_{i=1}^{3} i
\end{equation*}

The intuition is that this expression should evaluate to something
(the number 6 in this case). The mutually defined function is
exactly the evaluation function.
The type is defined as follows.

\begin{code}
  mutual
    data Arith : Set where
      Num : ℕ → Arith
      Prod : (a : Arith) (f : Fin (eval a) → Arith) → Arith
  
    eval : Arith → ℕ
    eval (Num n) = n
    eval (Prod a f) = prod (eval a) (λ a → eval (f a))
\end{code}

A literal number is represented using the \AgdaCon{Num} constructor,
evaluating to said number. A mathematical product is represented using
the \AgdaCon{Prod} constructor, where the first argument \AgdaVar{a}
is the upper bound of the product as an arithmetic expression (3 in
the example above), and the
second argument \AgdaVar{f} is the
body of the product ($i$ in the example above)
as a functional representation of a vector of arithmetic
expressions. Note that \AgdaData{Arith} is also an
\textit{infinitary type}, as the codomain of \AgdaVar{f} is
\AgdaData{Arith}. 

The length of the vector (the argument to \AgdaData{Fin} in the type
of \AgdaVar{f})
should be the \AgdaFun{eval}uation of the of the upper bound
\AgdaVar{a}. Hence, the evaluation function \AgdaFun{eval} must be mutually defined
with the type \AgdaData{Arith}. The \AgdaCon{Prod} constructor
evaluates to the product computed with our \AgdaFun{prod} function
from \refsec{indx}.
We can represent the mathematical equation given earlier as follows.

\AgdaHide{
\begin{code}
    num : ∀ {n} → Fin n → ℕ
    num zero = suc zero
    num (suc i) = suc (num i)
\end{code}}

\begin{code}
    six : Arith
    six = Prod (Num 3) (λ i → Num (num i))
\end{code}

The result of applying \AgdaFun{eval} to the inductive-recursive
(\AgdaData{Arith})
equation \AgdaFun{six}
is the natural number \AgdaNum{6}.
An \AgdaData{Arith} equation may be nested in its upper bound
(\AgdaVar{a}) or body (codomain of \AgdaVar{f}), but the lower
bound is always 1.
Note that above we define the expression \AgdaFun{six} with the helper function
\AgdaFun{num}, which converts the finite set value \AgdaVar{i} to a natural number
using one-based indexing. 

A more typical example of an inductive-recursive type is a
\textit{universe} modeling a dependently typed language, which we will
see in \refsec{closedu}.

\subsection{Algebraic Types}

An \textit{algebraic} type is a type defined as the fixpoint of a suitable
algebra. Although this fixpoint construction is not given directly,
it is the semantics of types defined using \AgdaKeyword{data}
declarations. For example, the inductive type of lists is defined as the
fixpoint below.
\begin{equation*}
\rm{List} \triangleq \lambda A. ~\mu X. ~1 + A \cdot X
\end{equation*}

In the equation, X is used to ask for recursive arguments (such as
the second argument to \AgdaData{cons}).
A non-inductive type like booleans can also be defined by ignoring
X.
\begin{equation*}
\rm{Bool} \triangleq \mu X. ~1 + 1
\end{equation*}

We would like to emphasize that this definition of booleans
corresponds to the semantics of defining \AgdaData{Bool} using a
\AgdaKeyword{data} declaration (as in \refsec{nonind}). 
Although it looks
syntatically similar to the \textit{derived} definition of booleans
using unit and disjoint union in \refsec{derived}, that derived
definition is \textit{not} algebraic because it is not defined with
$\mu$ (either syntatically or semantically).
However, some derived types \textit{can} be algebraic if we
internalize $\mu$ as a type former \AgdaData{μ} (as in
\refsec{TODO}), and use this type former to derive type definitions.
In the scope of this thesis, an algebraic type is one defined using
a \AgdaKeyword{data} declaration, a \AgdaData{μ} type former, or a
\AgdaData{W} type former (introduced in \refsec{wtypes}). Although
\AgdaData{W} types are not syntatically fixpoint constructions, they
are semantically very similar so we still call them algebraic.

Finally, below is an example of an indexed type defined algebraically. The
index is given as a lambda argument (\AgdaVar{n}) just like the
parameter (\AgdaVar{A}). However, the \AgdaCon{nil} and \AgdaCon{cons}
constructor must appropriately constrain the index argument (to zero
or the successor of the previous vector respectively). Additionally,
the recursive argument X takes the index as an argument. 
\begin{equation*}
\rm{Vec} \triangleq \lambda A. ~\lambda n. ~\mu X. ~(n=\rm{zero}) +
((m : \mathbb{N}) \cdot A \cdot X~m \cdot n=\rm{suc}~m)
\end{equation*}

Notice that
in \AgdaCon{cons} the index of the previous vector is given as an
explicit argument (m), and the index (n) is constrained to be the
successor of that argument.

%% TODO Constrained Families

\subsection{Computational Families}\label{sec:compu}

A \textit{computational family} is an indexed type defined by computing
over its index. We have already seen a non-algebraic computational
family, namely the derived type of vectors from \refsec{derived}.

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
  Vec : Set → ℕ → Set
  Vec A zero = ⊤
  Vec A (suc n) = A × Vec A n
\end{code}

However, computational families can also be algebraic. In the previous
section, vectors are algebraically defined by constraining the input
index given as a lambda argument.
As a computational algebraic family,
we case-analyze the lambda index argument to determine the algebra
that we take the fixpoint of rather than constraining the
input.
\begin{singlespace}
\begin{align*}
\rm{Vec} &\triangleq \lambda A. ~\lambda n. ~\mu X. ~\rm{\textbf{case}}~n~\rm{\textbf{of}}\\
\rm{zero} &\mapsto 1\\
\rm{suc}~n &\mapsto A \cdot X~n
\end{align*}
\end{singlespace}

Agda does not currently support a high-level syntax (like
\AgdaKeyword{data}) for defining computational algebraic
families. Nonetheless, we semantically model them using an internalized \AgdaData{μ} type
former in \refsec{TODO}.

\subsection{Open Types}\label{sec:open}

An \textit{open} type is any type whose definition mentions the type
of types (\AgdaData{Set}). In an \textit{open type theory} datatype
declarations add new types to the language, extending \AgdaData{Set}
with additional type formers. Therefore the collection of type formers
(values of type \AgdaData{Set}) is considered to be ``open''.
Consequently, open languages must prohibit case
analysis over \AgdaData{Set}, because a total function matching against
currently defined types becomes partial when a new datatype is
declared.
One example of an open datatype is the type of heterogenous lists
(\AgdaData{HList}).

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\begin{code}
  data HList : Set₁ where
    nil : HList
    cons : {A : Set} → A → HList → HList

  append : HList → HList → HList
  append nil ys = nil
  append (cons x xs) ys = cons x (append xs ys)
\end{code}

\AgdaData{HList} is an open type because its
\AgdaCon{cons} constructor has an argument \AgdaVar{A} of type
\AgdaData{Set}, and an argument \AgdaVar{a} whose type is the open
type \AgdaData{A}.

The parametric lists from \refsec{param} are another example of an open
type, as the \AgdaVar{a} argument in the \AgdaCon{cons} constructor
has type \AgdaVar{A}. The type of lists parameterized by \AgdaVar{A}
is open because \AgdaCon{cons} uses \AgdaVar{A}, and \AgdaVar{A} has
type \AgdaData{Set}.

\subsection{Closed Types}\label{sec:closed}

A \textit{closed} type is any type whose definition does not mention
\AgdaData{Set}. For example, if we specialize the type of parametric
lists to booleans (as the type \AgdaFun{Bits}) the source of openess
(the parameter \AgdaVar{A} of type \AgdaData{Set}) disappears.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Bool
 private
  data List (A : Set) : Set where
    nil : List A
    cons : A → List A → List A
\end{code}}

\begin{code}
  Bits : Set
  Bits = List Bool

  all : Bits → Bool
  all nil = true
  all (cons false xs) = false
  all (cons true xs) = all xs
\end{code}


