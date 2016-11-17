\AgdaHide{
\begin{code}
open import Data.Bool
open import Data.Product hiding ( map )
module _ where
\end{code}}

\section{Types}
In programming languages, a \textit{type} is a construct used to capture the
notion of a collection of \textit{values}.
A primary motivation of types is the ability to assign them to the
inputs and output of a function, thereby allowing the function to
only consider sensible values.
For example, below the \AgdaFun{concat} function assumes that
it receives a list of lists and flattens it to a single list.

\AgdaHide{
\begin{code}
module _ where
 private
  data List (A : Set) : Set where
    nil : List A
    cons : A → List A → List A
  postulate append : ∀{A} → List A → List A → List A
\end{code}}

\begin{code}
  concat : ∀{A} → List (List A) → List A
  concat nil = nil
  concat (cons xs xss) = append xs (concat xss)
\end{code}

Because the outer list always contains a sublist, the \AgdaCon{cons}
case can assume that its first argument is a list that can be
\AgdaFun{append}ed to the recursive call.

\subsection{Open Types}

We call an \textit{open type} any type whose definition mentions the type
of types (\AgdaData{Set}). For example, the type of parametrically
polymorphic lists takes a \AgdaData{Set} as its parameter.

\begin{code}
data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A
\end{code}

Another example is the type of heterogenous lists, which are lists
containing values of possibly distinct types. The
\AgdaCon{cons} constructor of heterogenous lists takes a
\AgdaData{Set} as an implicit argument, indicating the type of the
value that the list is being extended by.

\AgdaHide{
\begin{code}
module HList where
\end{code}}

\begin{code}
  data HList : Set₁ where
    nil : HList
    cons : {A : Set} → A → HList → HList
\end{code}

We call these \textit{open types} because their collection of values
not only includes types that are currently defined, but also all types
that may be defined in the future.
Many useful functions can be defined over open types, such as the
parametrically polymorphic \AgdaFun{concat} above, and the
heterogenous \AgdaFun{append} below.

\begin{code}
  append : HList → HList → HList
  append nil ys = nil
  append (cons x xs) ys = cons x (append xs ys)
\end{code}

We can define \AgdaFun{append} for both parametric and heterogenous
lists. However, all functions over open types
must treat \AgdaData{Set} arguments abstractly. Therefore, we cannot
define a function like \AgdaData{concat} for heterogenous lists
because we can never be sure if the first value of a
\AgdaCon{cons} is an \AgdaData{HList} or a value of some other type.

\subsection{Closed Types}

\AgdaHide{
\begin{code}
module ClosedType where
\end{code}}

We call a \textit{closed type} any type whose definition does not mention
\AgdaData{Set}. For example, the type of bits (lists specialized to
only contain booleans).

\begin{code}
  Bits : Set
  Bits = List Bool
\end{code}

Functions over closed types may behave \textit{differently} depending
on \textit{any} value within the type. For example, below the
\AgdaFun{all} function returns true if all bits are true.

\begin{code}
  all : Bits → Bool
  all nil = true
  all (cons false xs) = false
  all (cons true xs) = all xs
\end{code}

The \AgdaFun{all} function makes a decision based on the boolean value
contained in the first argument of \AgdaCon{cons}. In contrast, a function over an open
\AgdaData{HList} cannot make such a decision. If a
function over an \AgdaData{HList} did make a decision based on which
\AgdaData{Set} was passed in, it would only be able to consider all
types currently defined, not any type definable in the future.

\subsection{Spectrum of Open Types}

\AgdaHide{
\begin{code}
module Spectrum where
\end{code}}

While a closed type makes no reference to \AgdaData{Set} in its
definition, certain open types may refer to \AgdaData{Set} more than
others. We can imagine a spectrum of
open and closed datatypes. Informally, we
might order datatypes in the spectrum by counting the occurrences of
\AgdaData{Set} in the datatype definitions.
For example, consider the type of binary trees whose branches may
contain a value of two possibly distinct types.

\begin{code}
  data Tree (A B : Set) : Set where
    leaf : Tree A B
    branch₁ : A → Tree A B → Tree A B → Tree A B
    branch₂ : B → Tree A B → Tree A B → Tree A B
\end{code}

Specializing \AgdaData{List} \AgdaVar{A} to \AgdaData{List}
\AgdaData{Bool} turns it from open to closed. In contrast, partially
specializing \AgdaData{Tree} \AgdaVar{A} \AgdaVar{B} to
\AgdaData{Tree} \AgdaData{Bool} \AgdaVar{B} turns it from
more open to less open (two references to \AgdaData{Set} versus one).

Formally, we order datatypes in the spectrum is
by the number of values that we can make decisions about.
We can make a decision
about a function by applying it to a value, and we can make a
decision about an inductive value by pattern matching against
it. However, we cannot make a decision about a \AgdaData{Set}
because we cannot pattern match against it.
\footnote{Any collection of pattern matching clauses for currently
defined \AgdaData{Set}s becomes partial as soon as another
datatype is defined in the future.}

More generally, our open versus closed spectrum is actually ordering
abstract versus concrete datatypes. However, this thesis only
considers \AgdaData{Set} arguments as a means of creating abstract types,
so in our context abstract can be identified with open, and concrete
can be identified with closed.
\footnote{The more general spectrum could also include
definitions given as abstract datatypes (ADTs). An abstract datatype
exports an interface to its values and operations, but we cannot make
any decisions about their concrete implementations.}

The act of defining an inductive datatype pushes
us closer to the closed side of the spectrum, because we can make
decisions by pattern matching on the constructors of the new
type. However, the arguments of the constructors of an open type may
contain \AgdaData{Set}s that we may \textit{not} inspect. As we
replace \AgdaData{Set}s with specialized types, we move even closer
towards the closed side of the spectrum.
One end of the spectrum includes closed types, which allow
functions to make decisions about all of their values. The other end of
the spectrum includes \textit{fully} open types, which do \textit{not} allow
functions to make decisions about any of their values.
In our setting the only fully open type is \AgdaData{Set} itself, as
demonstrated by the unique inhabitant of the identity function (there
are no decisions to be made). 

\begin{code}
  id : {A : Set} → A → A
  id a = a
\end{code}

