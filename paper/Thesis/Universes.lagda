\AgdaHide{
\begin{code}
open import Data.Bool    
module Thesis.Universes where
\end{code}}

\subsection{Types}
In programming languages, a \textit{type} is a construct used to capture the
notion of a collection of \textit{values}.
A primary motivation of types is the ability to assign them to the
inputs and output of a function, thereby allowing the function to
only consider sensible values.

For example, below the \AgdaFun{reverse} function assumes that
it works over lists, because working over values of many other types
(such as trees) does not make sense.

\AgdaHide{
\begin{code}
module PList where
  data List (A : Set) : Set where
    nil : List A
    cons : A → List A → List A
  postulate append : ∀{A} → List A → List A → List A
\end{code}}

\begin{code}
  reverse : ∀{A} → List A → List A
  reverse nil = nil
  reverse (cons x xs) = append (reverse xs) (cons x nil)
\end{code}

\paragraph{Open Types}

We call an \textit{open type} any type whose definition uses the type
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
\AgdaData{Set} as an argument (which is the type of the heterogenous
value that the list is being extended by).

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
not only includes types that are currently defined, but also any type
that may be defined in the future.
Many useful functions can be defined over open types, such the
parametrically polymorphic \AgdaFun{reverse} above, and the
heterogenous \AgdaFun{reverse} below.

\AgdaHide{
\begin{code}
  postulate append : HList → HList → HList
\end{code}}

\begin{code}
  reverse : HList → HList
  reverse nil = nil
  reverse (cons x xs) = append (reverse xs) (cons x nil)
\end{code}

In a sense, functions over open types are \textit{generic} with
respect to any concrete \AgdaData{Set} that the open type may be
instantiated with. In fact, the functions must work the
\textit{same way} for any concrete \AgdaData{Set}.
\footnote{In open type theories, there is no way to case-analyze
  values of \AgdaData{Set}, so functions cannot make decisions based
  on which concrete \AgdaData{Set} appears.}

\paragraph{Closed Types}

\AgdaHide{
\begin{code}
module Closed where
\end{code}}

We call a \textit{closed type} any type whose definition does not use 
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
contained in each \AgdaCon{cons}. In contrast, a function over an open
\AgdaData{HList} would not be able to make such a decision. If a
function over an \AgdaData{HList} did make a decision based on which
\AgdaData{Set} was passed in, it would only be able to consider all
types currently defined, not any type definable in the future.

\paragraph{Spectrum of Open and Closed Types}

\AgdaHide{
\begin{code}
module Spectrum where
\end{code}}

While a closed type makes no reference to \AgdaData{Set} in its
definition, certain open types may refer to \AgdaData{Set} more than
others. In other words, we can imagine a spectrum of datatypes ordered
according how how many times their definition refers to
\AgdaData{Set}.

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
specializing \AgdaData{Tree} \AgdaData{Bool} \AgdaVar{B} turns it from
open to less open.

%% When we create a type, we
%% usually have particular properties in mind that values in the
%% collection adhere to.

%% idea of an open or closed type / collection of values
%% closed is all values defined by the type
%% closed List specialized to Nat


%% A function can be given a type to restrict 
%% The motivation behind types is the ability to write functions

%% that can
%% assume certain properties about its inputs to consume and output to
%% produce. 

%% to constrain functions to only operate on values

%% In a programming languages, a type captures the notion of a particular
%% collection of values.

%% The idea behind universes is to capture the notion of a collection of
%% datatypes as a first class entity in our programming language.
