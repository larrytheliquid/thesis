\AgdaHide{
\begin{code}
open import Data.Bool    
open import Data.Product hiding ( map )
module Thesis.Universes where
\end{code}}

\subsection{Types}
In programming languages, a \textit{type} is a construct used to capture the
notion of a collection of \textit{values}.
A primary motivation of types is the ability to assign them to the
inputs and output of a function, thereby allowing the function to
only consider sensible values.

For example, below the \AgdaFun{concat} function assumes that
it receives a list of lists and flattens it to a single list.

\AgdaHide{
\begin{code}
module PList where
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

\paragraph{Closed Types}

\AgdaHide{
\begin{code}
module ClosedType where
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
contained in a \AgdaCon{cons}. In contrast, a function over an open
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
others. To a first approximation, we can imagine a spectrum of
datatypes ordered according how how many times their definition refers
to \AgdaData{Set}.

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

More generally, the spectrum of open versus closed is not necessarily
about how many times a type definition mentions \AgdaData{Set}, but
about how many values in a type we can make decisions about. In other
words, the spectrum is really about abstract versus concrete.

The act of defining a datatype inductively pushes
us closer to the closed side of the spectrum, because we can make
decisions by pattern matching on the constructors of the new
type. However, the arguments of the constructors of an open type may
contain \AgdaData{Set}s that we may \textit{not} inspect. As we
replace \AgdaData{Set}s with specialized types, we move even closer
towards the closed spectrum. A fully closed type is one that allows
functions to make decisions based on any of its values.
A fully open type is one that does not allow functions to make any
decisions, such as the \AgdaData{Set} itself as demonstrated by the
unique inhabitant of the identity function. 

\begin{code}
  id : {A : Set} → A → A
  id a = a
\end{code}

Fully open and fully closed types are the endpoints of our
spectrum.
\footnote{Although this thesis only considers occurrences of
\AgdaData{Set} as a means to make a definition open, another example
would be definitions given as abstract datatypes (ADTs). For example,
the abstract datatype of key/value dictionaries exports the type
of dictionaries and their operations (create an empty dictionary,
insert into a dictionary, and delete from a dictionary.) Importantly,
the constructors of the underlying dictionary type and the
implementation details of its operations are not exported.}

\subsection{Universes}

Just as a type is a collection of values, a \textit{universe}
is a collection of \textit{types}. 
A primary motivation of universes is allowing functions to only
consider the values of a sensible collection of types.

\paragraph{Open Universes}

In a dependently typed language, a universe can be defined as a
collection of codes representing the types in the universe, and a
meaning function mapping each code to the actual type in the language.

An \textit{open universe} refers to \AgdaData{Set} either in its
codes, or in its meaning function. For example, below is the universe of
some base type closed under list formation.

\AgdaHide{
\begin{code}
module OpenUniv where
  postulate append : ∀{A} → List A → List A → List A
\end{code}}

\begin{code}
  data ListStar (A : Set) : Set₁ where
    `Base : ListStar A
    `List : ListStar A → ListStar A
  
  ⟦_⟧ : ∀{A} → ListStar A → Set
  ⟦_⟧ {A} `Base = A
  ⟦ `List A ⟧ = List ⟦ A ⟧
\end{code}

The act of defining a universe also pushes us towards the closed side
of the spectrum, because we can make decisions by pattern matching on
the codes of the universe. For example, consider the \AgdaFun{concat}
function below operating over our universe.

\begin{code}
  concat : ∀{A} (B : ListStar A) → ⟦ B ⟧ → List A
  concat `Base x = cons x nil
  concat (`List A) nil = nil
  concat (`List A) (cons x xs) = append (concat A x) (concat (`List A) xs)
\end{code}

``closed under list formation''

\paragraph{Closed Universes}

A \textit{closed universe} does not refer to \AgdaData{Set} in its
codes, nor in its meaning function. For example, below is the universe of
booleans closed under list formation.

\AgdaHide{
\begin{code}
module ClosedUniv where
\end{code}}

\begin{code}
  data Code : Set₁ where
    `Bool : Code
    `List : Code → Code
  
  ⟦_⟧ : Code → Set
  ⟦ `Bool ⟧ = Bool
  ⟦ `List A ⟧ = List ⟦ A ⟧
\end{code}

%% \paragraph{More Closed}
%% Add a `Pair or `Tree constructor for concat


%% \subsection{Generic Functions}

%% In a sense, functions over open types are \textit{generic} with
%% respect to all concrete \AgdaData{Set}s that the open type may be
%% instantiated with. In fact, the functions must work the
%% \textit{same way} for all concrete \AgdaData{Set}s.
%% \footnote{In open type theories, there is no way to case-analyze
%%   values of \AgdaData{Set}, so functions cannot make decisions based
%%   on which concrete \AgdaData{Set} appears.}

%% Recall that functions defined over open types can be considered
%% \textit{generic} in the sense they are defined once and for all
%% \AgdaData{Set}s (those defined now or in the future). 
%% Similarly, \textit{generic} functions defined over a universe can be
%% defined once and for all types in the universe.

%% The difference is that a generic functions over an open type (such as
%% a parametrically polymorphic functions) must act the \textit{same} for
%% all possible \AgdaData{Set}s. In contrast, a generic
%% function over a universe can behave \textit{differently} for each type
%% in the universe, because there are a finite number of type
%% \textit{codes} to consider.
%% This is similar to the way a function over a closed type can behave
%% \textit{differently} for all values contained within it.





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
