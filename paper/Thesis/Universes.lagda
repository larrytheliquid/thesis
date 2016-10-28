\AgdaHide{
\begin{code}
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
module Lists where
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

\begin{code}
data HList : Set₁ where
  nil : HList
  cons : {A : Set} → A → HList → HList
\end{code}



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
