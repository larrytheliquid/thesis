\AgdaHide{
\begin{code}
module Thesis.Universes where

data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A

append : ∀{A} → List A → List A → List A
append nil ys = nil
append (cons x xs) ys = cons x (append xs ys)
\end{code}}

\subsection{Types}
In programming languages, a \textit{type} is a construct used to capture the
notion of a collection of \textit{values}.
%% When we create a type, we
%% usually have particular properties in mind that values in the
%% collection adhere to. 
A primary motivation of types is the ability to assign them to the
inputs and output of a function, thereby allowing the function to
only consider sensible values.

For example, below the \AgdaFun{reverse} function assumes that
it works over lists, because working over values of many other types
(such as trees) does not make sense.

\begin{code}
reverse : ∀{A} → List A → List A
reverse nil = nil
reverse (cons x xs) = append (reverse xs) (cons x nil)
\end{code}





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
