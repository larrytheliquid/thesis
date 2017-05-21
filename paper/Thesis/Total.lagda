\AgdaHide{
\begin{code}
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.List hiding ( concat ) renaming ( [] to nil ; _∷_ to cons )
module _ where
\end{code}}

\section{Totality}\label{sec:totality}

\AgdaHide{
\begin{code}
module _ where
 private
  postulate
\end{code}}

Functions written in dependent type theory (DTT) must be
\textit{total} (defined over all inputs). Thus, partial functions
written in traditional languages cannot be directly encoded as
functions in DTT. In this section, we explain a general technique for
altering the type signature of a partial function so that it may be
encoded as a total function in DTT.
We use the \AgdaFun{head} function as our running example of a
partial function that we wish to encode in a total language.

\begin{code}
   head : {A : Set} → List A → A
\end{code}

Applying \AgdaFun{head} to a non-empty list should return the first
element, but applying \AgdaFun{head} to an empty list should be
undefined. Below we explain how to encode \AgdaFun{head} as a total
function by altering either the domain or codomain, first by using
non-dependent types and then by taking advantage of dependent types.

\subsection{Non-Dependent Domain Change}

In a non-dependent language, we could write \AgdaFun{head} as a total
function by adding an extra \AgdaVar{A} argument to the domain. This
extra argument serves as a ``default'' argument to return in the
(otherwise partial) empty list case.

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\begin{code}
  head : {A : Set} → List A → A → A
  head nil y = y
  head (cons x xs) y = x
\end{code}

\subsection{Non-Dependent Codomain Change}

In a non-dependent language, we could also write \AgdaFun{head} as a
total function by changing the return type to
\AgdaData{Maybe} \AgdaVar{A}. This allows us to dynamically model
partiality by failing with \AgdaCon{nothing} in the empty list case,
and succeeding with \AgdaCon{just} in the non-empty list case.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Maybe
 private
\end{code}}

\begin{code}
  head : {A : Set} → List A → Maybe A
  head nil = nothing
  head (cons x xs) = just x
\end{code}

\subsection{Dependent Domain Change}\label{sec:comparg}

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

Without dependent types we can add a default argument to
\AgdaFun{head}. Unfortunately, a user must supply this default
argument even if they are taking the head of a non-empty
list. With dependent types, we can add an extra \textit{dependent}
argument to \AgdaFun{head}. The type of the extra argument depends on
the input list, and is defined below as a
\textit{computational argument type} (a type family defined as a
computation as in \refsec{compu}, in an argument position of a
function).
%% TODO footnote could also define as an algebraic type family propositionally

\begin{code}
  HeadArg : {A : Set} → List A → Set
  HeadArg {A = A} nil = A
  HeadArg (cons x xs) = ⊤
\end{code}

If the input list is empty, \AgdaFun{HeadArg} computes to \AgdaVar{A},
the type of the default argument that is required. If the input list
is non-empty, \AgdaFun{HeadArg} returns the unit type (\AgdaData{⊤}). Because a
value of type unit can always be trivially constructed, this is
equivalent to not having an extra argument at all when the input list
is non-empty. Now we can define \AgdaFun{head} with \AgdaFun{HeadArg}
as its extra argument.

\begin{code}
  head : {A : Set} (xs : List A) → HeadArg xs → A
  head nil y = y
  head (cons x xs) tt = x
\end{code}

Notice that \AgdaFun{head} only receives the default argument
\AgdaVar{y} in the empty list case. Otherwise, it receives the trivial
\AgdaCon{tt} constructor of the unit type.

\subsection{Dependent Codomain Change}\label{sec:compret}

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

Without dependent types we can change the codomain to dynamically
model partiality using the \AgdaData{Maybe} type. Dependent types
allow us to statically enforce partiality.
We define the return type to be a
\textit{computational return type} (a type family defined as a
computation, in the return type position of a function).

\begin{code}
  HeadRet : {A : Set} → List A → Set
  HeadRet nil = ⊤
  HeadRet {A = A} (cons x xs) = A
\end{code}

If the input list is non-empty, \AgdaFun{HeadRet} computes the
standard return type \AgdaVar{A}. However, if the list is empty then
\AgdaFun{HeadRet} computes the unit type. A function returning unit
may as well be undefined, as its output is uniquely determined to be
\AgdaCon{tt}.

\begin{code}
  head :{A : Set} (xs : List A) → HeadRet xs
  head nil = tt
  head (cons x xs) = x
\end{code}

Rather than dynamically enforcing partiality by returning a
\AgdaCon{nothing} failure value for non-empty lists, \AgdaFun{head}
is statically ``partial'' as its definition for the empty list case is
uniquely determined.

\subsection{Domain Supplements}\label{sec:domsup}

\AgdaHide{
\begin{code}
module _ where
 open import Data.Empty
 private
\end{code}}

We have seen two different ways
(in \refsec{comparg} and \refsec{compret})
to make \AgdaFun{head} total using
dependent types, first by adding missing data (the default argument
\AgdaVar{A}), and second by effectively making the function undefined
for its ``partial'' cases.

A more common approach is to directly model partiality as a computational
argument type that \textit{requests} an argument of the empty type for the
empty list case. This in contrast to modeling partiality as a
computational return type (\refsec{compret}) that \textit{returns} unit for the empty
list case. 

\begin{code}
  HeadArg : {A : Set} → List A → Set
  HeadArg {A = A} nil = ⊥
  HeadArg (cons x xs) = ⊤
\end{code}

This allows us to leave the empty list case undefined, as a value of
type \AgdaData{⊥} is known to not exist.

\begin{code}
  head : {A : Set} (xs : List A) → HeadArg xs → A
  head nil ()
  head (cons x xs) tt = x
\end{code}

It is clear that the computational argument type
\AgdaFun{HeadArg} above acts a
\textit{domain predicate}, refining the domain of all lists to be
undefined for the empty list by asking
the user to provide a value of
the empty type (\AgdaData{⊥}). Compare this to the version of \AgdaFun{HeadArg} in
\refsec{comparg}, which requests an extra argument (\AgdaVar{A}) in the empty list
case. The \refsec{comparg} \AgdaFun{HeadArg} is also technically a
domain predicate, as it restricts the input of all lists to supply
additional data (\AgdaVar{A}) in the empty list case
(i.e. \AgdaFun{head} is no longer defined for all lists, only those
with additional data). However,
this usage of the word ``predicate'' feels unnatural, as predicates
are associated with logically restricting a domain (rather than
requesting additional data). For this reason, we prefer to call
the \refsec{comparg} \AgdaFun{HeadArg} a \textit{domain supplement}.
Thus, we have two options when embedding a partial
function in type theory:
\begin{enumerate}
\item Use a domain predicate to
  restrict the domain, avoiding definitions for the partial cases. For
  example, adding an empty type argument or returning unit.
\item Use a domain supplement to request additional data,
  computing results for the partial cases using the additional data.
  For example, returning a default value provided as an additional
  argument.
\end{enumerate}

This thesis focuses more on the second
option. Functions made total using domain supplements are
more interesting than ones using domain predicates, as the supplement
adds computationally relevant
data rather than just restricting the
domain to be undefined for certain cases.
Thus, a domain supplement is like a proof-relevant version of a domain
predicate (even though both technically restrict the domain). 

\subsubsection{Conclusion}

We have seen how to encode partial functions within total type theory
by modifying the domain or codomain of a function, with and without
the benefits afforded by dependent typing. Previously, when writing
ordinary functions over types (\refsec{types}), and especially when
writing generic functions over universes (\refsec{universes}), we
deliberately chose examples that were naturally total to avoid using
the techniques of this section.

However, as we write generic programs over larger universes (those
containing more types),
it often becomes necessary to use computational argument or
return types to make generic functions total. This is particularly
true when writing fully generic functions (\refsec{fullygeneric}), as
it might not be possible to define them for certain values of a
universe without domain supplements.

%% TODO forward reference uses of this
