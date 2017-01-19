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
 open import Level
 private
  postulate
\end{code}}

Functions written in dependent type theory (DTT) must be
\textit{total} (defined over all inputs). Thus, partial functions
written in traditional languages cannot be directly encoded as
functions in DTT. In this section we explain a general technique for
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
function by altering either the domain or codmain, first by using
non-dependent types and then by taking advantage of dependent types.

\subsection{Non-Dependent Domain Change}

\subsection{Non-Dependent Codomain Change}

\subsection{Dependent Domain Change}

\subsection{Dependent Codomain Change}

%% \subsection{Domain Predicates}

\subsection{Summary}

We have seen how to encode partial functions within total type theory
by modifying the domain or codomain of a function, with and without
the benefits afforded by dependent typing. Previously when writing
ordinary functions over types (\refsec{types}), and especially when
writing generic functions over universes (\refsec{universes}), we
deliberately chose examples that were naturally total to avoid using
the techniques of this section.

However, as the size of the universes we generically program over
grows it often becomes necessary to use computational argument or
return types to make the generic functions total. This is especially
true when writing fully generic functions (\refsec{fullygeneric}), as
it might not be possible to define a function for certain values of a
universe without extra data, or without restricting the
domain to be undefined (as \AgdaData{⊥}) for certain values.
