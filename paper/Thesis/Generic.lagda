\AgdaHide{
\begin{code}
module _ where
open import Function
open import Appendix
\end{code}}

\chapter{Fully Generic Functions}\label{ch:fullyg}

In this chapter we formally model fully generic programming in a
closed dependently typed language. We write fully generic functions in
the universe of \refsec{closed},
supporting user-declared datatypes while remaining closed.

Thus far, we have focused on defining concrete datatypes in our
universe of (inductive-recursive) algebraic types.
\textit{Smart constructors} (defined as functions, first demonstrated
\refsec{nondepalgtps}), for the type former and constructors of a
concrete algebraic datatypes, allow us
to \textit{construct} concrete types and their values while hiding
their generic encoding in terms of initial algebra
semantics. Similarly, \textit{pattern synonyms}
(demonstrated in \refsec{nondepalgtps}),
for constructors of
concrete types encoded using initial algebra semantics,
allow us to
\textit{deconstruct} generically encoded values by writing
functions defined by pattern matching
while hiding underlying algebraic encodings.

While smart constructors and pattern synonyms shelter users from
generic encodings when they construct and deconstruct
\textit{concrete} datatypes, fully generic programming requires users
to understand how to generically construct and deconstruct \textit{encoded}
datatypes, by applying and matching against the \Con{init}ial algebra
constructor of \Data{μ₁}. By definition, fully generic functions can
be applied to (and may return) values of any user-declared type, thus
understanding the underlying generic encoding is necessary. In this
chapter we define 4 fully generic functions:
\begin{enumerate}
\item \Fun{count}, in \refsec{gcount}, counting the number of nodes
  in a generically encoded value.
\item \Fun{lookup}, in \refsec{glookup}, looking up any subnode in a
  in a generically encoded value.
\item \Fun{update}, in \refsec{gupdate}, updating any subnode in a
  in a generically encoded value.
\item \Fun{ast}, in \refsec{gast}, marshalling any generically
  encoded value to an abstract syntax tree (AST), defined as a rose
  tree.
\end{enumerate}


\section{Fully Generic Count}\label{sec:gcount}

In this section we develop a fully generic \Fun{count} function,
which counts the number of nodes that make up a generically encoded
value. The \Fun{count} function is used in the types of
subsequently-defined generic functions, \Fun{lookup} in \refsec{glookup} and
\Fun{update} in \refsec{gupdate}, to constrain those operations
to valid positions of a value.

\subsection{Generic Types}

Before covering the details of implementing \Fun{count}, we return
to the introduction of our dissertation to clarify our intuition about
the type signatures of fully generic functions.
In \refsec{naivegfun}, we hinted that any fully
generic function can be defined by mutually defining a function over
all types and another function over all descriptions (whose fixpoint
is a special case of the function over all types). 

$$
(\Var{A} : \Data{Type})~
(\Var{a} : \AgdaFun{⟦}~\AgdaVar{A}~\AgdaFun{⟧})
→ ...
$$
$$
(\Var{D} : \Data{Desc})~
(\Var{x} : \AgdaData{μ}~\AgdaVar{D})
→ ...
$$

Specializing this template to a generic \Fun{count}, and
making some changes to work with our closed universe of
\refsec{closed} (discussed below), results in the following two
mutually defined functions.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open Prim
 open Alg
 open Closed
 private
  postulate
\end{code}}

\begin{code}
   count : (A : `Set) → ⟦ A ⟧ → ℕ
   countμ : {O : `Set} (D : `Desc O) → μ₁ ⟦ O ⟧ ⟪ D ⟫ → ℕ
\end{code}

The intuition (presented in \refsec{naivegfun} of the introduction)
behind the closed \Fun{count} function is largely correct. The only
difference is that we have renamed \Data{Type} to \Data{`Set}, to
notationally emphasize that its intepretation as a \Data{Set} is
obtained by ``removing the backtick''.

However, the intuition behind the closed \Fun{countμ} function was
simplified in the introduction. A minor difference is that we must
add an \Var{O} parameter, to account for the codomain of the
inductive-recursive decoding function. One major difference is that
the intuition from the introduction leads to defining \Fun{countμ}
over all \textit{open} descriptions (\Data{Desc}), but fully generic
programming demands that we define it over all \textit{closed}
descriptions (\Data{`Desc}). Let's remind ourselves of the definition
of the type component of the fixpoint operator:

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open Prim
 open Alg hiding ( μ₁ )
 private
\end{code}}

\begin{code}
   data μ₁ (O : Set) (D : Desc O) : Set where
     init : ⟦ D ⟧₁ D → μ₁ O D
\end{code}

Recall that \Data{μ₁} expects \Var{O} to be the kind of open types
(\Data{Set}), and \Var{D} to be the kind of open descriptions
(\Data{Desc}). In the type of the generic \Fun{countμ} function,
\Var{O} is the type of closed types
(\Data{`Set}), and \Var{D} is the type of closed descriptions
(\Data{`Desc}), hence \Data{μ₁}
(appearing in an argument position of the type of \Fun{countμ}) is
applied to the meaning of
\Var{O} and \Var{D}
(obtained by applying \Fun{⟦\_⟧} and \Fun{⟪\_⟫}, respectively).

There is a second major difference between the types we use for fully
generic programming, and the types behind the intuition in the
introduction. It is not possible to directly define a function over
all closed descriptions like \Fun{countμ}. The problem is that the
inductive hypothesis is not general enough in the
infinitary (hence, also inductive) \Con{`δ} case. Instead of mutually
defining \Fun{count} with \Fun{countμ} (a function over all algebraic
types), we mutually define
\Fun{count} with \Fun{counts} (a function over all
arguments of algebraic types, isomorphic to \Fun{countμ}).

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open Prim
 open Alg
 open Closed
 private
  postulate
\end{code}}

\begin{code}
   counts : {O : `Set} (D R : `Desc O) → ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫ → ℕ
\end{code}

Recall that \Fun{⟦\_⟧₁} (defined below, for reference)
is the type component of the interpretation
function for descriptions. It appears as the sole argument to the
\Con{init}ial algebra constructor of \Data{μ₁}. Because \Data{μ₁} \Var{O} \Var{D} is
isomorphic to \Fun{⟦} \Var{D} \Fun{⟧₁} \Var{D}, defining \Fun{counts}
is an acceptable alternative to defining \Fun{countμ}.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open Prim
 open Alg hiding ( ⟦_⟧₁ )
 private
\end{code}}

\begin{code}
   ⟦_⟧₁ : {O : Set} (D R : Desc O) → Set
   ⟦ ι o ⟧₁ R = ⊤
   ⟦ σ A D ⟧₁ R = Σ A (λ a → ⟦ D a ⟧₁ R)
   ⟦ δ A D ⟧₁ R = Σ (A → μ₁ _ R) λ f → ⟦ D (λ a → μ₂ R (f a)) ⟧₁ R
\end{code}

The interpretation function recurses over the first argument (\Var{D}) to
determine the type of constructor arguments, while holding the second
argument (\Var{R}) constant. This allows
\Fun{⟦\_⟧₁} to remember the original \textit{complete} description
(\Var{R}) of the algebraic type, even though it is destructing a copy
of it (\Var{D}) as it recurses.

By remembering the original description
(\Var{R}), the open \Con{δ} case can request an infinitary (hence, also
inductive) argument as the first argument to \Data{Σ}.
For analogous reasons, \Fun{counts} is generically defined over
all descriptions (\Var{D}), but also a copy (\Var{R}) of the original
\textit{complete} description that it can use to count infinitary
arguments in the closed \Con{`δ} case.

\subsection{Counting All Values}

First, let's define \Fun{count} fully generically for all values of
all types. This involves calling the mutually defined \Fun{counts}
functions (for all arguments of the \Con{init}ial algebra), which we define
next.
Below, we restate the type of \Fun{count}, and then define
\Fun{count} by case analysis and recursion over all of its closed
types. 

\AgdaHide{
\begin{code}
module Count where
 open import Data.Nat
 open Prim
 open Alg
 open Closed
 mutual
\end{code}}

\begin{code}
  count : (A : `Set) → ⟦ A ⟧ → ℕ
\end{code}

Remember, we wish to define \Fun{count} as the sum of all
constructors and the recursive \Fun{count} of all constructor
arguments. It may be helpful to review \Fun{count} for the
\textit{fixed} closed universe in the introduction
(\refsec{introcount}), to see how it compares to our new \Fun{count},
defined over an \textit{extendable}
(by user-declared datatypes) closed universe.

\paragraph{Dependent Pair}

We \Fun{count} a dependent pair by summing the recursive
\Fun{count} of both its components (\Var{a} and \Var{b}),
plus 1 to also count the pair constructor (\Con{,}). Notice that the
\textit{dependent} type of the second component (\Var{b}) is computed by
applying the codomain of the dependent pair (\Var{B}) to the
first component (\Var{a}).

\begin{code}
  count (`Σ A B) (a , b) = 1 + count A a + count (B a) b
\end{code}

\paragraph{Algebraic Fixpoint}

We \Fun{count} an algebraic fixpoint by by recursively counting its
arguments (\Var{xs}) using \Fun{counts}, plus 1 to account
for the \Con{init} constructor. When we initially call \Fun{counts},
\Var{D} is used for both of its arguments. However, as \Fun{counts}
recurses, the first description argument will be destructed while the
second (original) description argument is held constant.

\begin{code}
  count (`μ₁ O D) (init xs) = 1 + counts D D xs
\end{code}

\paragraph{Remaining Values}

All constructors of the remaining types (such as \Data{Bool}) do not
have arguments, so we \Fun{count} them as 1 (for their constructor,
plus 0 for their arguments). Note that this includes functions, which
which we treat as a black box by counting the $\lambda$ constructor as
1, without recursively counting its body.

\begin{code}
  count A a = 1
\end{code}

\subsection{Counting Algebraic Arguments}

the mutually defined \Fun{count}
(for values of all types) and
\Fun{counts} (for arguments of descriptions for all fixpoints)
functions. Below, we follow the type signatures of each full generic
function (\Fun{count} and \Fun{counts}) with their definitions by case
analysis. 

\begin{code}
  counts : {O : `Set} (D R : `Desc O) → ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫ → ℕ
\end{code}

\paragraph{Last Argument}

\begin{code}
  counts (`ι o) R tt = 1
\end{code}

\paragraph{Non-Inductive Argument}

\begin{code}
  counts (`σ A D) R (a , xs) = count A a + counts (D a) R xs
\end{code}

\paragraph{Inductive Argument}

\begin{code}
  counts (`δ `⊤ D) R (f , xs) = count (`μ₁ _ R) (f tt) +
    counts (D (λ u → μ₂ ⟪ R ⟫ (f u))) R xs
\end{code}
  
\paragraph{Infinitary Argument}

\begin{code}
  counts (`δ A D) R (f , xs) = 1 + counts (D (λ a → μ₂ ⟪ R ⟫ (f a))) R xs
\end{code}

\subsection{Examples}

\subsection{Generic Lemmas}

\section{Fully Generic Lookup}\label{sec:glookup}

\section{Fully Generic Update}\label{sec:gupdate}

\section{Fully Generic AST}\label{sec:gast}

