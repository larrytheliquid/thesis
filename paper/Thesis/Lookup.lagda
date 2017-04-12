\AgdaHide{
\begin{code}
module _ where
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Function
open import Appendix
open import Data.Product
open import Count
open Prim  hiding ( Σ )
open Alg
open Closed
open Count.Count
open Count.Split
\end{code}}

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open import Data.Vec hiding ( lookup ) renaming ( [] to nil ; _∷_ to cons)
 private
\end{code}}

\section{Fully Generic Lookup}\label{sec:glookup}

In this section we develop a fully generic \Fun{lookup} function,
which can retrieve any node of a generically encoded value.
The input to \Fun{lookup} is a value and an index into a position
within the value. To prevent out-of-bounds errors during lookups, we
generalize the type of \Fun{lookup} for vectors (\Data{Vec}).

To retrieve a value within a vector, we apply \Fun{lookup} to a
vector (\Data{Vec}) and a finite set (\Data{Fin}), where \Data{Fin}
acts as an index whose maximum value is constrained to equal the
length of the vector. Recall the type of finite sets from
\refsec{indx}.

\begin{code}
  data Fin : ℕ → Set where
    here : {n : ℕ} → Fin (suc n)
    there : {n : ℕ} → Fin n → Fin (suc n)
\end{code}

The type of finite sets acts as a 1-based index whose maxium value is
the natural number that \Data{Fin} is applied to. For all
\Var{n}, there are \Var{n}-1 inhabitants of \Data{Fin} \Var{n}, where
the first is \Con{here}, and the rest are successive applications of
\Con{there} (ending in \Con{here}). For example, the inhabitants of
\Data{Fin} \Num{3} are
\Con{here} (for index \Num{1}),
\Con{there here} (for index \Num{2}), and
\Con{there} (\Con{there here}) (for index \Num{3}).

To \Fun{lookup} a \Data{Vec}tor of length \Var{n}, we index by
\Data{Fin} \Var{n}. The implementation of \Fun{lookup} returns the
head of the vector (at position \Num{1}) if the index is
\Con{here}. If the index is \Con{there}, \Fun{lookup} recursively
searches the tail of the vector (until it finally finds a value
to return, indicated by peeling off enough \Con{there}'s to arrive
at a \Con{here}).

\begin{code}
  lookup : {A : Set} {n : ℕ} → Vec A n → Fin n → A
  lookup (cons x xs) here = x
  lookup (cons x xs) (there i) = lookup xs i
\end{code}

Instead of using vectors, we can define \Fun{lookup} equivalently over
lists, by \textit{computing} the maximum bound of the index
(\Data{Fin}) from the \Fun{length} of the \Data{List}.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Fin renaming ( zero to here ; suc to there )
 open import Data.List renaming ( [] to nil ; _∷_ to cons)
 private
\end{code}}

\begin{code}
  lookup : {A : Set} (xs : List A) → Fin (length xs) → A
  lookup nil ()
  lookup (cons x xs) here = x
  lookup (cons x xs) (there i) = lookup xs i
\end{code}

Besides needing to supply explicit evidence, by pattern matching
against the uninhabited empty \Data{Fin} \Num{0} index
(using empty parentheses) in the \Con{nil} case, the implementation
for \Data{List}s is the same as the implementation for \Data{Vec}tors.

Our fully generic \Fun{lookup} is defined similarly to the \Data{List}
lookup, except \Fun{length} (calculating the bound of index
\Data{Fin}) is replaced by our fully generic \Fun{count}
from \refsec{gcount}. Recall that \Fun{count} sums the number of nodes
in a generic value according to a depth-first traversal. Therefore,
\Fun{lookup}ing up a node in a generic value corresponds to supplying
a \Data{Fin} index representing the depth-first label of the node
(seen in the figures of \refsec{gcount:egs}).

\AgdaHide{
\begin{code}
open import Data.Fin hiding ( _+_ ) renaming ( zero to here ; suc to there )
\end{code}}

\subsection{Generic Types}

Before covering the details of implementing \Fun{lookup},
let's consider what its type should be.
As mentioned above, we expect \Fun{lookup} to have a \Data{Fin}
index argument whose bound is calculated by the generic \Fun{count}
of the value that \Fun{lookup} is applied to.

Looking up a \Data{List} \Var{A} results in an \Var{A}, but
looking up a node in a generic value causes the return type
of \Fun{lookup} to depend on the type of node being looked up.
Thus, we must define a
computational return type (\refsec{compret}),
named \Fun{Lookup} below, to determine what the return type of
\Fun{lookup} should be. 

\AgdaHide{
\begin{code}
module _ where
 private
  postulate
\end{code}}

\begin{code}
   Lookup : (A : `Set) (a : ⟦ A ⟧)
     → Fin (count A a) → Set
   lookup : (A : `Set) (a : ⟦ A ⟧)
     (i : Fin (count A a)) → Lookup A a i
\end{code}

We must also mutually define
\Fun{Lookups}, to compute the return type when
looking up an argument of an algebraic constructor,
via \Fun{lookups}.

\begin{code}
   Lookups : {O : `Set} (D R : `Desc O) (xs : ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫)
    → Fin (counts D R xs) → Set
   lookups : {O : `Set} (D R : `Desc O) (xs : ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫)
    (i : Fin (counts D R xs)) → Lookups D R xs i
\end{code}

Whenever defining the value component (\Fun{lookup} or \Fun{lookups}),
we must pattern match against at least as many arguments as the
type component (\Fun{Lookup} or \Fun{Lookups}), in order for the
computational return type to definitionally unfold.
Instead of defining the value and type components separately,
thereby repeating the pattern matching structure twice,
we will actually define single functions returning
\textit{dependent pairs} (\Data{Σ}).

\AgdaHide{
\begin{code}
module _ where
 private
  postulate
\end{code}}

\begin{code}
   lookup : (A : `Set) (a : ⟦ A ⟧)
     → Fin (count A a) → Σ Set (λ A → A)
   lookups : {O : `Set} (D R : `Desc O) (xs : ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫)
    (i : Fin (counts D R xs)) → Σ Set (λ A → A)
\end{code}

The first component of the pair corresponds to the type component
(\Fun{Lookup} or \Fun{Lookups}), and the second component
of the pair is a value
(corresponding to the formerly named \Fun{lookup} or \Fun{lookups}),
whose type is the first component.
We can still recover the original type and value components by
taking the first (\Fun{proj₁}) and
second (\Fun{proj₂}) projections of the dependent pairs (\Data{Σ})
resulting from the new versions of \Fun{lookup} and \Fun{lookups}.
By convention, we refer to the first projection (type component)
of these functions by suffixing ₁ (e.g. \Fun{lookup₁}),
and to the second projection (value component)
version by suffixing ₂ (e.g. \Fun{lookup₂}).

\subsection{Looking Up All Values}\label{sec:lookup}

\AgdaHide{
\begin{code}
module Lookup where
 open import Data.Nat
 mutual
\end{code}}

First, let's define \Fun{lookup} fully generically for all values of
all types. This involves calling \Fun{lookups} in the \Con{`μ₁} case,
defined mutually (in \refsec{lookups}) over all arguments of the
\Con{init}ial algebra.
Below, we restate the type of \Fun{lookup}, and then define
\Fun{lookup} by case analysis and recursion over all of its closed
types, \textit{and} its \Data{Fin} indices.

\begin{code}
  lookup : (A : `Set) (a : ⟦ A ⟧) → Fin (count A a) → Σ Set (λ A → A)
\end{code}

Before we actually define \Fun{lookup}, let's consider what the type
of the index \Data{Fin} argument could be \textit{before} we pattern
match against it, and what \Fun{lookup} should return
once we do match against the index.
Below, we give a template of 3 different
\Data{Fin} types that appear when when defining \Fun{lookup} (as well
as \Fun{lookups}). Each template represents a possible type of
\Data{Fin}, due to partially unfolding a case of
\Fun{count} (in \refsec{count})
or \Fun{counts} (in \refsec{counts}).
\begin{enumerate}
\item{\textbf{Case} (\Data{Fin} \Num{1})}
  There is only one possible index, so we define a \Con{here} case
  that returns the value at this index.
\item{\textbf{Case} (\Data{Fin} (\Num{1} \Fun{+} \Var{n}))}
  We define a \Con{here} case (for the \Num{1}),
  returning the value at this index.
  We also define a \Con{there} case (for the \Var{n}),
  giving us a new argument of type \Data{Fin} \Var{n}.
  In the \Con{there} case, we return
  the recursive call of \Fun{lookup} or \Fun{lookups},
  depending on whether \Var{n} is \Fun{count} or \Fun{counts}.
\item{\textbf{Case} (\Data{Fin} (\Num{1} \Fun{+} \Var{n} \Fun{+} \Var{m}))}
  We define a \Con{here} case (for the \Num{1}),
  returning the value at this index.
  We also define a \Con{there} case (for the \Var{n} \Fun{+} \Var{m}),
  giving us a new argument of type \Data{Fin} (\Var{n} \Fun{+} \Var{m}).
  Within the \Con{there} case, we must translate the single
  \Data{Fin} (\Var{n} \Fun{+} \Var{m}) index to the disjoint union of
  the two potential indices \Data{Fin} \Var{n} \Data{⊎} \Data{Fin} \Var{m}.
  After case-analyzing the disjoint union (\Data{⊎}),
  we make a recursive call using the index within the
  left (\Con{inj₁}) or right (\Con{inj₂}) injection. Once again, the
  recursive call is either \Fun{lookup} or \Fun{lookups}, depending on
  whether \Var{n} or \Var{m}
  (whichever one we find in the disjoint union)
  is \Fun{count} or \Fun{counts}.
\end{enumerate}

To know which \textbf{Case} template to use for \Fun{lookup}
at some type \Var{A},
match the template with the \Var{A} case
of \Fun{count} in \refsec{count}.

\paragraph{Algebraic Fixpoint}

For the \Con{there} case of algebraic fixpoints
(\textbf{Case 2}), we recursively lookup its arguments (\Var{xs}),
using the mutually defined \Fun{lookups}.

\begin{code}
  -- i : Fin (counts D D xs)
  lookup (`μ₁ O D) (init xs) (there i) = lookups D D xs i
\end{code}

For clarity, we include the type of the
index \Var{i} (the argument of the \Con{there} constructor) as a
comment. In the type of \Var{i}, the value that \Data{Fin} is applied
to corresponds to the value of \Var{n} in \textbf{Case 2}.

\paragraph{Dependent Pair}

For the \Con{there} case of dependent pairs
(\textbf{Case 3}), we use the helper function \Fun{splitΣ}
to turn \Var{i}, a single index (\Data{Fin})
containing a sum (\Fun{+}), into a disjoint union (\Data{⊎})
of two indices. 

\begin{code}
  -- i : Fin (count A a + count (B a) b)
  lookup (`Σ A B) (a , b) (there i) with splitΣ A B a b i
  -- j : Fin (count A a)
  ... | inj₁ j = lookup A a j
  -- j : Fin (count (B a) b)
  ... | inj₂ j = lookup (B a) b j
\end{code}

If the disjoint union is the left injection
(\Con{inj₁}), we recursively \Fun{lookup} the first component of the
pair (\Var{a}).
If the disjoint union is the right injection
(\Con{inj₂}), we recursively \Fun{lookup} the second component of the
pair (\Var{b}). The two possible values that \Data{Fin} is applied to in
the two possible types of \Var{j} correspond to \Var{n} and \Var{m}
in \textbf{Case 3}.

\paragraph{Remaining Values}

Finally, the \Con{here} case can be defined uniformly over all
types. If the index points to \Con{here}, we simply return the
value \Var{a} at this position, along with the
type meaning function (\Fun{⟦\_⟧}) applied to the
closed type (\Var{A}) of the value,
as a dependent pair (\Con{,}).\footnote{
  We use an @-pattern to bind \Var{A} to the matched \Con{`Σ}
  type. Unfortunately Agda makes us repeat this definition for all
  other remaining types, but at least the right-hand sides are all the
  same because of the @-pattern.
  The problem with \Fun{lookup} is that \Fun{count}
  appears in its type, which is defined using a catch-all pattern
  clause. Unfortunately, we cannot write \Fun{lookup} using the same
  catch-all pattern structure, and must instead enumerate all types
  and duplicate their right-hand sides manually.
  Defining \Fun{lookup} by repating the catch-all structure of
  \Fun{count} would be possible if Agda were changed to type-check
  code \textit{after} coverage checking. 
  }

\begin{code}
  lookup A@(`Σ _ _) a here = ⟦ A ⟧ , a
\end{code}

For \Con{`μ₁} this is the \Con{here} component of the
definition of \textbf{Case 2}, and for \Con{`Σ} this is the
\Con{here} component of the definition of \textbf{Case 3}.
For all other types, this is the definition of
\textbf{Case 1} (which does not have a \Con{there}
component).

\AgdaHide{
\begin{code}
  lookup A@`⊥ a i = ⟦ A ⟧ , a
  lookup A@`Bool a i = ⟦ A ⟧ , a
  lookup A@`⊤ a i = ⟦ A ⟧ , a
  lookup A@`String a i = ⟦ A ⟧ , a
  lookup A@(`Π _ _) a i = ⟦ A ⟧ , a
  lookup A@(`Id _ _ _) a i = ⟦ A ⟧ , a
  lookup A@(`μ₁ _ _) a i = ⟦ A ⟧ , a
\end{code}}

\subsection{Looking Up Algebraic Arguments}\label{sec:lookups}

Second, let's define \Fun{lookups} fully generically for all
arguments of the \Con{init}ial algebra. This involves calling
\Fun{lookup} in the \Con{`σ} and \Con{`δ} cases,
defined mutually (in \refsec{lookup}) over all values of all types.
Below, we restate the type of \Fun{lookups}, and then define
\Fun{lookups} by case analysis and recursion over all of its closed
descriptions, \textit{and} its \Data{Fin} indices.

\begin{code}
  lookups : {O : `Set} (D R : `Desc O) (xs : ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫)
    → Fin (counts D R xs) → Σ Set (λ A → A)
\end{code}

We will also classify the cases in the definition of \Fun{lookups} by
the \textbf{Case} template numbers. Below, we repeat the first 2
\textbf{Case} templates from \refsec{lookup} verbatim. However, the 3rd template is
different because it lacks a ``\Num{1} \Fun{+} ...'' prefix.
\footnote{
  The lack of the ``\Num{1} \Fun{+} ...''
  prefix is because we allow indexing into any argument of a sequence,
  but prevent indexing into the sequence itself or subsequences. Instead,
  we hide that aspect of the algebraic encoding, making
  \Con{init} (containing the sequence of arguments)
  seem like one big $n$-ary tuple, rather than containing $n$ nested
  pairs.
}
\begin{enumerate}
\item{\textbf{Case} (\Data{Fin} \Num{1})}
  There is only one possible index, so we define a \Con{here} case
  that returns the value at this index.
\item{\textbf{Case} (\Data{Fin} (\Num{1} \Fun{+} \Var{n}))}
  We define a \Con{here} case (for the \Num{1}),
  returning the value at this index.
  We also define a \Con{there} case (for the \Var{n}),
  giving us a new argument of type \Data{Fin} \Var{n}.
  In the \Con{there} case, we return
  the recursive call of \Fun{lookup} or \Fun{lookups},
  depending on whether \Var{n} is \Fun{count} or \Fun{counts}.
\item{\textbf{Case} (\Data{Fin} (\Var{n} \Fun{+} \Var{m}))}
  There is only one possible index, so we define its
  \Con{there} case (for \Var{n} \Fun{+} \Var{m}).
  Within the \Con{there} case, we must translate the single
  \Data{Fin} (\Var{n} \Fun{+} \Var{m}) index to the disjoint union of
  the two potential indices \Data{Fin} \Var{n} \Data{⊎} \Data{Fin} \Var{m}.
  After case-analyzing the disjoint union (\Data{⊎}),
  we make a recursive call using the index within the
  left (\Con{inj₁}) or right (\Con{inj₂}) injection. Once again, the
  recursive call is either \Fun{lookup} or \Fun{lookups}, depending on
  whether \Var{n} or \Var{m}
  (whichever one we find in the disjoint union)
  is \Fun{count} or \Fun{counts}.
\end{enumerate}



To know which \textbf{Case} template to use for \Fun{lookups} at some
description \Var{D}, match the template with the \Var{D} case
of \Fun{counts} in \refsec{counts}.

\paragraph{Non-Inductive Argument}

For the (only) \Con{there} case of a non-inductive argument
(\textbf{Case 3}), in a sequence of arguments,
we use the helper function \Fun{splitσ}.
The helper function turns \Var{i}, a single index (\Data{Fin})
containing a sum (\Fun{+}), into a disjoint union (\Data{⊎})
of two indices. While \Fun{splitΣ} operates over a dependent pair,
\Fun{splitσ} is specialized to operate over a non-inductive argument
(\Var{a}) and its dependent sequence (\Var{xs}).

\begin{code}
  -- i : Fin (count A a + counts (D a) R xs)
  lookups (`σ A D) R (a , xs) i with splitσ A D R a xs i
  -- j  : Fin (count A a)
  ... | inj₁ j = lookup A a j
  -- j : Fin (counts (D a) R xs)
  ... | inj₂ j = lookups (D a) R xs j
\end{code}

If the disjoint union is the left injection
(\Con{inj₁}), we recursively \Fun{lookup} 
the non-inductive argument (\Var{a}).
If the disjoint union is the right injection
(\Con{inj₂}), we recursively \Fun{lookups} the tail of the
sequence of arguments (\Var{xs}).

\paragraph{Inductive Argument}

For the (only) \Con{there} case of an inductive argument
(\textbf{Case 3}), in a sequence of
arguments, we use the helper function \Fun{splitδ}.
The helper function turns \Var{i}, a single index (\Data{Fin})
containing a sum (\Fun{+}), into a disjoint union (\Data{⊎})
of two indices. The \Fun{splitδ} function is specialized to work with
an \textit{inductive} (i.e. not infinitary) argument, and its
dependent sequence (\Var{xs}). Hence, we apply \Fun{splitδ}
to (\Var{f} \Con{tt}), computing the inductive codomain from the
trivially infinitary \Var{f}.

\begin{code}
  -- i : Fin (count (`μ₁ _ R) (f tt) + counts (D (μ₂ ⟪ R ⟫ ∘ f)) R xs)
  lookups (`δ `⊤ D) R (f , xs) i with splitδ (D ∘ const) R (f tt) xs i
  -- j : Fin (count (`μ₁ _ R) (f tt))
  ... | inj₁ j = lookup (`μ₁ _ R) (f tt) j
  -- j : Fin (counts (D (μ₂ ⟪ R ⟫ ∘ f)) R xs)
  ... | inj₂ j = lookups (D (μ₂ ⟪ R ⟫ ∘ f)) R xs j
\end{code}

\paragraph{Infinitary Argument}

For the \Con{there} case of an infinitary argument (\textbf{Case 2}),
in a sequence of arguments,
we recursively \Fun{lookups} its arguments (\Var{xs}).

\begin{code}
  lookups (`δ A@`Bool D) R (f , xs) (there i) = lookups (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i
\end{code}

\AgdaHide{
\begin{code}
  lookups (`δ A@`⊥ D) R (f , xs) (there i) = lookups (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i
  lookups (`δ A@`String D) R (f , xs) (there i) = lookups (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i
  lookups (`δ A@(`Σ _ _) D) R (f , xs) (there i) = lookups (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i
  lookups (`δ A@(`Π _ _) D) R (f , xs) (there i) = lookups (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i
  lookups (`δ A@(`Id  _ _ _) D) R (f , xs) (there i) = lookups (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i
  lookups (`δ A@(`μ₁ _ _) D) R (f , xs) (there i) = lookups (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i
\end{code}}

For the \Con{here} case of an infinitary argument (\textbf{Case 1}),
we return the infinitary function. The type of infinitary function
has the type meaning (\Fun{⟦\_⟧}) of \Var{A} as its domain,
and the type component of the fixpoint \Data{μ₁}, applied
to the description meaning (\Fun{⟪\_⟫}) of \Var{R}, as its
codomain.

\begin{code}
  lookups D@(`δ A@`Bool _) R (f , xs) here = (⟦ A ⟧ → μ₁ _ ⟪ R ⟫) , f
\end{code}


Recall that \Fun{lookup} (in \refsec{lookup}, as a special case
of \textbf{Remaining Values}) only has a \Con{here} case for
functions (\Con{`Π}). Similarly, there is only a \Con{here} case
of \Fun{lookups} for infinitary functions
(\Con{`δ}, where \Var{A} is not \Con{`⊤}). This is because we treat
functions as a black box, so we can point at an entire
function (using \Con{here}),
but not something within its body
(using \Con{there}).

\AgdaHide{
\begin{code}
  lookups D@(`δ A@`⊥ _) R (f , xs) here = (⟦ A ⟧ → μ₁ _ ⟪ R ⟫) , f
  lookups D@(`δ A@`String _) R (f , xs) here = (⟦ A ⟧ → μ₁ _ ⟪ R ⟫) , f
  lookups D@(`δ A@(`Σ _ _) _) R (f , xs) here = (⟦ A ⟧ → μ₁ _ ⟪ R ⟫) , f
  lookups D@(`δ A@(`Π _ _) _) R (f , xs) here = (⟦ A ⟧ → μ₁ _ ⟪ R ⟫) , f
  lookups D@(`δ A@(`Id _ _ _) _) R (f , xs) here = (⟦ A ⟧ → μ₁ _ ⟪ R ⟫) , f
  lookups D@(`δ A@(`μ₁ _ _) _) R (f , xs) here = (⟦ A ⟧ → μ₁ _ ⟪ R ⟫) , f
\end{code}}

\paragraph{Last Argument}

Finally, the \Con{here} case of the last argument (\textbf{Case 1}),
described by \Con{`ι} , simply returns the unit type and value.

\begin{code}
  lookups (`ι o) R tt here = ⊤ , tt
\end{code}

Note also that \Con{`ι} does not have a \Con{there} case, because it
encodes and final argument, so there is nothing left to index.

\AgdaHide{
\begin{code}
  lookups D@(`ι _) R tt (there ())
\end{code}}

\AgdaHide{
\begin{code}
  lookup₁ : (A : `Set) (a : ⟦ A ⟧)
    → Fin (count A a) → Set
  lookup₁ A a i = proj₁ (lookup A a i)

  lookup₂ : (A : `Set) (a : ⟦ A ⟧)
    (i : Fin (count A a)) → lookup₁ A a i
  lookup₂ A a i = proj₂ (lookup A a i)

  lookups₁ : {O : `Set} (D R : `Desc O) (xs : ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫)
   → Fin (counts D R xs) → Set
  lookups₁ D R xs i = proj₁ (lookups D R xs i)

  lookups₂ : {O : `Set} (D R : `Desc O) (xs : ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫)
   (i : Fin (counts D R xs)) → lookups₁ D R xs i
  lookups₂ D R xs i = proj₂ (lookups D R xs i)
\end{code}}


\subsection{Examples}\label{sec:glookup:egs}

Now we run \Fun{lookup} on some examples. The expected behavior of
\Fun{lookup} is to return the value associated with the $n$th
(where $n$ is the \Data{Fin} index) position in a depth-first search.
Hence, \Con{here} of type \Data{Fin} corresponds to the position 0, and
\Con{there} \Var{i} of type \Data{Fin} corresponds to the successor of
the position associated with \Var{i}.

\paragraph{Natural Numbers}

Let's \Fun{lookup₂} some values in the closed
natural number \Fun{two}.\footnote{
  Recall that we define \Fun{lookup} as a dependent pair, where
  the first component is a type and the second component is a value
  (whose type is the first component). As a shorthand, \Fun{lookup₁}
  refers to the type component, while \Fun{lookup₂} refers to the
  value component.
}
To see the expected value of
\Fun{lookup₂} for \Fun{two} at some index, simply consult
\reffig{two}. The labels in the \reffig{two} correspond to natural
number indices, ordered according to a depth-first search.
Thus, by viewing \Con{here} of \Data{Fin}
as \Con{zero} of \Data{ℕ}, and
\Con{there} of \Data{Fin} as
\Con{suc} of \Data{ℕ}, we can always consult the figure to determine
the expected return value of \Fun{lookup₂}.

Looking up index \Con{here} corresponds to position 0, or the
root node in \reffig{two}. Hence, \Fun{lookup₂} using index \Con{here}
is the identity function.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Fin renaming ( zero to here ; suc to there )
 open Lookup
 open Count.Data
 open Count.VecEg
 private
\end{code}}

\AgdaHide{
\begin{code}
  _ :
\end{code}}

\begin{code}
   lookup₂ `ℕ two here ≡ two
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}


If we lookup position 1 (using index \Con{there} \Con{here})
of \Fun{two} (visualized by \reffig{two}),
we get \Con{false} (encoding the choice of the \Fun{cons}
constructor).

\AgdaHide{
\begin{code}
  _ :
\end{code}}

\begin{code}
   lookup₂ `ℕ two (there here) ≡ false
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}

If we lookup position 2 (using index \Con{there} (\Con{there}
\Con{here})) of \Fun{two} (visualized by \reffig{two}),
we get \Fun{one} (visualized by \reffig{one}).

\AgdaHide{
\begin{code}
  _ :
\end{code}}

\begin{code}
   lookup₂ `ℕ two (there (there here)) ≡ one
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}

To make lookups of higher positions more readable,
we use a helper function (\Fun{\#}) coercing natural numbers
to finite sets by converting \Con{zero} to \Con{here},
and \Con{suc} to \Con{there}. Therfore,
we can repeat the \Fun{lookup₂} of
position 2 above as follows.

\AgdaHide{
\begin{code}
  _ :
\end{code}}

\begin{code}
   lookup₂ `ℕ two (# 2) ≡ one
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}

Finally, looking up position 4 of \Fun{two}
results in \Fun{zero}.

\AgdaHide{
\begin{code}
  _ :
\end{code}}

\begin{code}
   lookup₂ `ℕ two (# 4) ≡ zero
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}

\paragraph{Vectors}

Looking up vectors is just as easy as looking up natural numbers, by
considering the \Data{Fin} argument as a natural number index
of a depth-first traversal of the closed value.
For example, the \Fun{lookup₂} of \Fun{vec2}
(visualized by \reffig{vec2})
at position 3
is the natural number \Fun{one} (visualized by \reffig{one}).

\AgdaHide{
\begin{code}
  _ :
\end{code}}

\begin{code}
   lookup₂ (`Vec (`String `× `String) two) vec2 (# 3) ≡ one
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}

The \Fun{lookup₂} of \Fun{vec2}
(visualized by \reffig{vec2})
at position 10 is the string \Str{"x"}.

\AgdaHide{
\begin{code}
  _ :
\end{code}}

\begin{code}
   lookup₂ (`Vec (`String `× `String) one) vec1 (# 8) ≡ "x"
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}

\begin{figure}[ht]
\centering
\includegraphics[scale=0.7]{vec21.pdf}  
\caption{The inductive-recursive component of the
  length-1 vector of pairs of strings
  \texttt{[("b", "y")]}, as a closed algebraic type.
  Recall that indexed vectors are encoded as a dependent pair,
  where the first component is an inductive-recursive value and the
  second component is a length constraint. This figure depicts the
  first component of the vector.}
\label{fig:vec21}
\end{figure}

Finally, the \Fun{lookup₂} of \Fun{vec2}
(visualized by \reffig{vec2})
at position 12
is the inductive-recursive component
of the vector \texttt{[("b", "y")]}
(visualized by \reffig{vec21}).

\AgdaHide{
\begin{code}
  _ :
\end{code}}

\begin{code}
   lookup₂ (`Vec (`String `× `String) two) vec2 (# 12) ≡ cons₁ ("b" , "y") nil
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}

\AgdaHide{
\begin{code}
  _ :

   lookup₂ (`Vec (`String `× `String) one) vec1 (# 9) ≡ nil₁
  _ = refl
\end{code}}
