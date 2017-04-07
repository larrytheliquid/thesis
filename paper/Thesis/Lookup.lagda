\AgdaHide{
\begin{code}
module _ where
open import Data.Sum
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Function
open import Appendix
open import Data.Product
open import Count
open Prim  hiding ( Σ )
open Alg
open Closed
open Count.Count
\end{code}}

\AgdaHide{
\begin{code}
module _ where
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
composing our new functions with the first (\Fun{proj₁}) and
second (\Fun{proj₂}) projections of dependent pairs (\Data{Σ}).

\subsection{Looking Up All Values}\label{sec:lookup}

\AgdaHide{
\begin{code}
module Lookup where
 postulate
   splitΣ : (A : `Set) (B : ⟦ A ⟧ → `Set)
     (a : ⟦ A ⟧) (b : ⟦ B a ⟧) →
     Fin (count A a + count (B a) b) →
     Fin (count A a) ⊎ Fin (count (B a) b)
   splitσ : {O : `Set} (A : `Set) (D : ⟦ A ⟧ → `Desc O) (R : `Desc  O)
     (a : ⟦ A ⟧) (xs : ⟦ ⟪ D a ⟫ ⟧₁ ⟪ R ⟫) →
     Fin (count A a + counts (D a) R xs) →
     Fin (count A a) ⊎ Fin (counts (D a) R xs)
   splitδ : {O : `Set} (D : ⟦ O ⟧ → `Desc O) (R : `Desc  O)
     (x : μ₁ ⟦ O ⟧ ⟪ R ⟫) (xs : ⟦ ⟪ D (μ₂ ⟪ R ⟫ x) ⟫ ⟧₁ ⟪ R ⟫) →
     Fin (count (`μ₁ O R) x + counts (D (μ₂ ⟪ R ⟫ x)) R xs) →
     Fin (count (`μ₁ O R) x) ⊎ Fin (counts (D (μ₂ ⟪ R ⟫ x)) R xs)
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
\item{\textbf{Case} (\Data{Fin} (\Num{1} + \Var{n}))}
  We define a \Con{here} case (for the \Num{1}),
  returning the value at this index.
  We also define a \Con{there} case (for the \Var{n}),
  giving us a new argument of type \Data{Fin} \Var{n}.
  In the \Con{there} case, we return
  the recursive call of \Fun{lookup} or \Fun{lookups},
  depending on whether \Var{n} is \Fun{count} or \Fun{counts}.
\item{\textbf{Case} (\Data{Fin} (\Num{1} + \Var{n} + \Var{m}))}
  We define a \Con{here} case (for the \Num{1}),
  returning the value at this index.
  We also define a \Con{there} case (for the \Var{n} + \Var{m}),
  giving us a new argument of type \Data{Fin} (\Var{n} + \Var{m}).
  Within the \Con{there} case, we must translate the single
  \Data{Fin} (\Var{n} + \Var{m}) index to the disjoint union of
  the two potential indices \Data{Fin} \Var{n} \Data{⊎} \Data{Fin} \Var{m}.
  After case-analyzing the disjoint union (\Data{⊎}),
  we make a recursive call using the index within the
  left (\Con{inj₁}) or right (\Con{inj₂}) injection. Once again, the
  recursive call is either \Fun{lookup} or \Fun{lookups}, depending on
  whether \Var{n} or \Var{m}
  (whichever one we find in the disjoint union)
  is \Fun{count} or \Fun{counts}.
\end{enumerate}

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
meaning function (\Fun{⟦\_⟧}) applied to its
closed type (\Var{A}), as a dependent pair (\Con{,}).

\begin{code}
  lookup A@(`Σ _ _) a here = ⟦ A ⟧ , a
\end{code}

For \Con{`μ₁} this is the \Con{here} component of the
definition of \textbf{Case 2}, and for \Con{`Σ} this is the
\Con{here} component of the definition of \textbf{Case 3}.
For all other types, this is the definition of
\textbf{Case 1} (which does not have a \Con{there} component).

\AgdaHide{
\begin{code}
  lookup A@`⊥ a i = ⟦ A ⟧ , a
  lookup A@`Bool a i = ⟦ A ⟧ , a
  lookup A@`⊤ a i = ⟦ A ⟧ , a
  lookup A@`String a i = ⟦ A ⟧ , a
  lookup A@(`Π _ _) a i = ⟦ A ⟧ , a
  lookup A@(`Id _ _ _) a i = ⟦ A ⟧ , a
  lookup A@(`μ₁ _ _) a@(init _) here = ⟦ A ⟧ , a
\end{code}}

\subsection{Looking Up Algebraic Arguments}\label{sec:lookups}

\begin{code}
  lookups : {O : `Set} (D R : `Desc O) (xs : ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫)
    → Fin (counts D R xs) → Σ Set (λ A → A)

  -- i : Fin (count A a + counts (D a) R xs)
  lookups (`σ A D) R (a , xs) i with splitσ A D R a xs i
  -- j  : Fin (count A a)
  ... | inj₁ j = lookup A a j
  -- j : Fin (counts (D a) R xs)
  ... | inj₂ j = lookups (D a) R xs j

  -- i : Fin (count (`μ₁ _ R) (f tt) + counts (D (μ₂ ⟪ R ⟫ ∘ f)) R xs)
  lookups (`δ `⊤ D) R (f , xs) i with splitδ (D ∘ const) R (f tt) xs i
  -- j : Fin (count (`μ₁ _ R) (f tt))
  ... | inj₁ j = lookup (`μ₁ _ R) (f tt) j
  -- j : Fin (counts (D (μ₂ ⟪ R ⟫ ∘ f)) R xs)
  ... | inj₂ j = lookups (D (μ₂ ⟪ R ⟫ ∘ f)) R xs j

  lookups D@(`ι _) R xs i = ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫ , xs
  lookups D@(`δ `⊥ _) R xs here = ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫ , xs
  lookups D@(`δ `Bool _) R xs here = ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫ , xs
  lookups D@(`δ `String _) R xs here = ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫ , xs
  lookups D@(`δ (`Σ _ _) _) R xs here = ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫ , xs
  lookups D@(`δ (`Π _ _) _) R xs here = ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫ , xs
  lookups D@(`δ (`Id _ _ _) _) R xs here = ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫ , xs
  lookups D@(`δ (`μ₁ _ _) _) R xs here = ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫ , xs

  lookups (`δ A@`⊥ D) R (f , xs) (there i) = lookups (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i
  lookups (`δ A@`Bool D) R (f , xs) (there i) = lookups (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i
  lookups (`δ A@`String D) R (f , xs) (there i) = lookups (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i
  lookups (`δ A@(`Σ _ _) D) R (f , xs) (there i) = lookups (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i
  lookups (`δ A@(`Π _ _) D) R (f , xs) (there i) = lookups (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i
  lookups (`δ A@(`Id  _ _ _) D) R (f , xs) (there i) = lookups (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i
  lookups (`δ A@(`μ₁ _ _) D) R (f , xs) (there i) = lookups (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i
\end{code}