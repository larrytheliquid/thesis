\AgdaHide{
\begin{code}
module _ where
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Function
open import Appendix
open import Data.Product
open import Data.List
open import Count
open import Lookup
open Prim  hiding ( Σ )
data W (A : Set) (B : A → Set) : Set where
  sup : (a : A) (f : B a → W A B) → W A B
\end{code}}

\chapter{Closed Hierarchy of Universes}\label{ch:hier}

\refchap{closed} demonstrates closing a universe of
algebraic (inductive-recursive) \textit{types}, and
\refchap{fullyg} demonstrates fully generic programming over that
universe. In this chapter, we expand the closed universe of
\refsec{closed} to also include \textit{kinds},
\textit{superkinds}, and an infinite hierarchy of such
classifications. Types (\Data{Set}) are classified by
kinds (\Data{Set₁}).
$$
\Data{Set} : \Data{Set₁}
$$

Going one level up, kinds (\Data{Set₁}) are classified
by superkinds (\Data{Set₂}).
$$
\Data{Set₁} : \Data{Set₂}
$$

This pattern repeats itself indefinitely. We refer to any such
construction (e.g. a type, or a kind, or a superkind, etc.) as a
\textit{universe}. In \refsec{closed}, we only considered the first
(or zeroth, because we count universe levels by starting with 0)
closed universe (i.e. the universe of types, classified by kinds). Now, we expand this
notion to a closed infinite hierarchy of universes, where each universe in
the hierarchy is classified by another universe, one level above.
$$
\Data{Set}_{\Var{n}} : \Data{Set}_{\Con{suc}~\Var{n}}
$$

There are 3 primary things we achieve by creating a closed hierarchy
of universes:
\begin{enumerate}
\item We can encode formers and constructors of kinds (as well as
  superkinds, etc.) in the closed hierarchy. This includes the two
  primitive kinds, closed types (\Con{`Set}) and
  closed descriptions (\Con{`Desc}). It also includes closed algebraic
  user-declared kinds, such as heterogenous lists (\Fun{`HList}).
\item We can write \textit{leveled} fully generic functions.
  By this we mean universe polymorphic fully generic functions,
  which can be applied to members of any universe in the hierarchy.
  Hence, we can extend fully generic functions
  (like \Fun{count}, \Fun{lookup}, \Fun{ast}, etc.)
  from working over all types and their values,
  to working over all kinds and their types
  (and all superkinds and their kinds, etc.).
\item We can \textit{internalize} the kind (and superkind, etc.)
  signatures of formers, constructors, and functions, by writing them
  as the meaning of a closed code in our universe.
\end{enumerate}

Let's clarify what we mean by the third point, above.
Throughout this disseration we have written the signatures of
closed formers, constructors, and functions using our Agda metatheory,
which is \textit{external} to our closed universe. For example,
consider the \textit{type} signature of the \Fun{suc}cessor of closed
natural numbers, below.

\AgdaHide{
\begin{code}
module _ where
 open Closed
 private 
  postulate
   `ℕ : `Set
\end{code}}

\begin{code}
   suc : (n : ⟦ `ℕ ⟧) → ⟦ `ℕ ⟧
\end{code}

The type signature of \Fun{suc} uses Agda's \textit{open} dependent
function type (→). Instead, we may \textit{internalize} the type
signature of \Fun{suc} as the meaning (\Fun{⟦\_⟧})
of a \textit{closed} dependent
function (\Con{`Π}).

\AgdaHide{
\begin{code}
module _ where
 open Closed
 private 
  postulate
   `ℕ : `Set
\end{code}}

\begin{code}
   suc : ⟦ `Π `ℕ (λ n → `ℕ) ⟧
\end{code}

Another way to look at it, is that we can fit the entire type
signature of \Fun{suc} into the meaning brackets (\Fun{⟦\_⟧}),
as a single closed type (\Data{`Set}).
In contrast, let's consider the \textit{kind} signature of the
\Fun{cons} constructor of closed parameterized lists.

\AgdaHide{
\begin{code}
module _ where
 open Closed
 private 
  postulate
   `List : `Set → `Set
\end{code}}

\begin{code}
   cons : (A : `Set) (a : ⟦ A ⟧) (xs : ⟦ `List A ⟧) → ⟦ `List A ⟧
\end{code}

We cannot internalize the \textit{kind} signature of the \Fun{cons}
function. Even though \Fun{cons} returns a list value, its signature
is kinded because the \Var{A} argument is a kind (\Data{`Set}).
We would like to internalize the kind of \Fun{cons} as
3 nested uses of \Con{`Π}
(for arguments \Var{A}, \Var{a}, and \Var{xs}).
However, the domain of the first \Con{`Π}
would need to be a constructor of closed kinds (\Con{`Set}),
which does not exist in the universe of closed types
(\refapen{closed}).

Similarly, we cannot internalize the kind signature of fully generic
functions (like \Fun{count}),
or even parametrically polymorphic functions
(like the \Fun{id}entity function),
because they need to equantify over all
closed types. By defining a closed hierarchy of universes
in \refsec{hierir}, we \textit{can} internalize
kind (and superkind, etc.) signatures,
thereby fitting them within meaning brackets.

\section{Closed Hierarchy of Well-Order Types}\label{sec:hierw}

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 private 
  {-# NO_POSITIVITY_CHECK #-}
\end{code}}

\begin{code}
  mutual
    data `Set[_] : ℕ → Set where
      `⊥ `⊤ `Bool : ∀{ℓ} → `Set[ ℓ ]
      `Σ `Π `W : ∀{ℓ} (A : `Set[ ℓ ]) (B : ⟦ ℓ ∣ A ⟧ → `Set[ ℓ ]) → `Set[ ℓ ]
      `Id : ∀{ℓ} (A : `Set[ ℓ ]) (x y : ⟦ ℓ ∣ A  ⟧) → `Set[ ℓ ]
      `Set : ∀{ℓ} → `Set[ suc ℓ ]
      `⟦_⟧ : ∀{ℓ} → `Set[ ℓ ] → `Set[ suc ℓ ]

    ⟦_∣_⟧ : (ℓ : ℕ) → `Set[ ℓ ] → Set
    ⟦ ℓ ∣ `⊥ ⟧ = ⊥
    ⟦ ℓ ∣ `⊤ ⟧ = ⊤
    ⟦ ℓ ∣ `Bool ⟧ = Bool
    ⟦ ℓ ∣ `Σ A B ⟧ = Σ ⟦ ℓ ∣ A ⟧ (λ a → ⟦ ℓ ∣ B a ⟧)
    ⟦ ℓ ∣ `Π A B ⟧ = (a : ⟦ ℓ ∣ A ⟧) → ⟦ ℓ ∣ B a ⟧
    ⟦ ℓ ∣ `W A B ⟧ = W ⟦ ℓ ∣ A ⟧ (λ a → ⟦ ℓ ∣ B a ⟧)
    ⟦ ℓ ∣ `Id A x y ⟧ = Id ⟦ ℓ ∣ A ⟧ x y
    ⟦ suc ℓ ∣ `Set ⟧ = `Set[ ℓ ]
    ⟦ suc ℓ ∣ `⟦ A ⟧ ⟧ = ⟦ ℓ ∣ A ⟧
\end{code}

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 private 
\end{code}}

\begin{code}
  record Level : Set₁ where
    field
      `SetForm : Set
      ⟦_/_⟧ : `SetForm → Set
\end{code}

\begin{code}
  mutual
    data `SetForm (ℓ : Level) : Set where
      `⊥ `⊤ `Bool : `SetForm ℓ
      `Σ `Π `W : (A : `SetForm ℓ) (B : ⟦ ℓ / A ⟧ → `SetForm ℓ) → `SetForm ℓ
      `Id : (A : `SetForm ℓ) (x y : ⟦ ℓ / A  ⟧) → `SetForm ℓ
      `Set : `SetForm ℓ
      `⟦_⟧ : Level.`SetForm ℓ → `SetForm ℓ

    ⟦_/_⟧ : (ℓ : Level) → `SetForm ℓ → Set
    ⟦ ℓ / `⊥ ⟧ = ⊥
    ⟦ ℓ / `⊤ ⟧ = ⊤
    ⟦ ℓ / `Bool ⟧ = Bool
    ⟦ ℓ / `Σ A B ⟧ = Σ ⟦ ℓ / A ⟧ (λ a → ⟦ ℓ / B a ⟧)
    ⟦ ℓ / `Π A B ⟧ = (a : ⟦ ℓ / A ⟧) → ⟦ ℓ / B a ⟧
    ⟦ ℓ / `W A B ⟧ = W ⟦ ℓ / A ⟧ (λ a → ⟦ ℓ / B a ⟧)
    ⟦ ℓ / `Id A x y ⟧ = Id ⟦ ℓ / A ⟧ x y
    ⟦ ℓ / `Set ⟧ = Level.`SetForm ℓ
    ⟦ ℓ / `⟦ A ⟧ ⟧ = Level.⟦ ℓ / A ⟧
\end{code}

\begin{code}
  level : (ℓ : ℕ) → Level
  level zero = record
    { `SetForm = ⊥
    ; ⟦_/_⟧ = λ()
    }
  level (suc ℓ) = record
    { `SetForm = `SetForm (level ℓ)
    ; ⟦_/_⟧ = ⟦_/_⟧ (level ℓ)
    }
\end{code}

\begin{code}
  `Set[_] : ℕ → Set
  `Set[ ℓ ] = `SetForm (level ℓ)

  ⟦_∣_⟧ : (ℓ : ℕ) → `Set[ ℓ ] → Set
  ⟦ ℓ ∣ A ⟧ = ⟦ level ℓ / A ⟧
\end{code}

\section{Closed Hierarchy of Well-Order Types}\label{sec:hierw}
\section{Closed Hierarchy of Inductive-Recursive Types}\label{sec:hierir}
\section{Leveled Fully Generic Domain}\label{sec:gdom}
