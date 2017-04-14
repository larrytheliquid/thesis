\AgdaHide{
\begin{code}
module _ where
open import Data.Nat
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


\section{Closed Hierarchy of Well-Order Types}\label{sec:hierw}

\AgdaHide{
\begin{code}
module _ where
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
