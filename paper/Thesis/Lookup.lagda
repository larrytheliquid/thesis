\AgdaHide{
\begin{code}
module _ where
open import Data.Sum
open import Data.Nat
open import Data.Fin hiding ( _+_ ) renaming ( zero to here ; suc to there )
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

\section{Fully Generic Lookup}\label{sec:glookup}

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

\begin{code}
  lookup : (A : `Set) (a : ⟦ A ⟧) → Fin (count A a) → Σ Set (λ A → A)
  -- i : Fin (count A a + count (B a) b)
  lookup (`Σ A B) (a , b) (there i) with splitΣ A B a b i
  -- j : Fin (count A a)
  ... | inj₁ j = lookup A a j
  -- j : Fin (count (B a) b)
  ... | inj₂ j = lookup (B a) b j
  -- i : Fin (counts D D xs)
  lookup (`μ₁ A D) (init xs) (there i) = lookups D D xs i
  lookup A@`⊥ a i = ⟦ A ⟧ , a
  lookup A@`⊤ a i = ⟦ A ⟧ , a
  lookup A@`Bool a i = ⟦ A ⟧ , a
  lookup A@`String a i = ⟦ A ⟧ , a
  lookup A@(`Σ _ _) a here = ⟦ A ⟧ , a
  lookup A@(`Π _ _) a i = ⟦ A ⟧ , a
  lookup A@(`Id _ _ _) a i = ⟦ A ⟧ , a
  lookup A@(`μ₁ _ _) a@(init _) here = ⟦ A ⟧ , a

  lookups : {O : `Set} (D R : `Desc O) (xs : ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫) → Fin (counts D R xs) → Σ Set (λ A → A)
  lookups (`σ A D) R xs i = {!!}
  lookups (`δ `⊤ D) R xs i = {!!}
  lookups (`δ `⊥ D) R xs i = {!!}
  lookups (`δ `Bool D) R xs i = {!!}
  lookups (`δ `String D) R xs i = {!!}
  lookups (`δ (`Σ A B) D) R xs i = {!!}
  lookups (`δ (`Π A B) D) R xs i = {!!}
  lookups (`δ (`Id A x y) D) R xs i = {!!}
  lookups (`δ (`μ₁ A D) D₁) R xs i = {!!}
  lookups (`ι o) R xs i = {!!}
\end{code}
