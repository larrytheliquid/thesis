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
  lookup (`μ₁ O D) (init xs) (there i) = lookups D D xs i

  lookup A@`⊥ a i = ⟦ A ⟧ , a
  lookup A@`⊤ a i = ⟦ A ⟧ , a
  lookup A@`Bool a i = ⟦ A ⟧ , a
  lookup A@`String a i = ⟦ A ⟧ , a
  lookup A@(`Σ _ _) a here = ⟦ A ⟧ , a
  lookup A@(`Π _ _) a i = ⟦ A ⟧ , a
  lookup A@(`Id _ _ _) a i = ⟦ A ⟧ , a
  lookup A@(`μ₁ _ _) a@(init _) here = ⟦ A ⟧ , a

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
