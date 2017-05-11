module Slides.GCount where
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Nat
open import Data.Product
open import Slides.OpenAlg
open import Slides.ClosedAlg

module _ where
 private
  postulate
    count : (A : `Set) → ⟦ A ⟧ → ℕ
    countFix : (D : `Desc) → μ ⟪ D ⟫ → ℕ

module _ where
 private
  postulate
    count : (A : `Set) → ⟦ A ⟧ → ℕ
    counts : (D : `Desc) (X : `Set) → ⟬ ⟪ D ⟫ ⟭ ⟦ X ⟧ → ℕ

module _ where
 private
  mutual
    count : (A : `Set) → ⟦ A ⟧ → ℕ
    count (A `⊎ B) (inj₁ a) = 1 + count A a
    count (A `⊎ B) (inj₂ b) = 1 + count B b
    count (`Σ A B) (a , b) = 1 + count A a + count (B a) b
    count (`μ D) (init xs) = 1 + counts D (`μ D) xs
    count A a = 1
    
    counts : (D : `Desc) (X : `Set) → ⟬ ⟪ D ⟫ ⟭ ⟦ X ⟧ → ℕ
    counts (D `⊕ E) X (inj₁ xs) = counts D X xs
    counts (D `⊕ E) X (inj₂ ys) = counts E X ys
    counts (D `⊗ E) X (xs , ys) = counts D X xs + counts E X ys
    counts (`κ A) X a = count A a
    counts `ι X x = count X x


module _ where
 private
  postulate
    Generic : (A : `Set) → ⟦ A ⟧ → Set
    Generics : (D : `Desc) (X : `Set) → ⟬ ⟪ D ⟫ ⟭ ⟦ X ⟧ → Set

    generic : (A : `Set) (a : ⟦ A ⟧) → Generic A a
    generics : (D : `Desc) (X : `Set) (xs : ⟬ ⟪ D ⟫ ⟭ ⟦ X ⟧) → Generics D X xs

