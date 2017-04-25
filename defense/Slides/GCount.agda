module Slides.GCount where
open import Data.Empty
open import Data.Unit
open import Data.Bool
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
    counts : (D R : `Desc) → ⟬ ⟪ D ⟫ ⟭ (μ ⟪ R ⟫) → ℕ

module _ where
 private
  mutual
    count : (A : `Set) → ⟦ A ⟧ → ℕ
    count (`Σ A B) (a , b) = 1 + count A a + count (B a) b
    count (`μ D) (init xs) = 1 + counts D D xs
    count A a = 1
    
    counts : (D R : `Desc) → ⟬ ⟪ D ⟫ ⟭ (μ ⟪ R ⟫) → ℕ
    counts (`σ A D) R (a , xs) = count A a + counts (D a) R xs
    counts (`δ D) R (x , xs) = count (`μ R) x + counts D R xs
    counts `ι R tt = 1

