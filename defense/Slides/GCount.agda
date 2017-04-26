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
    counts : (D : `Desc) (X : `Set) → ⟬ ⟪ D ⟫ ⟭ ⟦ X ⟧ → ℕ

module _ where
 private
  mutual
    count : (A : `Set) → ⟦ A ⟧ → ℕ
    count (`Σ A B) (a , b) = 1 + count A a + count (B a) b
    count (`μ D) (init xs) = 1 + counts D (`μ D) xs
    count A a = 1
    
    counts : (D : `Desc) (X : `Set) → ⟬ ⟪ D ⟫ ⟭ ⟦ X ⟧ → ℕ
    counts (`σ A D) X (a , xs) = count A a + counts (D a) X xs
    counts (`δ D) X (x , xs) = count X x + counts D X xs
    counts `ι X tt = 1


module _ where
 private
  postulate
    Generic : (A : `Set) → ⟦ A ⟧ → Set
    Generics : (D : `Desc) (X : `Set) → ⟬ ⟪ D ⟫ ⟭ ⟦ X ⟧ → Set

    generic : (A : `Set) (a : ⟦ A ⟧) → Generic A a
    generics : (D : `Desc) (X : `Set) (xs : ⟬ ⟪ D ⟫ ⟭ ⟦ X ⟧) → Generics D X xs
