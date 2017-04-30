module Slides.NaiveAlg where
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Slides.OpenAlg

mutual
  data `Set : Set₁ where
    `⊥ `⊤ : `Set
    _`⊎_ : (A B : `Set) → `Set
    `Σ `Π : (A : `Set) (B : ⟦ A ⟧ → `Set) → `Set
    `Id : (A : `Set) (x y : ⟦ A ⟧) → `Set
    `μ : (D : Desc) → `Set
  
  ⟦_⟧ : `Set → Set
  ⟦ `⊥ ⟧ = ⊥
  ⟦ `⊤ ⟧ = ⊤
  ⟦ A `⊎ B ⟧ = ⟦ A ⟧ ⊎ ⟦ B ⟧
  ⟦ `Σ A B ⟧ = Σ ⟦ A ⟧ (λ a → ⟦ B a ⟧)
  ⟦ `Π A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
  ⟦ `Id A x y ⟧ = Id ⟦ A ⟧ x y
  ⟦ `μ D ⟧ = μ D

module _ where
 private
  `Bool : `Set
  `Bool = `⊤ `⊎ `⊤

  `ListD : Set → Desc
  `ListD A = κ ⊤ ⊕ (κ A ⊗ ι)

  `List : `Set → `Set
  `List A = `μ (`ListD ⟦ A ⟧)

