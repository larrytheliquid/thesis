module Slides.NaiveAlg where
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Slides.OpenAlg

mutual
  data `Set : Set₁ where
    `⊥ `⊤ `Bool : `Set
    `Σ `Π : (A : `Set) (B : ⟦ A ⟧ → `Set) → `Set
    `Id : (A : `Set) (x y : ⟦ A ⟧) → `Set
    `μ : (D : Desc) → `Set
  
  ⟦_⟧ : `Set → Set
  ⟦ `⊥ ⟧ = ⊥
  ⟦ `⊤ ⟧ = ⊤
  ⟦ `Bool ⟧ = Bool
  ⟦ `Σ A B ⟧ = Σ ⟦ A ⟧ (λ a → ⟦ B a ⟧)
  ⟦ `Π A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
  ⟦ `Id A x y ⟧ = Id ⟦ A ⟧ x y
  ⟦ `μ D ⟧ = μ D

module _ where
 private
  `Truth : `Set
  `Truth = `Π `Bool (λ b → if b then `⊤ else `⊥)

  ListD : Set → Desc
  ListD A = σ Bool
    (λ b → if b then ι else σ A (λ a → δ ι))

  `List : `Set → `Set
  `List A = `μ (ListD ⟦ A ⟧)

