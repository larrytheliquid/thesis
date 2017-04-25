module Slides.ClosedAlg where
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Slides.OpenAlg

mutual
  data `Set : Set where
    `⊥ `⊤ `Bool : `Set
    `Σ `Π : (A : `Set) (B : ⟦ A ⟧ → `Set) → `Set
    `Id : (A : `Set) (x y : ⟦ A ⟧) → `Set
    `μ : (D : `Desc) → `Set 

  ⟦_⟧ : `Set → Set
  ⟦ `⊥ ⟧ = ⊥
  ⟦ `⊤ ⟧ = ⊤
  ⟦ `Bool ⟧ = Bool
  ⟦ `Σ A B ⟧ = Σ ⟦ A ⟧ (λ a → ⟦ B a ⟧)
  ⟦ `Π A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
  ⟦ `Id A x y ⟧ = Id ⟦ A ⟧ x y
  ⟦ `μ D ⟧ = μ ⟪ D ⟫

  data `Desc : Set where
    `ι : `Desc
    `σ : (A : `Set) (D : ⟦ A ⟧ → `Desc) → `Desc
    `δ : (D : `Desc) → `Desc

  ⟪_⟫ : `Desc → Desc
  ⟪ `ι ⟫ = ι
  ⟪ `σ A D ⟫ = σ ⟦ A ⟧ (λ a → ⟪ D a ⟫)
  ⟪ `δ D ⟫ = δ ⟪ D ⟫
