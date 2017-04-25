module Slides.ClosedW where
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product

data Id (A : Set) (a : A) : A → Set where
  refl : Id A a a

data W (A : Set) (B : A → Set) : Set where
  sup : (a : A) (f : B a → W A B) → W A B

mutual
  data `Set : Set where
    `⊥ `⊤ `Bool : `Set
    `Σ `Π `W : (A : `Set) (B : ⟦ A ⟧ → `Set) → `Set
    `Id : (A : `Set) (x y : ⟦ A ⟧) → `Set
  
  ⟦_⟧ : `Set → Set
  ⟦ `⊥ ⟧ = ⊥
  ⟦ `⊤ ⟧ = ⊤
  ⟦ `Bool ⟧ = Bool
  ⟦ `Σ A B ⟧ = Σ ⟦ A ⟧ (λ a → ⟦ B a ⟧)
  ⟦ `Π A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
  ⟦ `W A B ⟧ = W ⟦ A ⟧ (λ a → ⟦ B a ⟧)
  ⟦ `Id A x y ⟧ = Id ⟦ A ⟧ x y
