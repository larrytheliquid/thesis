module Slides.ClosedHier where
open import Function
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Product
open import Slides.OpenAlg

{-# NO_POSITIVITY_CHECK #-}
mutual
  data `Set[_] : ℕ → Set where
    `⊥ `⊤ `Bool : ∀{ℓ} → `Set[ ℓ ]
    `Σ `Π : ∀{ℓ} (A : `Set[ ℓ ]) (B : ⟦ ℓ ∣ A ⟧ → `Set[ ℓ ]) → `Set[ ℓ ]
    `Id : ∀{ℓ} (A : `Set[ ℓ ]) (x y : ⟦ ℓ ∣ A ⟧) → `Set[ ℓ ]
    `μ : ∀{ℓ} (D : `Desc[ ℓ ]) → `Set[ ℓ ]
    `Set `Desc : ∀{ℓ} → `Set[ suc ℓ ]
    `⟦_⟧ : ∀{ℓ} (A : `Set[ ℓ ]) → `Set[ suc ℓ ]
    `⟬_⟭ : ∀{ℓ} (D : `Desc[ ℓ ]) (X : `Set[ ℓ ]) → `Set[ suc ℓ ]
    `μ' : ∀{ℓ} (D : `Desc[ ℓ ]) → `Set[ suc ℓ ]

  ⟦_∣_⟧ : ∀ ℓ → `Set[ ℓ ] → Set
  ⟦ ℓ ∣ `⊥ ⟧ = ⊥
  ⟦ ℓ ∣ `⊤ ⟧ = ⊤
  ⟦ ℓ ∣ `Bool ⟧ = Bool
  ⟦ ℓ ∣ `Σ A B ⟧ = Σ ⟦ ℓ ∣ A ⟧ (λ a → ⟦ ℓ ∣ B a ⟧)
  ⟦ ℓ ∣ `Π A B ⟧ = (a : ⟦ ℓ ∣ A ⟧) → ⟦ ℓ ∣ B a ⟧
  ⟦ ℓ ∣ `Id A x y ⟧ = Id ⟦ ℓ ∣ A ⟧ x y
  ⟦ ℓ ∣ `μ D ⟧ = μ ⟪ ℓ ∣ D ⟫
  ⟦ suc ℓ ∣ `Set ⟧ = `Set[ ℓ ]
  ⟦ suc ℓ ∣ `Desc ⟧ = `Desc[ ℓ ]
  ⟦ suc ℓ ∣ `⟦ A ⟧ ⟧ = ⟦ ℓ ∣ A ⟧
  ⟦ suc ℓ ∣ `⟬ D ⟭ X ⟧ = ⟬ ⟪ ℓ ∣ D ⟫ ⟭ ⟦ ℓ ∣ X ⟧ 
  ⟦ suc ℓ ∣ `μ' D ⟧ = μ ⟪ ℓ ∣ D ⟫

  data `Desc[_] : ℕ → Set where
    `ι : ∀{ℓ} → `Desc[ ℓ ]
    `σ : ∀{ℓ} (A : `Set[ ℓ ]) (D : ⟦ ℓ ∣ A ⟧ → `Desc[ ℓ ]) → `Desc[ ℓ ]
    `δ : ∀{ℓ} (D : `Desc[ ℓ ]) → `Desc[ ℓ ]

  ⟪_∣_⟫ : ∀ ℓ → `Desc[ ℓ ] → Desc
  ⟪ ℓ ∣ `ι ⟫ = ι
  ⟪ ℓ ∣ `σ A D ⟫ = σ ⟦ ℓ ∣ A ⟧ (λ a → ⟪ ℓ ∣ D a ⟫)
  ⟪ ℓ ∣ `δ D ⟫ = δ ⟪ ℓ ∣ D ⟫

_`→_ : ∀{ℓ} (A B : `Set[ ℓ ]) → `Set[ ℓ ]
A `→ B = `Π A (λ a → B)

infixr 2 _`→_ 
