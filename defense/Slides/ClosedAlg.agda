module Slides.ClosedAlg where
open import Function
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Slides.OpenAlg

mutual
  data `Set : Set where
    `⊥ `⊤ : `Set
    _`⊎_ : (A B : `Set) → `Set
    `Σ `Π : (A : `Set) (B : ⟦ A ⟧ → `Set) → `Set
    `Id : (A : `Set) (x y : ⟦ A ⟧) → `Set
    `μ : (D : `Desc) → `Set 

  ⟦_⟧ : `Set → Set
  ⟦ `⊥ ⟧ = ⊥
  ⟦ `⊤ ⟧ = ⊤
  ⟦ A `⊎ B ⟧ = ⟦ A ⟧ ⊎ ⟦ B ⟧
  ⟦ `Σ A B ⟧ = Σ ⟦ A ⟧ (λ a → ⟦ B a ⟧)
  ⟦ `Π A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
  ⟦ `Id A x y ⟧ = Id ⟦ A ⟧ x y
  ⟦ `μ D ⟧ = μ ⟪ D ⟫

  data `Desc : Set where
    _`⊕_ _`⊗_ : (D E : `Desc) → `Desc
    `κ : (A : `Set) → `Desc
    `ι : `Desc

  ⟪_⟫ : `Desc → Desc
  ⟪ D `⊕ E ⟫ = ⟪ D ⟫ ⊕ ⟪ E ⟫
  ⟪ D `⊗ E ⟫ = ⟪ D ⟫ ⊗ ⟪ E ⟫
  ⟪ `κ A ⟫ = κ ⟦ A ⟧
  ⟪ `ι ⟫ = ι

_ : `Desc → Set
_ = μ ∘ ⟪_⟫

module _ where
 private
  `ℕD : `Desc
  `ℕD = `κ `⊤ `⊕ `ι

  `ℕ : `Set
  `ℕ = `μ `ℕD

  zero : ⟦ `ℕ ⟧
  zero = init (inj₁ tt)

  suc : ⟦ `ℕ ⟧ → ⟦ `ℕ ⟧
  suc n = init (inj₂ n)

module _ where
 private
  `ℕD : `Desc
  `ℕD = `κ `⊤ `⊕ `ι

  `ℕ : `Set
  `ℕ = `μ `ℕD

  zero : ⟦ `ℕ ⟧
  zero = init (inj₁ tt)

  suc : ⟦ `Π `ℕ (λ n  → `ℕ) ⟧
  suc n = init (inj₂ n)

module _ where
 private
  `ListD : `Set → `Desc
  `ListD A = `κ `⊤ `⊕ (`κ A `⊗ `ι)

  `List : `Set → `Set
  `List A = `μ (`ListD A)

  nil : {A : `Set} → ⟦ `List A ⟧
  nil = init (inj₁ tt)

  cons : {A : `Set} → ⟦ A ⟧ → ⟦ `List A ⟧ → ⟦ `List A ⟧
  cons x xs = init (inj₂ (x , xs))

  append : {A : `Set} → ⟦ `List A ⟧ → ⟦ `List A ⟧ → ⟦ `List A ⟧
  append (init (inj₁ tt)) ys = ys
  append (init (inj₂ (x , xs))) ys = cons x (append xs ys)
