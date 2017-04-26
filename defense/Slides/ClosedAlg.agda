module Slides.ClosedAlg where
open import Function
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

_ : `Desc → Set
_ = μ ∘ ⟪_⟫

module _ where
 private
  `ℕD : `Desc
  `ℕD = `σ `Bool
    (λ b → if b then `ι else `δ `ι)

  `ℕ : `Set
  `ℕ = `μ `ℕD

  zero : ⟦ `ℕ ⟧
  zero = init (true , tt)

  suc : ⟦ `ℕ ⟧ → ⟦ `ℕ ⟧
  suc n = init (false , n , tt)

module _ where
 private
  `ℕD : `Desc
  `ℕD = `σ `Bool
    (λ b → if b then `ι else `δ `ι)

  `ℕ : `Set
  `ℕ = `μ `ℕD

  zero : ⟦ `ℕ ⟧
  zero = init (true , tt)

  suc : ⟦ `Π `ℕ (λ n  → `ℕ) ⟧
  suc n = init (false , n , tt)

module _ where
 private
  `ListD : `Set → `Desc
  `ListD A = `σ `Bool
    (λ b → if b then `ι else `σ A (λ a → `δ `ι))

  `List : `Set → `Set
  `List A = `μ (`ListD A)

  nil : {A : `Set} → ⟦ `List A ⟧
  nil = init (true , tt)

  cons : {A : `Set} → ⟦ A ⟧ → ⟦ `List A ⟧ → ⟦ `List A ⟧
  cons x xs = init (false , x , xs , tt)

  append : {A : `Set} → ⟦ `List A ⟧ → ⟦ `List A ⟧ → ⟦ `List A ⟧
  append (init (true , tt)) ys = ys
  append (init (false , x , xs , tt)) ys = cons x (append xs ys)
