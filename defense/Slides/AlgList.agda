module Slides.AlgList where
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Bool

data _≅_ : {A : Set₁} → A → A → Set where

data Desc : Set₁ where
  ι : Desc
  σ : (A : Set) (D : A → Desc) → Desc
  δ : (D : Desc) → Desc

⟬_⟭ : Desc → Set → Set
⟬ ι ⟭ X = ⊤
⟬ σ A D ⟭ X = Σ A (λ a → ⟬ D a ⟭ X)
⟬ δ D ⟭ X = X × ⟬ D ⟭ X

data μ (D : Desc) : Set where
  init : ⟬ D ⟭ (μ D) → μ D

module _ where
 private
  ListD : Set → Desc
  ListD A = σ Bool
    (λ b → if b then ι else σ A (λ a → δ ι))

  List : Set → Set
  List A = μ (ListD A)

  nil : {A : Set} → List A
  nil = init (true , tt)

  cons : {A : Set} → A → List A → List A
  cons x xs = init (false , x , xs , tt)

  append : {A : Set} → List A → List A → List A
  append (init (true , tt)) ys = ys
  append (init (false , x , xs , tt)) ys = cons x (append xs ys)

module _ where
 private
  ListD : Set → Desc
  ListD A = σ Bool
    (λ b → if b then ι else σ A (λ a → δ ι))

  List : Set → Set
  List A = μ (ListD A)

  pattern nil = init (true , tt)
  pattern cons x xs = init (false , x , xs , tt)

  append : {A : Set} → List A → List A → List A
  append nil ys = ys
  append (cons x xs) ys = cons x (append xs ys)
