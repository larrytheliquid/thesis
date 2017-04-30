module Slides.AlgList where
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Bool
open import Slides.OpenAlg
open import Relation.Binary.PropositionalEquality

data _≅_ : {A : Set₁} → A → A → Set where

module _ where
 private
  ListD : Set → Desc
  ListD A = κ ⊤ ⊕ (κ A ⊗ ι)

  module _ where
    ListF : Set → Set → Set
    ListF A X = ⟬ ListD A ⟭ X

    _ : (A : Set) → ListF A ≡ ⟬ ListD A ⟭
    _ = λ A → refl

  List : Set → Set
  List A = μ (ListD A)

  nil : {A : Set} → List A
  nil = init (inj₁ tt)

  cons : {A : Set} → A → List A → List A
  cons x xs = init (inj₂ (x , xs))

  append : {A : Set} → List A → List A → List A
  append (init (inj₁ tt)) ys = ys
  append (init (inj₂ (x , xs))) ys = cons x (append xs ys)

