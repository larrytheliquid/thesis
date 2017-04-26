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
  ListD A = σ Bool
    (λ b → if b then ι else σ A (λ a → δ ι))

  module _ where
    ListF : Set → Set → Set
    ListF A X = ⟬ ListD A ⟭ X

    _ : (A : Set) → ListF A ≡ ⟬ ListD A ⟭
    _ = λ A → refl

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
