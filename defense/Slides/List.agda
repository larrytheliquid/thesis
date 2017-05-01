module Slides.List where
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.Nat

data _≅_ : {A : Set₁} → A → A → Set where

module _ where
 private
  postulate
   μ : (Set → Set) → Set
   sizes : (F : Set → Set) (X : Set) → F X → ℕ
   size : (F : Set → Set) → μ F → ℕ

  ListF : Set → Set → Set
  ListF A X = ⊤ ⊎ A × X

  List : Set → Set
  List A = μ (ListF A)

module _ where
 private
  data List (A : Set) : Set where
    list :  ⊤ ⊎ (A × List A) → List A

  nil : {A : Set} → List A
  nil = list (inj₁ tt)

  cons : {A : Set} → A → List A → List A
  cons x xs = list (inj₂ (x , xs))

  append : {A : Set} → List A → List A → List A
  append (list (inj₁ tt)) ys = ys
  append (list (inj₂ (x , xs))) ys = cons x (append xs ys)

