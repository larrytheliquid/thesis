module Slides.List where
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Bool

data _≅_ : {A : Set₁} → A → A → Set where

module _ (A : Set) where
 private
  postulate
   μ : (Set → Set) → Set

  F : Set → Set
  F X = ⊤ ⊎ A × X

  List = μ F

module _ where
 private
  data List (A : Set) : Set where
    nil : List A
    cons : A → List A → List A

module _ where
 private
  postulate
   _ : (A : Set) → A ≅ A × ⊤

  data List (A : Set) : Set where
    nil : ⊤ → List A
    cons : A → List A → ⊤ → List A

module _ where
 private
  postulate
   _ : (A B C : Set) → (A → B → C) ≅ (A × B → C)

  data List (A : Set) : Set where
    nil : ⊤ → List A
    cons : A × List A × ⊤ → List A

module _ where
 private
  postulate
   _ : (A B C : Set) → (A → B → C) ≅ (A × B → C)

  data List (A : Set) : Set where
    nil : ⊤ → List A
    cons : A × List A × ⊤ → List A

module _ where
 private
  data List (A : Set) : Set where
    list : ⊤ ⊎ (A × List A × ⊤) → List A

module _ where
 private
  postulate
   _ : (A B : Set) → A ⊎ B ≅ Σ Bool (λ b → if b then A else B)

  data List (A : Set) : Set where
    list : Σ Bool
      (λ b → if b then ⊤ else A × List A × ⊤)
      → List A

  nil : {A : Set} → List A
  nil = list (true , tt)

  cons : {A : Set} → A → List A → List A
  cons x xs = list (false , x , xs , tt)

  append : {A : Set} → List A → List A → List A
  append (list (true , tt)) ys = ys
  append (list (false , x , xs , tt)) ys = cons x (append xs ys)

module _ where
 private
  postulate
   _ : (A B : Set) → A ⊎ B ≅ Σ Bool (λ b → if b then A else B)

  data List (A : Set) : Set where
    list : Σ Bool
      (λ b → if b then ⊤ else A × List A × ⊤)
      → List A

  pattern nil = list (true , tt)
  pattern cons x xs = list (false , x , xs , tt)

  append : {A : Set} → List A → List A → List A
  append nil ys = ys
  append (cons x xs) ys = cons x (append xs ys)


