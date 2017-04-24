module Slides.List where
open import Data.Unit
open import Data.Product

data _≅_ : {A : Set₁} → A → A → Set where

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
 open import Data.Sum
 private
  postulate
   _ : (A B C : Set) → (A → B → C) ≅ (A × B → C)

  data List (A : Set) : Set where
    list : ⊤ ⊎ (A × List A × ⊤) → List A

module _ where
 open import Data.Sum
 open import Data.Bool
 private
  postulate
   _ : (A B : Set) → A ⊎ B ≅ Σ Bool (λ b → if b then A else B)

  data List (A : Set) : Set where
    list : (b : Bool) → (if b then ⊤ else A × List A × ⊤) → List A
