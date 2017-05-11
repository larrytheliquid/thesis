module Slides.Back where
open import Data.Nat

data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A

data Vec (A : Set) : ℕ → Set where
  nil : Vec A zero
  cons : {n : ℕ} → A → Vec A n → Vec A (suc n)

module _ where
 private
  append : (A : Set) → List A → List A → List A
  append A nil ys = ys
  append A (cons x xs) ys = cons x (append A xs ys)


module _ where
 private
  append : {A : Set} {n m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
  append nil ys = ys
  append (cons x xs) ys = cons x (append xs ys)


module _ where
 private
  append : (A : Set) (n m : ℕ) → Vec A n → Vec A m → Vec A (n + m)
  append A zero m nil ys = ys
  append A (suc n) m (cons x xs) ys = cons x (append A n m xs ys)

module _ where
 open import Data.Bool
 open import Data.String
 private
  data 𝒞 : Set where
    `Bool : 𝒞
    `ℕ : 𝒞
    `String : 𝒞

  ⟦_⟧ : 𝒞 → Set
  ⟦ `Bool ⟧ = Bool
  ⟦ `ℕ ⟧ = ℕ
  ⟦ `String ⟧ = String


module _ where
 private
  postulate
   ⋯ : Set
   𝒜 : Set₁
   generic : (A : 𝒜) → 𝒜 → ⋯

module _ where
 private
  postulate
   ⋯ : Set₀
   𝒜 : Set₁
   𝒞 : Set
   ⟦_⟧ : 𝒞 → Set
   generic : (C : 𝒞) → ⟦ C ⟧ → ⋯

module _ where
 private
  postulate
   ⋯ : Set
   𝒜 : Set₁
   ⟦_⟧₁ : 𝒜 → Set
   generic : (A : 𝒜) → ⟦ A ⟧₁ → ⋯

module _ where
 private
  postulate
   ⋯ : Set
   𝒜 : Set₁
   ⟦_⟧₁ : 𝒜 → Set
   𝒞 : Set
   ⟦_⟧₂ : 𝒞 → 𝒜
   generic : (C : 𝒞) → ⟦ ⟦ C ⟧₂ ⟧₁ → ⋯

