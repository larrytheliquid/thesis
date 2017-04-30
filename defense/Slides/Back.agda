module Slides.Back where
open import Data.Nat
open import Data.List renaming ( [] to nil ; _∷_ to cons )
open import Data.Vec renaming ( [] to nil ; _∷_ to cons )


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
 private
  postulate
   ⋯ : Set
   𝒜 : Set₁
   generic : (A : 𝒜) → 𝒜 → ⋯

module _ where
 private
  postulate
   ⋯ : Set
   𝒜 : Set₁
   𝒞 : Set
   ⟦_⟧ : 𝒞 → Set
   generic : (C : 𝒞) → ⟦ C ⟧ → ⋯

