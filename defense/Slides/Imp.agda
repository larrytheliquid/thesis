{-# OPTIONS --type-in-type #-}
module Slides.Imp where
open import Level
open import Data.Empty

data Imp : Set where
  imp : ((A : Set) → A → A) → Imp

bad : Imp → ⊥
bad (imp f) = bad (f Imp (imp f))

worse : ⊥
worse = bad (imp (λ A x → x))

postulate
  _ : Set₁
  _ : Set₂
  _ : Set₃
  _ : ∀ ℓ → Set ℓ → Set (suc ℓ)
