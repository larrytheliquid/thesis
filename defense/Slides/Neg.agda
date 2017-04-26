module Slides.Neg where
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Bool
open import Relation.Binary.PropositionalEquality

data Id (A : Set) (a : A) : A → Set where
  refl : Id A a a

{-# NO_POSITIVITY_CHECK #-}
data μ (F : Set → Set) : Set where
  init : F (μ F) → μ F

{-# NO_POSITIVITY_CHECK #-}
data Neg : Set where
  neg : (Neg → Neg) → Neg

bad : Neg → ⊥
bad (neg f) = bad (f (neg f))

worse : ⊥
worse = bad (neg (λ x → x))

