{-# OPTIONS --type-in-type #-}
module Slides.Imp where
open import Data.Empty

data Imp : Set where
  imp : ((A : Set) → A → A) → Imp

bad : Imp → ⊥
bad (imp f) = bad (f Imp (imp f))

worse : ⊥
worse = bad (imp (λ A x → x))
