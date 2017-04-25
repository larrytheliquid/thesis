module Slides.Prolif where
open import Data.Nat

postulate
  List : Set → Set
  Tree : Set → Set
  Rose : Set
  Fin : ℕ → Set
  SortedList : (A : Set) → List A → Set
  UniqueList : (A : Set) → List A → Set
  
  count : Set
  lookup : Set
  update : Set
  marshal : Set
  append : Set
