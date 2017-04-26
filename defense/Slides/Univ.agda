module Slides.Univ where

module _ where
 private
  record Univ : Set₁ where
    field
      Code : Set
      Meaning : Code → Set

module _ where
 private
  record Univ (K : Set₁) : Set₁ where
    field
      Code : Set
      Meaning : Code → K
