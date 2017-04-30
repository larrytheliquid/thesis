module Slides.OpenAlg where
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Sum

data Id (A : Set) (a : A) : A → Set where
  refl : Id A a a

data Desc : Set₁ where
  _⊕_ _⊗_ : (D E : Desc) → Desc
  κ : (A : Set) → Desc
  ι : Desc

⟬_⟭ : Desc → Set → Set
⟬ D ⊕ E ⟭ X = ⟬ D ⟭ X ⊎ ⟬ E ⟭ X
⟬ D ⊗ E ⟭ X = ⟬ D ⟭ X × ⟬ E ⟭ X
⟬ κ A ⟭ X = A
⟬ ι ⟭ X = X

data μ (D : Desc) : Set where
  init : ⟬ D ⟭ (μ D) → μ D

module _ where
 private
  postulate
   Generic : (D : Desc) → μ D → Set
   generic : (D : Desc) (x : μ D) → Generic D x

   Generics : (D : Desc) (X : Set) → ⟬ D ⟭ X → Set
   generics : (D : Desc) (X : Set) (xs : ⟬ D ⟭ X) → Generics D X xs
