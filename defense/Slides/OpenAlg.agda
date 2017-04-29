module Slides.OpenAlg where
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product

data Id (A : Set) (a : A) : A → Set where
  refl : Id A a a

data Desc : Set₁ where
  ι : Desc
  σ : (A : Set) (D : A → Desc) → Desc
  δ : (D : Desc) → Desc

⟬_⟭ : Desc → Set → Set
⟬ ι ⟭ X = ⊤
⟬ σ A D ⟭ X = Σ A (λ a → ⟬ D a ⟭ X)
⟬ δ D ⟭ X = X × ⟬ D ⟭ X

data μ (D : Desc) : Set where
  init : ⟬ D ⟭ (μ D) → μ D

module _ where
 private
  postulate
   Generic : (D : Desc) → μ D → Set
   generic : (D : Desc) (x : μ D) → Generic D x

   Generics : (D : Desc) (X : Set) → ⟬ D ⟭ X → Set
   generics : (D : Desc) (X : Set) (xs : ⟬ D ⟭ X) → Generics D X xs
