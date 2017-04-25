module Slides.GenFun where
open import Data.Bool
open import Data.Product
open import Data.Nat
open import Data.List renaming ( [] to nil ; _∷_ to cons )

module _ where
 private
  id : (A : Set) → A → A
  id A = λ x → x
 
  append : (A : Set) → List A → List A → List A
  append A nil ys = ys
  append A (cons x xs) ys = cons x (append A xs ys)

 postulate
   Code : Set
   Meaning : Code → Set
   ⋯ : Set
   generic : (A : Code) → Meaning A → ⋯

module _ where
 private

  data Size : Set₁ where
    `Bool : Size
    `Pair : (A B : Set) → Size
    `List : (A : Set) → Size

  ⟦_⟧ : Size → Set
  ⟦ `Bool ⟧ = Bool
  ⟦ `Pair A B ⟧ = A × B
  ⟦ `List A ⟧ = List A

  size : (A : Size) → ⟦ A ⟧ → ℕ
  size `Bool b = 1
  size (`Pair A B) (a , b) = 3
  size (`List A) nil = 1
  size (`List A) (cons x xs) = 2 + size (`List A) xs

module _ where
 private

  data Size : Set₁ where
    `Bool : Size
    `Pair : (A B : Set) → Size
    `List : (A : Set) → Size

  ⟦_⟧ : Size → Set
  ⟦ `Bool ⟧ = Bool
  ⟦ `Pair A B ⟧ = A × B
  ⟦ `List A ⟧ = List A

  sizeBool : Bool → ℕ
  sizeBool b = 1

  sizePair : {A B : Set} → A × B → ℕ
  sizePair (a , b) = 3

  sizeList : {A : Set} → List A → ℕ
  sizeList nil = 1
  sizeList (cons x xs) = 2 + sizeList xs

  size : (A : Size) → ⟦ A ⟧ → ℕ
  size `Bool b = sizeBool b
  size (`Pair A B) ab = sizePair ab
  size (`List A) xs = sizeList xs

module _ where
 private

  data Count : Set where
    `Bool : Count
    `Pair : (A B : Count) → Count
    `List : (A : Count) → Count

  ⟦_⟧ : Count → Set
  ⟦ `Bool ⟧ = Bool
  ⟦ `Pair A B ⟧ = ⟦ A ⟧ × ⟦ B ⟧
  ⟦ `List A ⟧ = List ⟦ A ⟧

  count : (A : Count) → ⟦ A ⟧ → ℕ
  count `Bool b = 1
  count (`Pair A B) (a , b) = 1 + count A a + count B b
  count (`List A) nil = 1
  count (`List A) (cons x xs) = 1 + count A x + count (`List A) xs
