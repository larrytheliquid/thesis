\AgdaHide{
\begin{code}
module _ where
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Function
open import Appendix
open import Data.Product
open import Count
open import Lookup
open Prim  hiding ( Σ )
open Alg
open Closed
open Count.Count
open Count.Split
open Lookup.Lookup

Endo : Set → Set
Endo A = A → A
\end{code}}

\section{Fully Generic Update}\label{sec:gupdate}

\begin{code}
module Update where
 open import Data.Nat
 open import Data.Fin renaming ( zero to here ; suc to there )
 mutual
  update : (A : `Set) (a : ⟦ A ⟧) (i : Fin (count A a))
    → Σ Set (λ Y → Y → ⟦ A ⟧)

  update₁ : (A : `Set) (a : ⟦ A ⟧) (i : Fin (count A a)) → Set
  update₁ A a i = proj₁ (update A a i)

  update₂ : (A : `Set) (a : ⟦ A ⟧) (i : Fin (count A a))
    → update₁ A a i → ⟦ A ⟧
  update₂ A a i a' = proj₂ (update A a i) a'

  update (`μ₁ O D) (init xs) (there i) = updates₁ D D xs i ,
    (λ xs' → init (updates₂ D D xs i xs'))

  update (`Σ A B) (a , b) (there i) with splitΣ A B a b i
  ... | inj₁ j = Σ (update₁ A a j) (λ a' → ⟦ B a ⟧ → ⟦ B (update₂ A a j a') ⟧)
    , λ { (a' , f) → update₂ A a j a' , f b }
  ... | inj₂ j = update₁ (B a) b j
    , (λ b' → a , update₂ (B a) b j b')

  update A@`⊥ a i = Endo ⟦ A ⟧ , (λ f → f a)
  update A@`⊤ a i = Endo ⟦ A ⟧ , (λ f → f a)
  update A@`Bool a i = Endo ⟦ A ⟧ , (λ f → f a)
  update A@`String a i = Endo ⟦ A ⟧ , (λ f → f a)
  update A@(`Σ _ _) a i = Endo ⟦ A ⟧ , (λ f → f a)
  update A@(`Π _ _) a i = Endo ⟦ A ⟧ , (λ f → f a)
  update A@(`Id _ _ _) a i = Endo ⟦ A ⟧ , (λ f → f a)
  update A@(`μ₁ _ _) a i = Endo ⟦ A ⟧ , (λ f → f a)

  updates : {O : `Set} (D R : `Desc O) (xs : ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫)
    (i : Fin (counts D R xs)) → Σ Set (λ Y → Y → ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫)

  updates (`σ A D) R (a , xs) i with splitσ A D R a xs i
  ... | inj₁ j =
    Σ (update₁ A a j)
      (λ a' → ⟦ ⟪ D a ⟫ ⟧₁ ⟪ R ⟫ → ⟦ ⟪ D (update₂ A a j a') ⟫ ⟧₁ ⟪ R ⟫)
    , λ { (a' , f) → update₂ A a j a' , f xs }
  ... | inj₂ j = updates₁ (D a) R xs j
    , (λ xs' → a , updates₂ (D a) R xs j xs')

  updates (`δ `⊤ D) R (f , xs) i with splitδ (D ∘ const) R (f tt) xs i
  ... | inj₁ j =
    Σ (update₁ (`μ₁ _ R) (f tt) j)
      (λ x' → ⟦ ⟪ D (μ₂ ⟪ R ⟫ ∘ f) ⟫ ⟧₁ ⟪ R ⟫ → ⟦ ⟪ D (λ a → μ₂ ⟪ R ⟫ (update₂ (`μ₁ _ R) (f a) j x')) ⟫ ⟧₁ ⟪ R ⟫)
    , (λ { (x' , g) → (λ u → update₂ (`μ₁ _ R) (f u) j x') , g xs })
  ... | inj₂ j = updates₁ (D (μ₂ ⟪ R ⟫ ∘ f)) R xs j
    , (λ xs' → f , updates₂ (D (μ₂ ⟪ R ⟫ ∘ f)) R xs j xs')

  updates (`δ A@`⊥ D) R (f , xs) (there i) = updates₁ (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i
    , (λ xs' → f , updates₂ (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i xs')
  updates (`δ A@`Bool D) R (f , xs) (there i) = updates₁ (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i
    , (λ xs' → f , updates₂ (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i xs')
  updates (`δ A@`String D) R (f , xs) (there i) = updates₁ (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i
    , (λ xs' → f , updates₂ (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i xs')
  updates (`δ A@(`Σ _ _) D) R (f , xs) (there i) = updates₁ (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i
    , (λ xs' → f , updates₂ (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i xs')
  updates (`δ A@(`Π _ _) D) R (f , xs) (there i) = updates₁ (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i
    , (λ xs' → f , updates₂ (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i xs')
  updates (`δ A@(`Id _ _ _) D) R (f , xs) (there i) = updates₁ (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i
    , (λ xs' → f , updates₂ (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i xs')
  updates (`δ A@(`μ₁ _ _) D) R (f , xs) (there i) = updates₁ (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i
    , (λ xs' → f , updates₂ (D (μ₂ ⟪ R ⟫ ∘ f)) R xs i xs')

  updates (`δ A@`⊥ D) R (f , xs) here =
    Σ (Endo (⟦ A ⟧ → μ₁ _ ⟪ R ⟫))
      (λ g → ⟦ ⟪ D (μ₂ ⟪ R ⟫ ∘ f) ⟫ ⟧₁ ⟪ R ⟫ → ⟦ ⟪ D (λ a → μ₂ ⟪ R ⟫ (g f a)) ⟫ ⟧₁ ⟪ R ⟫)
    , λ { (g , h) → g f , h xs }
  updates (`δ A@`Bool D) R (f , xs) here =
    Σ (Endo (⟦ A ⟧ → μ₁ _ ⟪ R ⟫))
      (λ g → ⟦ ⟪ D (μ₂ ⟪ R ⟫ ∘ f) ⟫ ⟧₁ ⟪ R ⟫ → ⟦ ⟪ D (λ a → μ₂ ⟪ R ⟫ (g f a)) ⟫ ⟧₁ ⟪ R ⟫)
    , λ { (g , h) → g f , h xs }
  updates (`δ A@`String D) R (f , xs) here =
    Σ (Endo (⟦ A ⟧ → μ₁ _ ⟪ R ⟫))
      (λ g → ⟦ ⟪ D (μ₂ ⟪ R ⟫ ∘ f) ⟫ ⟧₁ ⟪ R ⟫ → ⟦ ⟪ D (λ a → μ₂ ⟪ R ⟫ (g f a)) ⟫ ⟧₁ ⟪ R ⟫)
    , λ { (g , h) → g f , h xs }
  updates (`δ A@(`Σ _ _) D) R (f , xs) here =
    Σ (Endo (⟦ A ⟧ → μ₁ _ ⟪ R ⟫))
      (λ g → ⟦ ⟪ D (μ₂ ⟪ R ⟫ ∘ f) ⟫ ⟧₁ ⟪ R ⟫ → ⟦ ⟪ D (λ a → μ₂ ⟪ R ⟫ (g f a)) ⟫ ⟧₁ ⟪ R ⟫)
    , λ { (g , h) → g f , h xs }
  updates (`δ A@(`Π _ _) D) R (f , xs) here =
    Σ (Endo (⟦ A ⟧ → μ₁ _ ⟪ R ⟫))
      (λ g → ⟦ ⟪ D (μ₂ ⟪ R ⟫ ∘ f) ⟫ ⟧₁ ⟪ R ⟫ → ⟦ ⟪ D (λ a → μ₂ ⟪ R ⟫ (g f a)) ⟫ ⟧₁ ⟪ R ⟫)
    , λ { (g , h) → g f , h xs }
  updates (`δ A@(`Id _ _ _) D) R (f , xs) here =
    Σ (Endo (⟦ A ⟧ → μ₁ _ ⟪ R ⟫))
      (λ g → ⟦ ⟪ D (μ₂ ⟪ R ⟫ ∘ f) ⟫ ⟧₁ ⟪ R ⟫ → ⟦ ⟪ D (λ a → μ₂ ⟪ R ⟫ (g f a)) ⟫ ⟧₁ ⟪ R ⟫)
    , λ { (g , h) → g f , h xs }
  updates (`δ A@(`μ₁ _ _) D) R (f , xs) here =
    Σ (Endo (⟦ A ⟧ → μ₁ _ ⟪ R ⟫))
      (λ g → ⟦ ⟪ D (μ₂ ⟪ R ⟫ ∘ f) ⟫ ⟧₁ ⟪ R ⟫ → ⟦ ⟪ D (λ a → μ₂ ⟪ R ⟫ (g f a)) ⟫ ⟧₁ ⟪ R ⟫)
    , λ { (g , h) → g f , h xs }

  updates (`ι o) R u here = (⊤ → ⊤) , (λ f → f u)
  updates (`ι o) R xs (there ())

  updates₁ : {O : `Set} (D R : `Desc O) (xs : ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫)
    (i : Fin (counts D R xs)) → Set
  updates₁ D R xs i = proj₁ (updates D R xs i)

  updates₂ : {O : `Set} (D R : `Desc O) (xs : ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫)
    (i : Fin (counts D R xs)) (a' : updates₁ D R xs i)
    → ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫
  updates₂ D R xs i a' = proj₂ (updates D R xs i) a'

\end{code}
