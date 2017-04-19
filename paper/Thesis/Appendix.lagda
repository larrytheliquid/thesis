\AgdaHide{
\begin{code}
module _ where
\end{code}}

\chapter{Open Non-Algebraic Types}\label{apen:openprim}

\AgdaHide{
\begin{code}
module Prim where
  open import Agda.Builtin.String public
\end{code}}

\begin{code}
  data ⊥ : Set where
  
  record ⊤ : Set where
    constructor tt
  
  data Bool : Set where
    true false : Bool
  
  infixr 4 _,_
  record Σ (A : Set) (B : A → Set) : Set where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B proj₁
  
  data Id (A : Set) (x : A) : A → Set where
    refl : Id A x x
\end{code}

\chapter{Open Universe of Algebraic Types}\label{apen:openalg}

\AgdaHide{
\begin{code}
module Alg where
  open Prim
\end{code}}

\begin{code}
  data Desc (O : Set) : Set₁ where
    ι : (o : O) → Desc O
    σ : (A : Set) (D : A → Desc O) → Desc O
    δ : (A : Set) (D : (A → O) → Desc O) → Desc O
 
  mutual
    ⟦_⟧₁ : {O : Set} (D R : Desc O) → Set
    ⟦ ι o ⟧₁ R = ⊤
    ⟦ σ A D ⟧₁ R = Σ A (λ a → ⟦ D a ⟧₁ R)
    ⟦ δ A D ⟧₁ R = Σ (A → μ₁ _ R) λ f → ⟦ D (λ a → μ₂ R (f a)) ⟧₁ R
  
    ⟦_⟧₂ : {O : Set} (D R : Desc O) → ⟦ D ⟧₁ R → O
    ⟦ ι o ⟧₂ R tt = o
    ⟦ σ A D ⟧₂ R (a , xs) = ⟦ D a ⟧₂ R xs
    ⟦ δ A D ⟧₂ R (f , xs) = ⟦ D (λ a → μ₂ R (f a)) ⟧₂ R xs
 
    data μ₁ (O : Set) (D : Desc O) : Set where
      init : ⟦ D ⟧₁ D → μ₁ O D
 
    μ₂ : {O : Set} (D : Desc O) → μ₁ O D → O
    μ₂ D (init xs) = ⟦ D ⟧₂ D xs
\end{code}

\chapter{Closed Universe of Algebraic Types}\label{apen:closed}

\AgdaHide{
\begin{code}
module Closed where
  open Prim
  open Alg
\end{code}}

\begin{code}
  mutual
    data `Set : Set where
      `⊥ `⊤ `Bool `String : `Set
      `Σ `Π : (A : `Set) (B : ⟦ A ⟧ → `Set) → `Set
      `Id : (A : `Set) (x y : ⟦ A ⟧) → `Set
      `μ₁ : (O : `Set) (D : `Desc O) → `Set 

    ⟦_⟧ : `Set → Set
    ⟦ `⊥ ⟧ = ⊥
    ⟦ `⊤ ⟧ = ⊤
    ⟦ `Bool ⟧ = Bool
    ⟦ `String ⟧ = String
    ⟦ `Σ A B ⟧ = Σ ⟦ A ⟧ (λ a → ⟦ B a ⟧)
    ⟦ `Π A B ⟧ = (a : ⟦ A ⟧) → ⟦ B a ⟧
    ⟦ `Id A x y ⟧ = Id ⟦ A ⟧ x y
    ⟦ `μ₁ O D ⟧ = μ₁ ⟦ O ⟧ ⟪ D ⟫

    data `Desc (O : `Set) : Set where
      `ι : (o : ⟦ O ⟧) → `Desc O
      `σ : (A : `Set) (D : ⟦ A ⟧ → `Desc O) → `Desc O
      `δ : (A : `Set) (D : (o : ⟦ A ⟧ → ⟦ O ⟧) → `Desc O)
        → `Desc O
  
    ⟪_⟫ : {O : `Set} → `Desc O → Desc ⟦ O ⟧
    ⟪ `ι o ⟫ = ι o
    ⟪ `σ A D ⟫ = σ ⟦ A ⟧ (λ a → ⟪ D a ⟫)
    ⟪ `δ A D ⟫ = δ ⟦ A ⟧ (λ o → ⟪ D o ⟫)
\end{code}

\AgdaHide{
\begin{code}
  _`×_ : (A B : `Set) → `Set
  A `× B = `Σ A (λ _ → B)
\end{code}}


\chapter{Closed Hierarchy of Universes}\label{apen:hier}

\AgdaHide{
\begin{code}
module ClosedHier where
  open import Data.Nat
  open Prim
  open Alg
\end{code}}

\begin{code}
  record Level : Set₁ where
    field
      SetForm : Set
      ⟦_/_⟧ : (A : SetForm) → Set
      DescForm : (O : SetForm) → Set
      ⟦_/_⟧₁ : {O : SetForm} (D R : DescForm O) → Set
      μ₁' : (O : SetForm) (D : DescForm O) → Set

  mutual
    data SetForm (ℓ : Level) : Set where
      `⊥ `⊤ `Bool `String : SetForm ℓ
      `Σ `Π : (A : SetForm ℓ) (B : ⟦ ℓ / A ⟧ → SetForm ℓ) → SetForm ℓ
      `Id : (A : SetForm ℓ) (x y : ⟦ ℓ / A  ⟧) → SetForm ℓ
      `μ₁ : (O : SetForm ℓ) (D : DescForm ℓ O) → SetForm ℓ
      `Set : SetForm ℓ
      `⟦_⟧ : Level.SetForm ℓ → SetForm ℓ
      `Desc : Level.SetForm ℓ → SetForm ℓ
      `⟦_⟧₁ : {O : Level.SetForm ℓ} (D R : Level.DescForm ℓ O) → SetForm ℓ
      `μ₁' : (O : Level.SetForm ℓ) (D : Level.DescForm ℓ O) → SetForm ℓ

    ⟦_/_⟧ : (ℓ : Level) → SetForm ℓ → Set
    ⟦ ℓ / `⊥ ⟧ = ⊥
    ⟦ ℓ / `⊤ ⟧ = ⊤
    ⟦ ℓ / `Bool ⟧ = Bool
    ⟦ ℓ / `String ⟧ = String
    ⟦ ℓ / `Σ A B ⟧ = Σ ⟦ ℓ / A ⟧ (λ a → ⟦ ℓ / B a ⟧)
    ⟦ ℓ / `Π A B ⟧ = (a : ⟦ ℓ / A ⟧) → ⟦ ℓ / B a ⟧
    ⟦ ℓ / `Id A x y ⟧ = Id ⟦ ℓ / A ⟧ x y
    ⟦ ℓ / `μ₁ O D ⟧ = μ₁ ⟦ ℓ / O ⟧ ⟪ ℓ / D ⟫
    ⟦ ℓ / `Set ⟧ = Level.SetForm ℓ
    ⟦ ℓ / `⟦ A ⟧ ⟧ = Level.⟦ ℓ / A ⟧
    ⟦ ℓ / `Desc O ⟧ = Level.DescForm ℓ O
    ⟦ ℓ / `⟦ D ⟧₁ R ⟧ = Level.⟦ ℓ / D ⟧₁ R
    ⟦ ℓ / `μ₁' O D ⟧ = Level.μ₁' ℓ O D

    data DescForm (ℓ : Level) (O : SetForm ℓ) : Set where
      `ι : (o : ⟦ ℓ / O ⟧) → DescForm ℓ O
      `σ : (A : SetForm ℓ) (D : ⟦ ℓ / A ⟧ → DescForm ℓ O) → DescForm ℓ O
      `δ : (A : SetForm ℓ) (D : (o : ⟦ ℓ / A ⟧ → ⟦ ℓ / O ⟧) → DescForm ℓ O)
        → DescForm ℓ O

    ⟪_/_⟫ : (ℓ : Level) {O : SetForm ℓ} → DescForm ℓ O → Desc ⟦ ℓ / O ⟧
    ⟪ ℓ / `ι o ⟫ = ι o
    ⟪ ℓ / `σ A D ⟫ = σ ⟦ ℓ / A ⟧ (λ a → ⟪ ℓ / D a ⟫)
    ⟪ ℓ / `δ A D ⟫ = δ ⟦ ℓ / A ⟧ (λ o → ⟪ ℓ / D o ⟫)

  level : (ℓ : ℕ) → Level
  level zero = record
    { SetForm = ⊥
    ; ⟦_/_⟧ = λ()
    ; DescForm = λ O → ⊥
    ; ⟦_/_⟧₁ = λ ()
    ; μ₁' = λ ()
    }
  level (suc ℓ) = record
    { SetForm = SetForm (level ℓ)
    ; ⟦_/_⟧ = λ A → ⟦ level ℓ / A ⟧
    ; DescForm = DescForm (level ℓ) 
    ; ⟦_/_⟧₁ = λ D R → ⟦ ⟪ level ℓ / D ⟫ ⟧₁ ⟪ level ℓ / R ⟫
    ; μ₁' = λ O D → μ₁ ⟦ level ℓ / O ⟧ ⟪ level ℓ / D ⟫
    }

  `Set[_] : ℕ → Set
  `Set[ ℓ ] = SetForm (level ℓ)

  ⟦_∣_⟧ : (ℓ : ℕ) → `Set[ ℓ ] → Set
  ⟦ ℓ ∣ A ⟧ = ⟦ level ℓ / A ⟧

  `Desc[_] : (ℓ : ℕ) → `Set[ ℓ ] → Set
  `Desc[ ℓ ] O = DescForm (level ℓ) O

  ⟪_∣_⟫ : (ℓ : ℕ) {O : `Set[ ℓ ]} → `Desc[ ℓ ] O → Desc ⟦ ℓ ∣ O ⟧
  ⟪ ℓ ∣ D ⟫ = ⟪ level ℓ / D ⟫
\end{code}

\AgdaHide{
\begin{code}
  infixr 2 _`×_ 
  infixr 2 _`→_ 

  _`×_ : {ℓ : Level} (A B : SetForm ℓ) → SetForm ℓ
  A `× B = `Σ A (λ _ → B)

  _`→_ : {ℓ : Level} (A B : SetForm ℓ) → SetForm ℓ
  A `→ B = `Π A (λ _ → B)

  `μ₂ : {ℓ : Level} {O : SetForm ℓ} (D : DescForm ℓ O) → μ₁ ⟦ ℓ / O ⟧ ⟪ ℓ / D ⟫ → ⟦ ℓ / O ⟧
  `μ₂ D = μ₂ ⟪ _ / D ⟫
\end{code}}

\chapter{Internalized Signatures of Closed Constructors}\label{apen:intern}

\AgdaHide{
\begin{code}
module Internalization where
  open import Data.Nat
  open Prim
  open Alg
  open ClosedHier
\end{code}}

\begin{code}
  bot' : ⟦ 0 ∣ `⊥ `→ `⊥ ⟧
  bot' p = p

  tt' : ⟦ 0 ∣ `⊤ ⟧
  tt' = tt

  true' : ⟦ 0 ∣ `Bool ⟧
  true' = true

  false' : ⟦ 0 ∣ `Bool ⟧
  false' = false

  pair' : ⟦ 1 ∣ `Π `Set (λ A → `Π (`⟦ A ⟧ `→ `Set) (λ B →
    `Π `⟦ A ⟧ (λ a → `Π `⟦ B a ⟧ (λ b →
    `Σ `⟦ A ⟧ (λ a → `⟦ B a ⟧))))) ⟧
  pair' A B a b = a , b

  lambda' : ⟦ 1 ∣ `Π `Set (λ A → `Π (`⟦ A ⟧ `→ `Set) (λ B →
    `Π (`Π `⟦ A ⟧ (λ a → `⟦ B a ⟧)) (λ f →
    `Π `⟦ A ⟧ (λ a → `⟦ B a ⟧)))) ⟧
  lambda' A B f = λ a → f a

  refl' : ⟦ 1 ∣ `Π `Set (λ A → `Π `⟦ A ⟧ (λ a → `Id `⟦ A ⟧ a a)) ⟧
  refl' A a = refl

  init' : ⟦ 1 ∣ `Π `Set (λ O → `Π (`Desc O) (λ D → 
    `⟦ D ⟧₁ D `→ `μ₁' O D)) ⟧
  init' O D xs = init xs
\end{code}
