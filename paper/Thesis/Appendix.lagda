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

%% \chapter{Closed Hierarchy of Universes}\label{apen:hier}

