\AgdaHide{
\begin{code}
module _ where
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Function
open import Appendix
open import Data.Product
open import Data.Nat
open Prim  hiding ( Σ )
open Alg
open ClosedHier
\end{code}}

\section{Fully Generic Domain}\label{sec:gdom}

\begin{code}
module Dom where
 open import Data.Nat
 open import Data.List
 open import Data.Fin renaming ( zero to here ; suc to there ) hiding ( _+_ )

 postulate
   `List : {ℓ : Level} → SetForm ℓ → SetForm ℓ
   `Map : (ℓ : ℕ) → ⟦ suc ℓ ∣ `Π `Set (λ A → (`⟦ A ⟧ `→ `Set) `→ (`⟦ `List A ⟧ `→ `Set)) ⟧

   `List2 : (ℓ : ℕ) → ⟦ suc ℓ ∣ `Set `→ `Set ⟧
   `Map2 : (ℓ : ℕ) → ⟦ suc ℓ ∣ `Π `Set (λ A → (`⟦ A ⟧ `→ `Set) `→ (`⟦ `List2 ℓ A ⟧ `→ `Set)) ⟧

 mutual
   Arg : (ℓ : ℕ) → ⟦ suc ℓ ∣ `Π `Set (λ A → `⟦ A ⟧ `→ `Set) ⟧
   Arg ℓ (`Σ A B) (a , b) = Arg ℓ A a `× Arg ℓ (B a) b
   Arg ℓ (`Π A B) f = `Σ (`List A) (λ xs → `Map ℓ A (λ a → Arg ℓ (B a) (f a)) xs)
   Arg ℓ (`μ₁ O D) (init xs) = Args ℓ O D D xs
   Arg ℓ A a = `⊤

   Args : (ℓ : ℕ) → ⟦ suc ℓ ∣ `Π `Set (λ O → `Π (`Desc O) (λ D → `Π (`Desc O) (λ R →
     `⟦ D ⟧₁ R `→ `Set))) ⟧
   Args ℓ O (`σ A D) R (a , xs) = Arg ℓ A a `× Args ℓ O (D a) R xs
   Args ℓ O (`δ A D) R (f , xs) = `Σ (`List A) (`Map ℓ A (λ a → Arg ℓ (`μ₁ O R) (f a)))
     `× Args ℓ O (D (μ₂ ⟪ level ℓ / R ⟫ ∘ f)) R xs
   Args ℓ O (`ι o) R xs = `⊤
\end{code}

