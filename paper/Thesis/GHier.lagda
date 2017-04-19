\AgdaHide{
\begin{code}
module _ where
open import Function
open import Appendix
open import Data.Nat hiding ( zero ; suc ; _+_ )
open Prim
open Alg
open ClosedHier
open import HierIR
open Nat
\end{code}}

\section{Leveled Fully Generic Functions}\label{sec:gdom}


\AgdaHide{
\begin{code}
module Count where
  one : ⟦ 0 ∣ `ℕ ⟧
  one = suc zero
  two : ⟦ 0 ∣ `ℕ ⟧
  two = suc one
  infixl 6 _+_
  _+_ : ⟦ 0 ∣ `ℕ `→ `ℕ `→ `ℕ ⟧
  init (true , tt) + m = m
  init (false , n , tt) + m = n tt + m
      -- counts₀ O (D (μ₂ ⟪ 0 ∣ R ⟫ ∘ f)) R xs
      -- counts₁ O (D (μ₂ ⟪ 1 ∣ R ⟫ ∘ f)) R xs
\end{code}}

\begin{code}
  mutual
    count₀ : ⟦ 1 ∣ `Π `Set (λ A → `⟦ A ⟧ `→ `⟦ `ℕ ⟧) ⟧
    count₀ (`Σ A B) (a , b) = one + count₀ A a + count₀ (B a) b
    count₀ (`μ₁ O D) (init xs) = one + counts₀ O D D xs
    count₀ `Set ()
    count₀ (`Desc ()) ()
    count₀ (`⟦ () ⟧) a
    count₀ (`⟦ () ⟧₁ ()) xs
    count₀ (`μ₁' () ()) x
    count₀ A a = one
    
    counts₀ : ⟦ 1 ∣ `Π `Set (λ O → `Π (`Desc O) (λ D → `Π (`Desc O) (λ R →
      `⟦ D ⟧₁ R `→ `⟦ `ℕ ⟧))) ⟧
    counts₀ O (`σ A D) R (a , xs) = count₀ A a + counts₀ O (D a) R xs
    counts₀ O (`δ `⊤ D) R (f , xs) = count₀ (`μ₁ O R) (f tt) +
      counts₀ O (D (`μ₂ R ∘ f)) R xs
    counts₀ O (`δ A D) R (f , xs) = one + counts₀ O (D (`μ₂ R ∘ f)) R xs
    counts₀ O (`ι o) R tt = one
\end{code}

\begin{code}
  mutual
    count₁ : ⟦ 2 ∣ `Π `Set (λ A → `⟦ A ⟧ `→ `⟦ `⟦ `ℕ ⟧ ⟧) ⟧
    count₁ (`Σ A B) (a , b) = one + count₁ A a + count₁ (B a) b
    count₁ (`μ₁ O D) (init xs) = one + counts₁ O D D xs
    count₁ `Set A = countSet₁ A
    count₁ (`Desc O) D = countDesc₁ O D
    count₁ (`⟦ A ⟧) a = count₀ A a
    count₁ (`⟦ D ⟧₁ R) xs = counts₀ _ D R xs
    count₁ (`μ₁' O D) (init xs) = one + counts₀ O D D xs
    count₁ A a = one

    counts₁ : ⟦ 2 ∣ `Π `Set (λ O → `Π (`Desc O) (λ D → `Π (`Desc O) (λ R →
      `⟦ D ⟧₁ R `→ `⟦ `⟦ `ℕ ⟧ ⟧))) ⟧
    counts₁ O (`σ A D) R (a , xs) = count₁ A a + counts₁ O (D a) R xs
    counts₁ O (`δ `⊤ D) R (f , xs) = count₁ (`μ₁ O R) (f tt) +
      counts₁ O (D (`μ₂ R ∘ f)) R xs
    counts₁ O (`δ A D) R (f , xs) = one + counts₁ O (D (`μ₂ R ∘ f)) R xs
    counts₁ O (`ι o) R tt = one

    countSet₁ : ⟦ 1 ∣ `Set  `→ `⟦ `ℕ ⟧ ⟧
    countSet₁ (`Σ A B) = two + countSet₁ A
    countSet₁ (`Π A B) = two + countSet₁ A
    countSet₁ (`Id A x y) = one + countSet₁ A + count₀ A x + count₀ A y
    countSet₁ (`μ₁ O D) = one + countSet₁ O + countDesc₁ O D
    countSet₁ (`Desc ())
    countSet₁ (`⟦ () ⟧)
    countSet₁ (`⟦ () ⟧₁ ())
    countSet₁ (`μ₁' () ())
    countSet₁ A = one

    countDesc₁ : ⟦ 1 ∣ `Π `Set (λ O → `Desc O  `→ `⟦ `ℕ ⟧) ⟧
    countDesc₁ O (`ι o) = one + count₀ O o
    countDesc₁ O (`σ A D) = two + countSet₁ A
    countDesc₁ O (`δ A D) = two + countSet₁ A
\end{code}
