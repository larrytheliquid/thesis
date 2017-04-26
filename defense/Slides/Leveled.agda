module Slides.Leveled where
open import Function
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Slides.OpenAlg
open import Slides.ClosedHier

`ℕD : ⟦ 1 ∣ `Desc ⟧
`ℕD = `σ `Bool
  (λ b → if b then `ι else `δ `ι)

`ℕ : ⟦ 1 ∣ `Set ⟧
`ℕ = `μ `ℕD

zero : ⟦ 0 ∣ `ℕ ⟧
zero = init (true , tt)

suc : ⟦ 0 ∣ `Π `ℕ (λ n  → `ℕ) ⟧
suc n = init (false , n , tt)

`ListD : ⟦ 1 ∣ `Set `→ `Desc ⟧
`ListD A = `σ `Bool
  (λ b → if b then `ι else `σ A (λ a → `δ `ι))

`List : ⟦ 1 ∣ `Set `→ `Set ⟧
`List A = `μ (`ListD A)

nil : ⟦ 1 ∣ `Π `Set (λ A → `⟦ `List A ⟧) ⟧
nil A = init (true , tt)

cons : ⟦ 1 ∣ `Π `Set (λ A → `⟦ A ⟧ `→ `⟦ `List A ⟧ `→ `⟦ `List A ⟧) ⟧
cons A x xs = init (false , x , xs , tt)


postulate
  count : ⟦ 1 ∣ `Π `Set (λ A → `⟦ A ⟧ `→ `⟦ `ℕ ⟧) ⟧
  counts : ⟦ 1 ∣ `Π `Desc (λ D → `Π `Set (λ X → `⟬ D ⟭ X `→ `⟦ `ℕ ⟧)) ⟧
  Count : ⟦ 2 ∣ `Π `Set (λ A → `⟦ A ⟧ `→ `⟦ `⟦ `ℕ ⟧ ⟧) ⟧
  Counts : ⟦ 2 ∣ `Π `Desc (λ D → `Π `Set (λ X → `⟬ D ⟭ X `→ `⟦ `⟦ `ℕ ⟧ ⟧)) ⟧

pair' : ⟦ 1 ∣ `Π `Set (λ A → `Π (`⟦ A ⟧ `→ `Set) (λ B → `Π `⟦ A ⟧ (λ a → `⟦ B a ⟧ `→  `Σ `⟦ A ⟧ (λ x → `⟦ B x ⟧)))) ⟧
pair' A B a b = a , b

init' : ⟦ 1 ∣ `Π `Desc (λ D → `⟬ D ⟭ (`μ D) `→ `μ' D) ⟧
init' D xs = init xs
