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
-- open Count.Count
\end{code}}

\section{Fully Generic AST}\label{sec:gast}

\begin{code}
module AST where
 open import Data.Nat
 open import Data.List
 open import Data.Fin renaming ( zero to here ; suc to there ) hiding ( _+_ )

 data Rose (A : Set) : Set where
  tree : A → List (Rose A) → Rose A

 data Node : Set where
   lam : Node
   ind : Bool → Node
   non str : String → Node

 mutual
  astInd : {O : `Set} (D : `Desc O) → μ₁ ⟦ O ⟧ ⟪ D ⟫ → Bool → Rose Node
  astInd D (init xs) b = tree (ind b) (asts D D xs)

  ast : (A : `Set) (a : ⟦ A ⟧) → Rose Node
  ast (`Σ A B) (a , b) = tree (non "_,_") (ast A a ∷ ast (B a) b ∷ [])
  ast (`μ₁ A D) x = astInd D x true
  ast (`Π A B) f = tree lam []
  ast `⊥ ()
  ast `⊤ tt = tree (non "tt") []
  ast `Bool true = tree (non "true") []
  ast `Bool false = tree (non "false") []
  ast `String x = tree (str x) []
  ast (`Id A x y) refl = tree (non "refl") []

  asts : {O : `Set} (D R : `Desc O) → ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫ → List (Rose Node)
  asts (`ι o) R tt = tree (non "tt") [] ∷ []
  asts (`σ A D) R (a , xs) = ast A a ∷ asts (D a) R xs
  asts (`δ `⊤ D) R (f , xs) =
    astInd R (f tt) false ∷ asts (D (μ₂ ⟪ R ⟫ ∘ f)) R xs
  asts (`δ A D) R (f , xs) = tree lam [] ∷ []
\end{code}

