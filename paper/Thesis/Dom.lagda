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

\section{Fully Generic Domain}\label{sec:gdom}

\begin{code}
module Dom where
 open import Data.Nat
 open import Data.List
 open import Data.Fin renaming ( zero to here ; suc to there ) hiding ( _+_ )

 Map : {A : Set} → (A → Set) → List A → Set
 Map F [] = ⊤
 Map F (a ∷ as) = F a × Map F as

 mutual
  Dom : (A : `Set) → ⟦ A ⟧ → Set
  Dom (`Σ A B) (a , b) = Dom A a × Dom (B a) b
  Dom (`Π A B) f = Σ (List ⟦ A ⟧) (Map (λ a → Dom (B a) (f a)))
  Dom (`μ₁ O D) (init xs) = Doms D D xs
  Dom A a = ⊤

  Doms :  {O : `Set} (D R : `Desc O) → ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫ → Set
  Doms (`σ A D) R (a , xs) = Dom A a × Doms (D a) R xs
  Doms (`δ A D) R (f , xs) = Σ (List ⟦ A ⟧) (Map (λ a → Dom (`μ₁ _ R) (f a)))
    × Doms (D (μ₂ ⟪ R ⟫ ∘ f)) R xs
  Doms (`ι o) R xs = ⊤

 data Rose (A : Set) : Set where
  tree : A → List (Rose A) → Rose A

 data Node : Set where
   lam : Node
   ind : Bool → Node
   non str : String → Node

 -- mutual
 --  ast : (A : `Set) (a : ⟦ A ⟧) → Dom A a → Rose Node

 --  ast (`Σ A B) (a , b) (as , bs) = tree (non "_,_") (ast A a as ∷ ast (B a) b bs ∷ [])
 --  ast (`μ₁ A D) (init xs) xss = {!!} -- tree (ind true) (asts D D xs)
 --  ast (`Π `⊤ B) f ((tt ∷ []) , (bs , tt)) = ast (B tt) (f tt) bs 
 --  ast (`Π A B) f (as , bs) = tree lam (ext as bs)
 --    where
 --    ext : (as : List ⟦ A ⟧) → Map (λ a → Dom (B a) (f a)) as → List (Rose Node)
 --    ext [] tt = []
 --    ext (a ∷ as) (b , bs) = ast (B a) (f a) b ∷ ext as bs

 --  ast `⊥ () tt
 --  ast `⊤ tt tt = tree (non "tt") []
 --  ast `Bool true tt = tree (non "true") []
 --  ast `Bool false tt = tree (non "false") []
 --  ast `String x tt = tree (str x) []
 --  ast (`Id A x y) refl tt = tree (non "refl") []

 --  asts : {O : `Set} (D R : `Desc O) (xs : ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫) → Doms D R xs → List (Rose Node)
 --  asts (`ι o) R tt tt = tree (non "tt") [] ∷ []
 --  asts (`σ A D) R (a , xs) (as , xss) = ast A a as ∷ asts (D a) R xs xss
 --  asts (`δ `⊤ D) R (f , xs) ((tt ∷ [] , bs , tt) , xss) = tree (ind false) {!asts R R ? bs!} ∷ {!!}
 --  asts (`δ A D) R (f , xs) ((as , bs) , xss) = tree lam (ext as  bs)
 --    ∷ asts (D (μ₂ ⟪ R ⟫ ∘ f)) R xs xss
 --    where
 --    ext : (as : List ⟦ A ⟧) → Map (Dom (`μ₁ _ R) ∘ f) as → List (Rose Node)
 --    ext [] tt = []
 --    ext (a ∷ as) (b , bs) with f a
 --    ... | init ys = tree (ind false) {!!} ∷ {!!}
\end{code}

