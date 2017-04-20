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

\section{Leveled Fully Generic Functions}\label{sec:lgcount}

\refchap{fullyg} demonstrates writing fully generic functions
(like \Fun{count}, \Fun{lookup} and \Fun{ast}) over all
\textit{values} of the
\textit{Closed Inductive-Recursive Types}
universe (of \refsec{closed}). In this section, we show how to write
\textit{leveled} fully generic functions, or fully generic functions
at any level of the
\textit{Closed Hierarchy of Inductive-Recursive Universes}
(of \refsec{hierir}).

In \refsec{count0}, we patch fully generic \Fun{count}
(of \refsec{count}), converting it to work in level 0 of our hierarchy,
over all \textit{values} of types.
Subsequently, in \refsec{count1}, we define fully generic \Fun{Count}
in level 1 of our hierarchy,
over all \textit{types} of kinds.
As we shall see, the \Fun{Count} function at level 1 must be defined
in terms of the \Fun{count} function at level 0,
because the values of level 0 are lifted to the type level 1,
which is expected because our universes form a \textit{hierarchy}.

\subsection{Counting Values of Types in Universe Zero}\label{sec:count0}

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
      -- counts O (D (μ₂ ⟪ 0 ∣ R ⟫ ∘ f)) R xs
      -- Counts O (D (μ₂ ⟪ 1 ∣ R ⟫ ∘ f)) R xs
\end{code}}

\begin{code}
  mutual
    count : ⟦ 1 ∣ `Π `Set (λ A → `⟦ A ⟧ `→ `⟦ `ℕ ⟧) ⟧
    count (`Σ A B) (a , b) = one + count A a + count (B a) b
    count (`μ₁ O D) (init xs) = one + counts O D D xs
    count `Set ()
    count (`Desc ()) ()
    count (`⟦ () ⟧) a
    count (`⟦ () ⟧₁ ()) xs
    count (`μ₁' () ()) x
    count A a = one
    
    counts : ⟦ 1 ∣ `Π `Set (λ O → `Π (`Desc O) (λ D → `Π (`Desc O) (λ R →
      `⟦ D ⟧₁ R `→ `⟦ `ℕ ⟧))) ⟧
    counts O (`σ A D) R (a , xs) = count A a + counts O (D a) R xs
    counts O (`δ `⊤ D) R (f , xs) = count (`μ₁ O R) (f tt) +
      counts O (D (`μ₂ R ∘ f)) R xs
    counts O (`δ A D) R (f , xs) = one + counts O (D (`μ₂ R ∘ f)) R xs
    counts O (`ι o) R tt = one
\end{code}

\subsection{Counting Types of Kinds in Universe One}\label{sec:count1}

\begin{code}
  mutual
    Count : ⟦ 2 ∣ `Π `Set (λ A → `⟦ A ⟧ `→ `⟦ `⟦ `ℕ ⟧ ⟧) ⟧
    Count (`Σ A B) (a , b) = one + Count A a + Count (B a) b
    Count (`μ₁ O D) (init xs) = one + Counts O D D xs
    Count `Set A = CountSet A
    Count (`Desc O) D = CountDesc O D
    Count (`⟦ A ⟧) a = count A a
    Count (`⟦ D ⟧₁ R) xs = counts _ D R xs
    Count (`μ₁' O D) (init xs) = one + counts O D D xs
    Count A a = one

    Counts : ⟦ 2 ∣ `Π `Set (λ O → `Π (`Desc O) (λ D → `Π (`Desc O) (λ R →
      `⟦ D ⟧₁ R `→ `⟦ `⟦ `ℕ ⟧ ⟧))) ⟧
    Counts O (`σ A D) R (a , xs) = Count A a + Counts O (D a) R xs
    Counts O (`δ `⊤ D) R (f , xs) = Count (`μ₁ O R) (f tt) +
      Counts O (D (`μ₂ R ∘ f)) R xs
    Counts O (`δ A D) R (f , xs) = one + Counts O (D (`μ₂ R ∘ f)) R xs
    Counts O (`ι o) R tt = one

    CountSet : ⟦ 1 ∣ `Set  `→ `⟦ `ℕ ⟧ ⟧
    CountSet (`Σ A B) = two + CountSet A
    CountSet (`Π A B) = two + CountSet A
    CountSet (`Id A x y) = one + CountSet A + count A x + count A y
    CountSet (`μ₁ O D) = one + CountSet O + CountDesc O D
    CountSet (`Desc ())
    CountSet (`⟦ () ⟧)
    CountSet (`⟦ () ⟧₁ ())
    CountSet (`μ₁' () ())
    CountSet A = one

    CountDesc : ⟦ 1 ∣ `Π `Set (λ O → `Desc O  `→ `⟦ `ℕ ⟧) ⟧
    CountDesc O (`ι o) = one + count O o
    CountDesc O (`σ A D) = two + CountSet A
    CountDesc O (`δ A D) = two + CountSet A
\end{code}
