\AgdaHide{
\begin{code}
open import Data.Bool
open import Data.Product hiding ( map )
module _ where
 data List (A : Set) : Set where
   nil : List A
   cons : A → List A → List A
\end{code}}

\section{Classifications of Universes}

A \textit{universe} is a collection of \textit{types}, possibly closed
under certain type formers. Just as we accompanied types with example
functions operating over them in \refsec{types}, we accompany
universes with example \textit{generic functions} in this section. A
\textit{generic function} is any function defined over multiple types.

\subsection{Universe Model}

In a dependently typed language, a universe can be defined as a
type of codes (representing the actual types in the universe), and a
meaning function (mapping each code to its actual type).

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\begin{code}
  data BitsStar : Set where
    `Bool : BitsStar
    `List : BitsStar → BitsStar
  
  ⟦_⟧ : BitsStar → Set
  ⟦ `Bool ⟧ = Bool
  ⟦ `List A ⟧ = List ⟦ A ⟧
\end{code}
