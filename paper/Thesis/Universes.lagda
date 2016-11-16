\AgdaHide{
\begin{code}
open import Data.Bool
open import Data.Product hiding ( map )
module _ where
 data List (A : Set) : Set where
   nil : List A
   cons : A → List A → List A
\end{code}}

%% TODO ListStar (A : Set) : Set ~> Set
%% TODO concat ~> flatten

\section{Universes}

Just as a type is a collection of values, a \textit{universe}
is a collection of \textit{types}. 
A primary motivation of universes is allowing functions to only
consider the values of a sensible collection of types. As demonstrated
below, a collection of types can be defined as a type itself, so
universes also fit into our spectrum.

\subsection{Open Universes}

In a dependently typed language, a universe can be defined as a
collection of codes representing the types in the universe, and a
meaning function mapping each code to the actual type in the language.

An \textit{open universe} refers to \AgdaData{Set} either in its
codes or in its meaning function. For example, below is the universe of
some base type closed under list formation.

\AgdaHide{
\begin{code}
module ListStar where
  postulate append : ∀{A} → List A → List A → List A
\end{code}}

\begin{code}
  data ListStar : Set where
    `Base : ListStar
    `List : ListStar → ListStar
  
  ⟦_⟧ : ListStar → Set → Set
  ⟦ `Base ⟧ X = X
  ⟦ `List A ⟧ X = List (⟦ A ⟧ X)
\end{code}

The act of defining a universe also pushes us towards the closed side
of the spectrum, because we can make decisions by pattern matching on
the codes of the universe. For example, consider the \AgdaFun{concat}
function below operating over our universe.

\begin{code}
  concat : ∀{X} (A : ListStar) → ⟦ A ⟧ X → List X
  concat `Base x = cons x nil
  concat (`List A) nil = nil
  concat (`List A) (cons x xs) = append (concat A x) (concat (`List A) xs)
\end{code}

A value of the \AgdaData{ListStar} universe is either a base type, or
some number of nested lists ending in a base type. Thus, we can define
\AgdaFun{concat} for any value of our
universe (a base value is flattened as the singleton list, and a list
is recursively flattened).

%% ``closed under list formation''

We can also define an even more open universe, the universe of
all \textit{all} base types closed under list formation.

\AgdaHide{
\begin{code}
module ListStarH where
  data HList : Set₁ where
    nil : HList
    cons : {A : Set} → A → HList → HList
  postulate append : HList → HList → HList
\end{code}}

\begin{code}
  data ListStarH : Set₁ where
    `Base : Set → ListStarH
    `List : ListStarH → ListStarH
  
  ⟦_⟧ : ListStarH → Set
  ⟦ `Base A ⟧ = A
  ⟦ `List A ⟧ = List ⟦ A ⟧
\end{code}

This universe also allows us to define concat, but our output type
changes from a list of a statically known base type to a
heterogenous list of many possibly different base types.

\begin{code}
  concat : (A : ListStarH) → ⟦ A ⟧ → HList
  concat (`Base A) x = cons x nil
  concat (`List A) nil = nil
  concat (`List A) (cons x xs) = append (concat A x) (concat (`List A) xs)
\end{code}

\subsection{Closed Universes}

A \textit{closed universe} does not refer to \AgdaData{Set} in its
codes, nor in its meaning function. For example, below is the universe of
booleans closed under list formation.

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

Because \AgdaData{BitsStar} is closed (it makes no
references to \AgdaData{Set}), we can write functions over it that make
decisions about any of its values. For example, below is an
\AgdaFun{all} function that returns true only if all boolean
sublists contain \AgdaCon{true} values.

\begin{code}
  all : (A : BitsStar) → ⟦ A ⟧ → Bool
  all `Bool b = b
  all (`List A) nil = true
  all (`List A) (cons x xs) = all A x ∧ all (`List A) xs
\end{code}

\subsection{Fully Closed Universes}\label{sec:treestar}

\AgdaHide{
\begin{code}
open import Data.Nat
data Tree (A B : Set) : Set where
  leaf : Tree A B
  branch₁ : A → Tree A B → Tree A B → Tree A B
  branch₂ : B → Tree A B → Tree A B → Tree A B

module _ where
 private
\end{code}}

Consider the definition of the universe of booleans closed under
binary tree formation, where the type of the right branches of trees
is specialized to contain natural numbers.

\begin{code}
  data TreeStar : Set where
    `Bool : TreeStar
    `Tree : TreeStar → TreeStar
  
  ⟦_⟧ : TreeStar → Set
  ⟦ `Bool ⟧ = Bool
  ⟦ `Tree A ⟧ = Tree ⟦ A ⟧ ℕ
\end{code}

Notice how the code for the tree constructor only takes a single
argument, which is used for the type of left branches of trees in the
meaning function. Although this is a closed universe, it feels a bit
unsettling because it contains trees with natural numbers in their
right branches, but their is no code for natural number types.

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

We call a universe \textit{fully} closed if all of its values
only contain sub-values whose types are also in the universe.
Thus,
the universe above is not fully closed, because the left branches of
Trees contain natural numbers. Below we define a fully closed version
of the universe of booleans and natural numbers closed under binary
tree formation.

\begin{code}
  data TreeStar : Set where
    `Bool `ℕ : TreeStar
    `Tree : TreeStar → TreeStar → TreeStar
  
  ⟦_⟧ : TreeStar → Set
  ⟦ `Bool ⟧ = Bool
  ⟦ `ℕ ⟧ = ℕ
  ⟦ `Tree A B ⟧ = Tree ⟦ A ⟧ ⟦ B ⟧
\end{code}

We fully close the universe by adding a code for natural numbers
(\AgdaCon{`ℕ}). We also changed the binary trees to be additionally
parameterized by the type of their left branches, but the specialized
version also defines a fully closed universe so long as their is a
code for natural numbers.

