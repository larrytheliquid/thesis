\AgdaHide{
\begin{code}
module _ where
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Function
open import Appendix
open import Data.Product
open import Data.List
open import Count
open import Lookup
open Prim  hiding ( Σ )
open Alg
open Closed
-- open Count.Count
\end{code}}

\section{Fully Generic AST}\label{sec:gast}

In this section we develop a fully generic function (\Fun{ast})
to \textit{marshal} values to an abstract syntax tree (AST).
Previously (in \refsec{gcount:egs} and \refsec{glookup:egs}),
we visualized generically encoded data in figures
(such as \reffig{vec2}). Those figures were created using fully
generic programming, rather than drawn by hand.
They are the result of applying \Fun{ast} to the value
they visualize, converting the resulting AST to a graph in the
DOT language~\cite{lang:dot},
and rendering the DOT code using
Graphviz~\cite{graphviz}.

The result of \Fun{ast} is a specialized version of a \Data{Rose}
tree. We use the standard \Data{List}-based rose tree, rather than an
infinitary version (\refsec{inft}).

\AgdaHide{
\begin{code}
module Rose where
\end{code}}

\begin{code}
  data Rose (A : Set) : Set where
    tree : A → List (Rose A) → Rose A
\end{code}

Specifically, the result of \Fun{ast} is a \Data{Rose} tree containing
\Data{Node} values.
A \Data{Node} is one of the following constructors.
 
\begin{code}
  data Node : Set where
    non str : String → Node
    ind : Bool → Node
    lam : Node
\end{code}

Each \Data{Node} constructor is translated to a DOT node
differently (for example, the constructor determines the name of
the DOT node, and the color of the name). Below, we describe what each \Data{Node}
constructor represents and how it affects the translation to DOT code:
\begin{itemize}
\item{\Con{non}:} Used for non-inductive constructors, such as
  the pair constructor (\Con{\_,\_} of type \Data{Σ}). The name of the
  node is determined by the \Data{String} argument, and is colored
  \Con{\textit{green}}.
\item{\Con{str}:} Used for string values. The name of the
  node is determined by the \Data{String} argument. The string
  argument is colored \Str{\textit{red}} and is enclosed in quotes.
\item{\Con{non}:} Used for the inductive initial algebra constructor
  (\Con{init} of type \Data{μ₁}).
  The name of the node is ``init'', and is colored
  \Con{\textit{green}}.
  If the \Data{Bool} argument is \Con{true}, then a rectangle is
  drawn around the node.
\item{\Con{lam}:} Used for higher-order values
  (i.e. the function case \Con{`Π} and the infinitary case \Con{`δ}).
  The name of the node is ``$\lambda$'', and is colored \textit{black}.
\end{itemize}

Finally, we abbreviate the result of \Fun{ast} as the type synonym
\Fun{AST}, standing for \Data{Rose} trees specialized to contain
\Data{Node}s.
  
\begin{code}
  AST : Set
  AST = Rose Node
\end{code}

\subsection{Generic Types}

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open import Data.List
 open import Data.Fin renaming ( zero to here ; suc to there ) hiding ( _+_ )
 open Rose
 private
  postulate
\end{code}}

Before implementing the fully generic marshalling functions, we
consider the functions involved and their generic types.
Two functions (\Fun{ast} and \Fun{asts}, below) are unsurprising, but we
define one extra generic function (\Fun{astInd}, below).

As expected, we will define (in \refsec{ast}) \Fun{ast} to fully
generically translate any value to an \Data{AST}.

\begin{code}
   ast : (A : `Set) (a : ⟦ A ⟧) → AST
\end{code}

Additionally, we will define (in \refsec{asts}) \Fun{asts} to fully
generically translate algebraic arguments (of \Con{init}),
to a \textit{list} of \Fun{AST}s.
Recall that the first argument of the \Con{tree} constructor of
\Fun{AST} (i.e. \Data{Rose} specialized to \Data{Node}) is a
\Data{Node}. The second argument to \Con{tree} is a list of other rose
trees (or \Fun{AST}s). Hence, \Fun{asts} returns a \Data{List} of
\Fun{AST}s, as it will be used
for the second argument of \Con{tree}.

\begin{code}
   asts : {O : `Set} (D R : `Desc O) → ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫ → List AST
\end{code}

Finally, we will define one additional helper function,
\Fun{astInd} (in \refsec{astind}).
The \Fun{astInd} function is defined fully generically over the
fixpoint of any description.

\begin{code}
   astInd : {O : `Set} (D : `Desc O) → μ₁ ⟦ O ⟧ ⟪ D ⟫ → Bool → AST
\end{code}

Normally, we inline the definition of such a function, by pattern
matching on \Con{init} (in the \Con{`μ₁} case of \Fun{ast},
and the \Con{`δ `⊤} case of \Fun{asts}),
and applying \Fun{asts} to the contained
algebraic arguments. However, we prefer to extract the definition
of \Fun{astInd} to define \Fun{ast} and \Fun{asts}.

Notice that \Fun{astInd} has an extra \Data{Bool} argument. We will
supply this argument to the \Con{ind} constructor of \Data{Node},
indicating whether or not to draw a box around the \textit{inductive} node.
Recall from \refsec{gcount:egs} that we draw boxes in figures around
the first occurrence of an inductive value, and suppress drawing boxes
for any contained inductive arguments \textit{of the same type}. However,
inductive values of \textit{different} types should start process
over, beginning by drawing a box around the inductive node.
In \refsec{ast} and \refsec{asts}
(when defining \Fun{ast} and \Fun{asts}),
we will see how passing the
appropriate boolean to \Fun{astInd} implements this box drawing logic.

\subsection{Marshalling Initial Algebras}\label{sec:astind}

\subsection{Marshalling All Values}\label{sec:ast}

\subsection{Marshalling Algebraic Arguments}\label{sec:asts}


\AgdaHide{
\begin{code}
module AST where
 open import Data.Nat
 open import Data.List
 open import Data.Fin renaming ( zero to here ; suc to there ) hiding ( _+_ )
 open Rose
 mutual
\end{code}}

\begin{code}
  astInd : {O : `Set} (D : `Desc O) → μ₁ ⟦ O ⟧ ⟪ D ⟫ → Bool → AST
  astInd D (init xs) b = tree (ind b) (asts D D xs)

  ast : (A : `Set) (a : ⟦ A ⟧) → AST
  ast (`Σ A B) (a , b) = tree (non "_,_") (ast A a ∷ ast (B a) b ∷ [])
  ast (`μ₁ A D) x = astInd D x true
  ast (`Π A B) f = tree lam []
  ast `⊥ ()
  ast `⊤ tt = tree (non "tt") []
  ast `Bool true = tree (non "true") []
  ast `Bool false = tree (non "false") []
  ast (`Id A x y) refl = tree (non "refl") []
  ast `String x = tree (str x) []

  asts : {O : `Set} (D R : `Desc O) → ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫ → List AST
  asts (`ι o) R tt = tree (non "tt") [] ∷ []
  asts (`σ A D) R (a , xs) = ast A a ∷ asts (D a) R xs
  asts (`δ `⊤ D) R (f , xs) =
    astInd R (f tt) false ∷ asts (D (μ₂ ⟪ R ⟫ ∘ f)) R xs
  asts (`δ A D) R (f , xs) = tree lam [] ∷ []
\end{code}

