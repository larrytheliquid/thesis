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
infinitary version (\refsec{inft}). Additionally, throughout this
section the ``cons'' constructor of \Data{List} is denoted by
(\Con{∷}), an infix constructor, and the ``nil'' constructor
of \Data{List}
is denoted by \Con{[]}.

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

\AgdaHide{
\begin{code}
module AST where
 open import Data.Nat
 open import Data.List
 open import Data.Fin renaming ( zero to here ; suc to there ) hiding ( _+_ )
 open Rose
 mutual
\end{code}}

\subsection{Marshalling Initial Algebras}\label{sec:astind}

First, let's define \Fun{astInd} fully generically over all
descriptions and their fixpoints. Below, we restate the type
of \Fun{astInd}, and define the only case to that needs to be
considered, the case for the lone \Con{init}ial algebra
constructor of \Data{μ₁}.

\begin{code}
  astInd : {O : `Set} (D : `Desc O) → μ₁ ⟦ O ⟧ ⟪ D ⟫ → Bool → AST
  astInd D (init xs) b = tree (ind b) (asts D D xs)
\end{code}

The first argument of the rose \Con{tree} constructor has type
\Data{Node}. Since initial algebras encode inductive types, we
use the \Con{ind} node. The boolean \Var{b} argument is also passed
along to the \Con{ind} node.

The second argument of the rose
\Con{tree} constructor is a \Data{List} of rose trees. Hence,
the second argument to \Con{tree} is the result of
recursively applying the mutually defined \Fun{asts} function to the
algebraic arguments (\Var{xs}). Hence, the number of children of the
resulting rose tree is equal to the number of arguments in \Var{xs}.

\subsection{Marshalling All Values}\label{sec:ast}

Second, let's define \Fun{ast} fully generically for all values of all
types. Below, we restate the type of \Fun{ast} before defining it by
its cases.

\begin{code}
  ast : (A : `Set) (a : ⟦ A ⟧) → AST
\end{code}

\paragraph{Algebraic Fixpoint}

To define the fixpoint case, we simply apply the mutually defined
\Fun{astInd} function to the algebraic argument \Var{x}.

\begin{code}
  ast (`μ₁ A D) x = astInd D x true
\end{code}

Importantly, we use \Con{true} for the boolean argument of
\Fun{astInd}. Hence, applying \Fun{ast} to any
algebraic value (having type \Con{`μ₁}) results in drawing a box
around it using the DOT language.

\paragraph{Dependent Pair}

The dependent pair case creates a rose \Con{tree} with two children
(in the second argument to \Con{tree}, below), by
recursively applying \Fun{ast} to each component of the pair
(\Var{a} and \Var{b}).

\begin{code}
  ast (`Σ A B) (a , b) = tree (non "_,_") (ast A a ∷ ast (B a) b ∷ [])
\end{code}

Because dependent pairs are non-inductive types, the first
(\Data{Node}) argument to \Con{tree} is \Con{non}. The argument to \Con{non} is a
string representing the name of the infix
dependent pair constructor (\Con{\_,\_}). 

\paragraph{Dependent Function}

We treat higher-order values, like dependent functions, as black
boxes. Hence, the \Fun{ast} of a function is a childless \Con{tree},
whose \Data{Node} is \Con{lam}.

\begin{code}
  ast (`Π A B) f = tree lam []
\end{code}

\paragraph{String}

Strings are non-inductive values, so we use the \Con{str} constructor
of \Data{Node}. Strings also have no additional arguments, so their
\Fun{AST} tree has no children.

\begin{code}
  ast `String x = tree (str x) []
\end{code}

Note that the string value \Var{x} is supplied as the argument to the
\Con{str} constructor of \Data{Node}, so a quoted version of \Var{x}
can act as the name of the node when interpreted as DOT code.

\paragraph{Remaining Non-Inductive Values}

All remaining non-inductive values use
the \Con{non} constructor of \Data{Node},
and are childless (except for the \Con{`⊥} value, which is
uninhabited). 

\begin{code}
  ast `⊥ ()
  ast `⊤ tt = tree (non "tt") []
  ast `Bool true = tree (non "true") []
  ast `Bool false = tree (non "false") []
  ast (`Id A x y) refl = tree (non "refl") []
\end{code}

Each occurrence of \Con{non} is applied to string name corresponding to
the name of the marshalled constructor.

\subsection{Marshalling Algebraic Arguments}\label{sec:asts}

Third, let's define \Fun{asts} fully generically for all arguments
of the \Con{init}ial algebra.
Below, we restate the type of \Fun{asts} before defining it by
its cases.

\begin{code}
  asts : {O : `Set} (D R : `Desc O) → ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫ → List AST
\end{code}

Recall (from \refsec{counts}) that the arguments of the
\Con{init}ial algebra are treated as one big $n$-tuple,
rather than $n$ nested pairs. This is why each case of
\Fun{asts} returns a \Data{List} of \Fun{AST}s, rather than
\Con{tree} (\Con{non} \Str{"\_,\_"}) applied to such a list.\footnote {
  If each case of \Fun{asts} did return such a
  \Con{tree} (\Con{non} \Str{"\_,\_"}) \Var{xs}, then each
  \Con{init} constructor in figures would have a pair
  (\Con{\_,\_}) as its child node. The first component of the pair
  would be the \Fun{head} of \Var{xs}.
  The second component of the pair
  child node would be a nested sequence of pairs, i.e. the
  nested representation of the \Fun{tail}
  of arguments \Var{xs}.
  }

\paragraph{Non-Inductive Argument}

\begin{code}
  asts (`σ A D) R (a , xs) = ast A a ∷ asts (D a) R xs
\end{code}

\paragraph{Inductive Argument}

\begin{code}
  asts (`δ `⊤ D) R (f , xs) =
    astInd R (f tt) false ∷ asts (D (μ₂ ⟪ R ⟫ ∘ f)) R xs
\end{code}

\paragraph{Infinitary Argument}

\begin{code}
  asts (`δ A D) R (f , xs) = tree lam [] ∷ asts (D (μ₂ ⟪ R ⟫ ∘ f)) R xs
\end{code}

\paragraph{Last Argument}

\begin{code}
  asts (`ι o) R tt = tree (non "tt") [] ∷ []
\end{code}
