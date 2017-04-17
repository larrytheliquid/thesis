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
data W (A : Set) (B : A → Set) : Set where
  sup : (a : A) (f : B a → W A B) → W A B
\end{code}}

\chapter{Closed Hierarchy of Universes}\label{ch:hier}

\refchap{closed} demonstrates closing a universe of
algebraic (inductive-recursive) \textit{types}, and
\refchap{fullyg} demonstrates fully generic programming over that
universe. In this chapter, we expand the closed universe of
\refsec{closed} to also include \textit{kinds},
\textit{superkinds}, and an infinite hierarchy of such
classifications. Types (\Data{Set}) are classified by
kinds (\Data{Set₁}).
$$
\Data{Set} : \Data{Set₁}
$$

Going one level up, kinds (\Data{Set₁}) are classified
by superkinds (\Data{Set₂}).
$$
\Data{Set₁} : \Data{Set₂}
$$

This pattern repeats itself indefinitely. We refer to any such
construction (e.g. a type, or a kind, or a superkind, etc.) as a
\textit{universe}. In \refsec{closed}, we only considered the first
(or zeroth, because we count universe levels by starting with 0)
closed universe (i.e. the universe of types, classified by kinds). Now, we expand this
notion to a closed infinite hierarchy of universes, where each universe in
the hierarchy is classified by another universe, one level above.
$$
\Data{Set}_{\Var{n}} : \Data{Set}_{\Con{suc}~\Var{n}}
$$

There are 3 primary things we achieve by creating a closed hierarchy
of universes:
\begin{enumerate}
\item We can encode formers and constructors of kinds (as well as
  superkinds, etc.) in the closed hierarchy. This includes the two
  primitive kinds, closed types (\Con{`Set}) and
  closed descriptions (\Con{`Desc}). It also includes closed algebraic
  user-declared kinds, such as heterogenous lists (\Fun{`HList}).
\item We can write \textit{leveled} fully generic functions.
  By this we mean universe polymorphic fully generic functions,
  which can be applied to members of any universe in the hierarchy.
  Hence, we can extend fully generic functions
  (like \Fun{count}, \Fun{lookup}, \Fun{ast}, etc.)
  from working over all types and their values,
  to working over all kinds and their types
  (and all superkinds and their kinds, etc.).
\item We can \textit{internalize} the kind (and superkind, etc.)
  signatures of formers, constructors, and functions, by writing them
  as the meaning of a closed code in our universe.
\end{enumerate}

Let's clarify what we mean by the third point, above.
Throughout this disseration we have written the signatures of
closed formers, constructors, and functions using our Agda metatheory,
which is \textit{external} to our closed universe. For example,
consider the \textit{type} signature of the \Fun{suc}cessor of closed
natural numbers, below.

\AgdaHide{
\begin{code}
module _ where
 open Closed
 private 
  postulate
   `ℕ : `Set
\end{code}}

\begin{code}
   suc : (n : ⟦ `ℕ ⟧) → ⟦ `ℕ ⟧
\end{code}

The type signature of \Fun{suc} uses Agda's \textit{open} dependent
function type (→). Instead, we may \textit{internalize} the type
signature of \Fun{suc} as the meaning (\Fun{⟦\_⟧})
of a \textit{closed} dependent
function (\Con{`Π}).

\AgdaHide{
\begin{code}
module _ where
 open Closed
 private 
  postulate
   `ℕ : `Set
\end{code}}

\begin{code}
   suc : ⟦ `Π `ℕ (λ n → `ℕ) ⟧
\end{code}

Another way to look at it, is that we can fit the entire type
signature of \Fun{suc} into the meaning brackets (\Fun{⟦\_⟧}),
as a single closed type (\Data{`Set}).
In contrast, let's consider the \textit{kind} signature of the
\Fun{cons} constructor of closed parameterized lists.

\AgdaHide{
\begin{code}
module _ where
 open Closed
 private 
  postulate
   `List : `Set → `Set
\end{code}}

\begin{code}
   cons : (A : `Set) (a : ⟦ A ⟧) (xs : ⟦ `List A ⟧) → ⟦ `List A ⟧
\end{code}

We cannot internalize the \textit{kind} signature of the \Fun{cons}
function. Even though \Fun{cons} returns a list value, its signature
is kinded because the \Var{A} argument is a kind (\Data{`Set}).
We would like to internalize the kind of \Fun{cons} as
3 nested uses of \Con{`Π}
(for arguments \Var{A}, \Var{a}, and \Var{xs}).
However, the domain of the first \Con{`Π}
would need to be a constructor of closed kinds (\Con{`Set}),
which does not exist in the universe of closed types
(\refapen{closed}).

Similarly, we cannot internalize the kind signature of fully generic
functions (like \Fun{count}),
or even parametrically polymorphic functions
(like the \Fun{id}entity function),
because they need to equantify over all
closed types. By defining a closed hierarchy of universes
in \refsec{hierir}, we \textit{can} internalize
kind (and superkind, etc.) signatures,
thereby fitting them within meaning brackets.

\section{Closed Hierarchy of Well-Order Types}\label{sec:hierw}

In this section we extend the
\textit{Closed Well-Order Types} universe of \refsec{wuni} to a closed
hierarchy of universes. At first, we present a
formal model (in \refsec{hierwi}) of the hierarchy.
Agda (the implementation of type theory we use
in this dissertation) does not recognize our definition of the
universe hierarchy type to be positive. However, we explain why the
formal model presented in this section is consistent, and use it as
motivation to define a model (in \refsec{hierwp}) that Agda
recognizes as positive.

By extending the \textit{Closed Well-Order Types} universe to a
hierarchy, we can explain how a hierarchy is formalized in a simpler
setting where \Data{Set} is the only kind being closed over. With this
background material under our belt, we move on to extending
the \textit{Closed Inductive-Recursive Types} universe
in \refsec{hierir}. There, we must close over a hierarchy
involving two kinds,
\Data{Set} and \Data{Desc}.

\subsection{Formal Model}\label{sec:hierwi}

Now we define a formal model of a
\textit{Closed Hierarchy of Well-Order Universes}.
We do this by mutually defining a type of
universe codes (\Data{`Set[\_]}), \textit{indexed}
by the natural numbers, and a
meaning function (\Fun{⟦\_∣\_⟧})
mapping a universe in the hierarchy to an
Agda type (i.e. a type of our metalanguage).
Henceforth, we refer to \Data{`Set[\_]} as
the \textit{leveled types} and
\Fun{⟦\_∣\_⟧} as the
\textit{leveled type meaning function}.

The natural number index represents the universe level,
in a hierarchy of universes. For example,
\Data{`Set[ \Num{0} ]} models closed types
(whose open equivalent is \Data{Set}),
\Data{`Set[ \Num{1} ]} models closed kinds
(whose open equivalent is \Data{Set₁}),
\Data{`Set[ \Num{2} ]} models closed superkinds
(whose open equivalent is \Data{Set₂}),
and so on.


\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 private 
  {-# NO_POSITIVITY_CHECK #-}
  mutual
\end{code}}

\paragraph{Closed Leveled Types}

First, we state the type former
of the closed leveled types.

\begin{code}
    data `Set[_] : ℕ → Set where
\end{code}

The name of the indexed type (\Data{`Set[\_]}) is Agda syntax for
defining an infix operator, such that the natural number index
appear where the underscore is located.

\paragraph{Closed Types}

Now let's define the closed types. The closed types inhabit
\Data{`Set[ \Num{0} ]}, where the natural number index is 0, encoding
the zeroth universe of types.
However, we want a version of all closed types
(especially closed type formers like \Con{`Π}) to appear at higher
universes as well.

\begin{code}
      `⊥ `⊤ `Bool : ∀{ℓ} → `Set[ ℓ ]
      `Σ `Π `W : ∀{ℓ} (A : `Set[ ℓ ]) (B : ⟦ ℓ ∣ A ⟧ → `Set[ ℓ ]) → `Set[ ℓ ]
      `Id : ∀{ℓ} (A : `Set[ ℓ ]) (x y : ⟦ ℓ ∣ A  ⟧) → `Set[ ℓ ]
\end{code}

Above, the index in the codomain of all constructors is \Var{ℓ}. Thus,
we have defined closed types as the special case where \Var{ℓ} is \Num{0},
and a copy of the closed types at all higher levels.
The constructors of these types are similar to
the constructors of \Data{`Set} in \refsec{wuni}, but with an extra
polymorphic level (\Var{ℓ}) threaded throughout.

\paragraph{Closed Kinds}

Now let's define the closed kinds.
The closed types inhabit
\Data{`Set[ \Num{1} ]}, where the natural number index is 1, encoding
the first universe of kinds.
We also want a version of all closed kinds
to appear at higher universes.

\begin{code}
      `Set : ∀{ℓ} → `Set[ suc ℓ ]
      `⟦_⟧ : ∀{ℓ} → `Set[ ℓ ] → `Set[ suc ℓ ]
\end{code}

Above, the index in the codomain of all constructors is
\Con{suc} \Var{ℓ}. Thus,
we have defined closed kinds as the special case where \Var{ℓ} is \Num{0},
and a copy of the closed kinds at all higher levels.

At universe level 1,
\Con{`Set} is the closed kind of types
(\Con{`Set} : \Data{`Set[ \Num{1} ]}). At universe level 0,
the \Con{`Set} constructor is uninhabited because its index specifies
that it should be greater than or equal to 1.

We have also added a closed meaning function constructor
(\Con{`⟦\_⟧}), allowing us to \textit{lift} a \textit{type} from the previous
universe to be a \textit{kind} in the current universe.
The closed meaning function (\Con{`⟦\_⟧}), or type lifting operator,
ensures that our universes form a \textit{hierarchy}.
This is because we can apply the type lifting operator \Con{`⟦\_⟧}
to any universe \Data{`Set[ \Var{ℓ} ]}, making it a member
of the subsequent universe \Data{`Set[ \Con{suc}~\Var{ℓ} ]}. 

\paragraph{Meaning of Closed Leveled Types}

Second, we state the signature of the meaning function of closed leveled
types. 

\begin{code}
    ⟦_∣_⟧ : (ℓ : ℕ) → `Set[ ℓ ] → Set
\end{code}

The name of the meaning function (\Fun{⟦\_∣\_⟧}) is Agda syntax for
defining a mixfix operator. The natural number argument (\Var{ℓ})
appears in the location of the first underscore, and the
closed leveled type (\Data{`Set[\_]}) argument appears in the location
of the second underscore.

\paragraph{Meaning of Closed Types}

The meaning of closed types (or their copies at higher levels)
is straightforward.

\begin{code}
    ⟦ ℓ ∣ `⊥ ⟧ = ⊥
    ⟦ ℓ ∣ `⊤ ⟧ = ⊤
    ⟦ ℓ ∣ `Bool ⟧ = Bool
    ⟦ ℓ ∣ `Σ A B ⟧ = Σ ⟦ ℓ ∣ A ⟧ (λ a → ⟦ ℓ ∣ B a ⟧)
    ⟦ ℓ ∣ `Π A B ⟧ = (a : ⟦ ℓ ∣ A ⟧) → ⟦ ℓ ∣ B a ⟧
    ⟦ ℓ ∣ `W A B ⟧ = W ⟦ ℓ ∣ A ⟧ (λ a → ⟦ ℓ ∣ B a ⟧)
    ⟦ ℓ ∣ `Id A x y ⟧ = Id ⟦ ℓ ∣ A ⟧ x y
\end{code}

The leveled closed type meaning function
(\Fun{⟦\_∣\_⟧}) is similar to the
unleveled version (\Fun{⟦\_⟧}) in \refsec{wuni}, but with an extra
polymorphic level (\Var{ℓ}) threaded throughout.

\paragraph{Meaning of Closed Kinds}

The meaning of closed kinds interprets the
\textit{code} of types \Con{`Set}
as a leveled type \Data{`Set[\_]},
and the \textit{code} of the closed meaning
function \Con{`⟦\_⟧} as the leveled
meaning function \Fun{⟦\_∣\_⟧}.

\begin{code}
    ⟦ suc ℓ ∣ `Set ⟧ = `Set[ ℓ ]
    ⟦ suc ℓ ∣ `⟦ A ⟧ ⟧ = ⟦ ℓ ∣ A ⟧
\end{code}

Importantly, the level decreases,
from \Con{suc} \Var{ℓ} to \Var{ℓ},
when interpreting closed kinds
(and their copies at higher universe levels).
Hence, we interpret the
code of types in this universe (\Con{`Set}) as the actual
leveled type of the previous universe
(\Data{`Set[ \Var{ℓ} ]}).

Consider the case where
\Con{`Set} : \Data{`Set[ \Num{1} ]}.
This implies that the interpretation
\Fun{⟦} \Num{1} \Fun{∣} \Con{`Set} \Fun{⟧}
is equal to \Data{`Set[ \Num{0} ]}.
In this model,
the level decreasing (from 1 to 0)
captures the high-level notion
that \Data{Set₀} : \Data{Set₁}, preventing
a ``type in type''
(or ``kind in kind'', etc.) paradox
(i.e. \Data{Set₁} : \Data{Set₁}, if the level
did not decrease).

\paragraph{Failing Positivity Check}

The problem with the formal model presented above is that it fails
Agda's positivity checker. The meaning function
(\Fun{⟦\_∣\_⟧}) appears in the domain of the \Var{B} argument of the
\Con{`Σ}, \Con{`Π}, and \Con{`W} constructors of
leveled types (\Data{`Set[\_]}).
If this meaning function is applied to the code of types
(e.g. \Fun{⟦} \Num{1} \Fun{∣} \Con{`Set} \Fun{⟧}), then the result
will be a leveled type (e.g. \Data{`Set[ \Num{0} ]}),
making \Var{B} a \textit{negative} infinitary argument.

By external analysis of the definition of the leveled types indexed by
the natural numbers, we can see that the index decreases (from 1 to 0)
when a negative occurrence manifests.
Furthermore, there are no constructors of
\Data{`Set[\_]} with an argument whose level increases.
Therefore, each leveled type in the hierarchy does not contain types
from levels above it (it only contains types from levels below it).
Hence, argument \Var{B} is not actually a negative occurrence, because
it only contains lower types, which cannot contain any types at the
current level. Currently, Agda's positivity checker cannot perform
such an analysis, so \refsec{hierwp} defines an Agda model that
reifies our positivity argument in its structure.


\subsection{Examples}

\paragraph{Negation Function}

\paragraph{Identity Function}

\subsection{Agda Model}\label{sec:hierwp}

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 private 
\end{code}}

\begin{code}
  record Level : Set₁ where
    field
      `SetForm : Set
      ⟦_/_⟧ : `SetForm → Set
\end{code}

\begin{code}
  mutual
    data `SetForm (ℓ : Level) : Set where
      `⊥ `⊤ `Bool : `SetForm ℓ
      `Σ `Π `W : (A : `SetForm ℓ) (B : ⟦ ℓ / A ⟧ → `SetForm ℓ) → `SetForm ℓ
      `Id : (A : `SetForm ℓ) (x y : ⟦ ℓ / A  ⟧) → `SetForm ℓ
      `Set : `SetForm ℓ
      `⟦_⟧ : Level.`SetForm ℓ → `SetForm ℓ

    ⟦_/_⟧ : (ℓ : Level) → `SetForm ℓ → Set
    ⟦ ℓ / `⊥ ⟧ = ⊥
    ⟦ ℓ / `⊤ ⟧ = ⊤
    ⟦ ℓ / `Bool ⟧ = Bool
    ⟦ ℓ / `Σ A B ⟧ = Σ ⟦ ℓ / A ⟧ (λ a → ⟦ ℓ / B a ⟧)
    ⟦ ℓ / `Π A B ⟧ = (a : ⟦ ℓ / A ⟧) → ⟦ ℓ / B a ⟧
    ⟦ ℓ / `W A B ⟧ = W ⟦ ℓ / A ⟧ (λ a → ⟦ ℓ / B a ⟧)
    ⟦ ℓ / `Id A x y ⟧ = Id ⟦ ℓ / A ⟧ x y
    ⟦ ℓ / `Set ⟧ = Level.`SetForm ℓ
    ⟦ ℓ / `⟦ A ⟧ ⟧ = Level.⟦ ℓ / A ⟧
\end{code}

\begin{code}
  level : (ℓ : ℕ) → Level
  level zero = record
    { `SetForm = ⊥
    ; ⟦_/_⟧ = λ()
    }
  level (suc ℓ) = record
    { `SetForm = `SetForm (level ℓ)
    ; ⟦_/_⟧ = ⟦_/_⟧ (level ℓ)
    }
\end{code}

\begin{code}
  `Set[_] : ℕ → Set
  `Set[ ℓ ] = `SetForm (level ℓ)

  ⟦_∣_⟧ : (ℓ : ℕ) → `Set[ ℓ ] → Set
  ⟦ ℓ ∣ A ⟧ = ⟦ level ℓ / A ⟧
\end{code}


\section{Closed Hierarchy of Inductive-Recursive Types}\label{sec:hierir}
\section{Leveled Fully Generic Functions}\label{sec:gdom}
