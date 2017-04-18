\AgdaHide{
\begin{code}
module _ where
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Function hiding ( id )
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
module HierWI where
  open import Data.Nat
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

Let's consider some examples where we internalize the signatures of
functions using codes of our universe hierarchy.

\paragraph{Negation Function}

First, we define the negation function (\Fun{not}),
whose type is defined using a dependent function (→),
external to our
closed hierarchy (i.e. from our Agda metalanguage).

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open HierWI
 private
\end{code}}

\begin{code}
  not : (b : ⟦ 0 ∣ `Bool ⟧) → ⟦ 0 ∣ `Bool ⟧ 
  not true = false
  not false = true
\end{code}

Note that the signature is a \textit{type} because the universe level
(i.e. the first argument to the meaning function)
is 0. Now, we internalize the type signature of negation.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open HierWI
 private
\end{code}}

\begin{code}
  not : ⟦ 0 ∣ `Π `Bool (λ b → `Bool) ⟧
  not true = false
  not false = true
\end{code}

It is good that we can internalize the \textit{type} of negation, but
we could already do that using our universe of closed types
in \refsec{wuni}. Our next example (the identity function) shows how
to internalize a \textit{kind}, which the universe of \refsec{wuni}
cannot do.

\paragraph{Identity Function}

First, we define the identity function (\Fun{id}),
whose type is defined using a dependent function (→) external to our
closed hierarchy.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open HierWI
 private
\end{code}}

\begin{code}
  id : (A : `Set[ 0 ]) (a : ⟦ 0 ∣ A ⟧) → ⟦ 0 ∣ A ⟧ 
  id A a = a
\end{code}

The type of the identity function quantifies over all types in the
zeroth universe. Hence, the universe of closed types
(in \refsec{wuni}) cannot internalize the signature of \Fun{id},
because it is a \textit{kind} signature that requires quanitifying
over all types. The universe of closed types (in \refsec{wuni}) does
not have a code for closed types (\Con{`Set}), making such a 
quantification impossible.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open HierWI
 private
\end{code}}

\begin{code}
  id : ⟦ 1 ∣ `Π `Set (λ A → `Π `⟦ A ⟧ (λ a → `⟦ A ⟧)) ⟧
  id A a = a
\end{code}

Above, we have internalized the \textit{kind} signature of
\Fun{id}. The signature is a kind, because the universe level
(i.e. the first argument to the meaning function) is 1. At
universe level 1, the closed type constructor \Con{`Set} and closed
meaning function constructor (\Con{`⟦\_⟧}) are inhabited, allowing us
to internalize the signature of \Fun{id} as a closed kind.

Note that the argument \Var{A} in the closed kind of \Fun{id} is the
meaning of \Con{`Set}. At \textit{kind} level 1,
the meaning function of \Con{`Set}
returns a closed \textit{type}
(\Data{`Set[ \Num{0} ]}, at level 0). Hence, the second
argument of \Fun{id}, and the codomain of \Fun{id}, must lift
(using \Con{`⟦\_⟧}) the \textit{type} \Var{A}
(at level 0), so that the entire signature
of \Fun{id} can be a \textit{kind} (at level 1).

\subsection{Agda Model}\label{sec:hierwp}

Now we define an Agda model of a
\textit{Closed Hierarchy of Well-Order Universes}.
Previously (in \refsec{hierwi}), we defined a formal model of the
hierarchy as a datatype \textit{indexed} by the natural numbers, which
Agda fails to recognize as a positive definition.

Now, we define the hierarchy in 2 stages, allowing Agda to recognize
the positivity of the definition. In the first stage,
we define an \textit{open} datatype (\Data{SetForm}),
\textit{parameterized} by an abstract notion of the previous universe
level (\Data{Level}).
In the second stage, we define the \textit{closed}
hierarchy (\Fun{`Set[\_]}) of universes, \textit{indexed}
by the natural numbers, but as a
\textit{computational family} (\refsec{compu}).
In other words,
we model the indexed definition (\Fun{`Set[\_]})
by \textit{deriving} it as a
\textit{function} from the natural numbers to types, and this function
is defined in terms of the parameterized definition (\Data{SetForm}).
Correspondingly, we also define a meaning function abstracted over the
previous universe level (\Fun{⟦\_/\_⟧}),
which is used to derive the meaning function
over all levels (\Fun{⟦\_∣\_⟧}).

\AgdaHide{
\begin{code}
module HierWP where
 open import Data.Nat
 private 
\end{code}}

\paragraph{Abstract Universe Levels}

First, we define the abstract notion of the previous universe
(whose level is the predecessor of the current universe),
as the dependent record \Data{Level}. The \Data{Level} record is used
as the parameter of the type defined in the first stage of our
hierarchy construction. 

\begin{code}
  record Level : Set₁ where
    field
      SetForm : Set
      ⟦_/_⟧ : SetForm → Set
\end{code}

The \Field{SetForm} field represents a closed type from the previous
universe, and the \Field{⟦\_/\_⟧} field represents the closed type meaning
function from the previous universe.
Note that \Data{Level} is isomoprhic to the \Data{Univ} record of
\refsec{gkind}, just with different field names.
Additionally, note that \Field{SetForm} is a \Data{Set},
and the codomain of \Field{⟦\_/\_⟧} is \Data{Set}, so
\Data{Level} is an \textit{open} kind.

\AgdaHide{
\begin{code}
  mutual
\end{code}}

\paragraph{Pre-Closed Leveled Types}

Next, we state the type former (\Data{SetForm})
of a type at an arbitrary level,
parameterized by the universe at the previous level.
Technically, \Data{SetForm} is an \textit{open} type, due to its
use of the open \Data{Level} parameter.
However, we plan to fill in the parameter with a closed universe in stage 2 of
the construction. Hence, we refer to \Data{SetForm}, and associated
constructions, as being \textit{pre-closed}.

\begin{code}
    data SetForm (ℓ : Level) : Set where
\end{code}

We name our parameterized pre-closed type ``\Data{SetForm}''.
Whereas \Data{`Set[\_]} is \textit{indexed} by natural numbers,
\Data{SetForm} is \textit{parameterized} by the previous universe
level. We call this type \Data{SetForm}, because we intend to
``fill in'' the abstract universe level
with a concrete universe in
the second stage of the construction (i.e. when deriving
the indexed type \Data{`Set[\_]}),
just like we would ``fill in'' a ``form''.

\paragraph{Pre-Closed Types}

The pre-closed type constructors of our
parameterized type (\Data{SetForm})
are similar to the corresponding constructors of the indexed
formal model (\Data{`Set[\_]}).

\begin{code}
      `⊥ `⊤ `Bool : SetForm ℓ
      `Σ `Π `W : (A : SetForm ℓ) (B : ⟦ ℓ / A ⟧ → SetForm ℓ) → SetForm ℓ
      `Id : (A : SetForm ℓ) (x y : ⟦ ℓ / A  ⟧) → SetForm ℓ
\end{code}

Compared to \Data{`Set[\_]}, the main difference is that the
constructors of \Data{SetForm} do not take the level \Var{ℓ} as a
formal argument. This is because \Var{ℓ} is now a parameter, hence it
is an informal and implicit argument of all constructors.
Importantly,
this allows \Data{SetForm} to be a \textit{type}, even though it is
parameterized by \Data{Level}, which is a \textit{kind}
(as explained in \refsec{kindparam}).

\paragraph{Pre-Closed Kinds}

The main change in the pre-closed kinds appears in the pre-closed meaning
function constructor (\Con{`⟦\_⟧}).

\begin{code}
      `Set : SetForm ℓ
      `⟦_⟧ : Level.SetForm ℓ → SetForm ℓ
\end{code}

The indexed closed meaning function constructor takes
\Data{`Set[ \Var{ℓ} ]} as an argument and returns a
\Data{`Set[ \Con{suc} \Var{ℓ} ]}. In this parameterized version of
the constructor, we \textit{cannot} return a \Data{SetForm \Var{ℓ}}, because
the parameter \Var{ℓ} must remain constant for all constructors.
However, we \textit{can} make the argument to the constructor be
a pre-closed type from the previous universe, by projecting
\Field{SetForm} out of our \Data{Level} record parameter \Var{ℓ}.
Hence, the argument in the indexed and parameterized version
of the meaning function constructor (\Con{`⟦\_⟧}) both
represent a closed type from the previous universe, just in
different ways.

\paragraph{Meaning of Pre-Closed Leveled Types}

Now let's define the meaning function for pre-closed types parameterized
by the previous universe.

\begin{code}
    ⟦_/_⟧ : (ℓ : Level) → SetForm ℓ → Set
\end{code}

The only difference in the syntax of the type signature is that we use
a slash, instead of a pipe, to distinguish the abstract
\Data{Level} version of the meaning function (\Fun{⟦\_/\_⟧})
from the natural number version (\Fun{⟦\_∣\_⟧}).

\paragraph{Meaning of Pre-Closed Types}

The meaning of pre-closed types using abstract levels is syntactically
identical to the natural number version, besides replacing pipes with
slashes.

\begin{code}
    ⟦ ℓ / `⊥ ⟧ = ⊥
    ⟦ ℓ / `⊤ ⟧ = ⊤
    ⟦ ℓ / `Bool ⟧ = Bool
    ⟦ ℓ / `Σ A B ⟧ = Σ ⟦ ℓ / A ⟧ (λ a → ⟦ ℓ / B a ⟧)
    ⟦ ℓ / `Π A B ⟧ = (a : ⟦ ℓ / A ⟧) → ⟦ ℓ / B a ⟧
    ⟦ ℓ / `W A B ⟧ = W ⟦ ℓ / A ⟧ (λ a → ⟦ ℓ / B a ⟧)
    ⟦ ℓ / `Id A x y ⟧ = Id ⟦ ℓ / A ⟧ x y
\end{code}

\paragraph{Meaning of Pre-Closed Kinds}

The meaning of pre-closed kinds is interpreted by projecting the field in
the \Data{Level} record \Var{ℓ} associated with the pre-closed kind being
interpreted.

\begin{code}
    ⟦ ℓ / `Set ⟧ = Level.SetForm ℓ
    ⟦ ℓ / `⟦ A ⟧ ⟧ = Level.⟦ ℓ / A ⟧
\end{code}

The meaning of a pre-closed type (\Con{`Set}) is a
pre-closed type (\Field{SetForm}) from the
previous universe (\Var{ℓ}).
The meaning of the pre-closed meaning
function is the meaning function (\Fun{⟦\_/\_⟧})
from the previous universe (\Var{ℓ}).

\paragraph{Passing Positivity Check}

It the definition of \Data{SetForm}, the codomain of the \Var{B}
argument of the \Con{`Σ}, \Con{`Π}, and \Con{`W} constructors is still
an application of the meaning function (\Fun{⟦\_/\_⟧}).
However, now the meaning of \Con{`Set} of is an abstract
\Data{Set} from the \Data{Level} record parameter \Var{ℓ}, whose field
we happend to call \Field{SetForm}. This name simply documents that
we plan to instantiate the field with a \Data{SetForm} of the
previous universe, in the second stage of our indexed universe
hierarchy construction. From the point of view of the definition of
\Data{SetForm}, \Field{SetForm} contains an arbitrary \Data{Set}, so
posivitiy is not violated when checking the infinitary \Var{B}
argument.

\paragraph{Derived Indexed Hierarchy of Universes}

Now we derive closed leveled types
(\Fun{`Set[\_]}),
indexed by the natural numbers,
from pre-closed leveled types (\Data{SetForm}),
parameterized by levels (\Data{Level}).

For each natural number, we need to apply
\Data{SetForm} to a closed \Data{Level}
encoding the previous universe in the hierarchy that the natural
numbers represent. To do so, we define the \Fun{level} function that
maps each natural number,
representing the \textit{current} universe,
to a \Data{Level}, encoding the \textit{previous} universe.

\begin{code}
  level : (ℓ : ℕ) → Level
\end{code}

If the universe level is 0, then there is no previous universe. Hence,
we define the previous closed types (\Field{SetForm})
to be uninhabited (i.e. the bottom type \Data{⊥}). The meaning function
\Field{⟦\_/\_⟧} for these previous closed types is also uninhabited, as
indicated by a $\lambda$ term matching against its empty argument
(empty parentheses, in an argument position,
is Agda syntax for matching against a value
of an uninhabited type).

\begin{code}
  level zero = record
    { SetForm = ⊥
    ; ⟦_/_⟧ = λ()
    }
\end{code}

If the universe level is the successor of some natural number, then
the previous closed types (\Field{SetForm})
are the pre-closed types (\Data{SetForm}), whose parameter is
instantiated with \Fun{level} applied to the predecessor of the input
natural number. The previous closed meaning function
(\Field{⟦\_/\_⟧}) is defined by the previous pre-closed meaning
function (\Fun{⟦\_/\_⟧}) in the same fashion.

\begin{code}
  level (suc ℓ) = record
    { SetForm = SetForm (level ℓ)
    ; ⟦_/_⟧ = ⟦_/_⟧ (level ℓ)
    }
\end{code}

Thus, we inductively define closed universe \Data{Level}s, for any
natural number, by applying pre-closed constructions to previous
closed levels, and defining the zeroth level to be uninhabited.

Finally, we derive (indexed) closed leveled types (and their
meaning functions) by composing pre-closed types (and their meaning
functions) with \Fun{level}.

\begin{code}
  `Set[_] : ℕ → Set
  `Set[ ℓ ] = SetForm (level ℓ)

  ⟦_∣_⟧ : (ℓ : ℕ) → `Set[ ℓ ] → Set
  ⟦ ℓ ∣ A ⟧ = ⟦ level ℓ / A ⟧
\end{code}

The \textit{indexed} leveled types are derived from the
\textit{parameterized} pre-closed types, because the pre-closed types
are used to define \Fun{level}.

