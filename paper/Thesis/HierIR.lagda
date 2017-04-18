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
open Alg
\end{code}}

\section{Closed Hierarchy of Inductive-Recursive Types}\label{sec:hierir}

In \refsec{hierw}, we extend the
\textit{Closed Well-Order Types} universe of \refsec{wuni} to
a \textit{Closed Hierarchy of Well-Order Universes}.
In this section, we extend the
\textit{Closed Inductive-Recursive Types} universe
of \refsec{closed} to
a \textit{Closed Hierarchy of Inductive-Recursive Universes}.
We define the Agda model of the hierarchy
(as in \refsec{hierwp}), skipping
the formal model (as in \refsec{hierwi}).

\subsection{Agda Model}\label{sec:hierir}

Now we define an Agda model of a
\textit{Closed Hierarchy of Inductive-Recursive Universes}.
Just like the Agda model of the
\textit{Closed Hierarchy of Well-Order Universes} in
\refsec{hierwp}, we derive closed leveled types and their meaning
from closed \Fun{level} universes, defined in terms of pre-closed
constructions parameterized by \Data{Level}.

Recall (from \refsec{closed}) that the
\textit{Closed Inductive-Recursive Types} universe is mutually
defined by closed types (\Data{`Set})
and closed descriptions (\Data{`Desc}). Similarly,
the \textit{Closed Hierarchy of Inductive-Recursive Universes}
is mutually defined by
pre-closed leveled types (\Data{SetForm})
and pre-closed leveled descriptions (\Data{DescForm}).

\AgdaHide{
\begin{code}
module HierIR where
 open import Data.Nat
 private 
\end{code}}

\paragraph{Abstract Universe Levels}

Once again, we define a dependent record (\Data{Level})
as the abstract notion of the previous universe, to be used
as the parameter of \Data{SetForm} and \Data{DescForm}.

\begin{code}
  record Level : Set₁ where
    field
      SetForm : Set
      ⟦_/_⟧ : (A : SetForm) → Set
\end{code}

As before (in \refsec{hierwp}), the
\Field{SetForm} field represents the closed types of the previous
universe, and the \Field{⟦\_/\_⟧} field is their meaning function.
Now we require 3 additional fields.

\begin{code}
      DescForm : (O : SetForm) → Set
      ⟦_/_⟧₁ : {O : SetForm} (D R : DescForm O) → Set
      μ₁' : (O : SetForm) (D : DescForm O) → Set
\end{code}

The \Field{DescForm} represents the closed descriptions of the
previous universe. The \Field{μ₁'} field represents the
type component of the fixpoint operator of
closed descriptions from the previous universe.
Recall (from \refsec{iralgmod}) that the type component of fixpoints
(\Data{μ₁}) is defined in terms of the type component of the
interpretation function for descriptions (\Fun{⟦\_⟧₁}).
The \Field{⟦\_/\_⟧₁} field represents the type component of
the interpretation function for closed descriptions of the previous
universe.

\AgdaHide{
\begin{code}
  mutual
\end{code}}

\paragraph{Pre-Closed Leveled Types}

Below we give the type former of pre-closed leveled types, this time
parameterized by our \Data{Level} record containing description
components, in addition to type components, from the previous
universe.

\begin{code}
    data SetForm (ℓ : Level) : Set where
\end{code}

\paragraph{Pre-Closed Types}

The pre-closed types are no different from
the well-order hierarchy of \refsec{hierwp}.
The only exception is that we
exchange the well-order constructor (\Con{`W})
for the fixpoint constructor (\Con{`μ₁}).

\begin{code}
      `⊥ `⊤ `Bool : SetForm ℓ
      `Σ `Π : (A : SetForm ℓ) (B : ⟦ ℓ / A ⟧ → SetForm ℓ) → SetForm ℓ
      `Id : (A : SetForm ℓ) (x y : ⟦ ℓ / A  ⟧) → SetForm ℓ
      `μ₁ : (O : SetForm ℓ) (D : DescForm ℓ O) → SetForm ℓ
\end{code}

Notice that the \Var{D} argument of \Con{`μ₁} is a mutually defined
\Data{DescForm}, in the same universe level (\Var{ℓ}) as our current
\Data{SetForm}. This is a natural generalization of \Con{`μ₁} from
the closed universe in \refsec{closed}, which which takes a
\Data{`Desc} and constructs a \Data{`Set}.

\paragraph{Pre-Closed Kinds}

The pre-closed kind of types (\Con{`Set}) and their
meaning function (\Con{`⟦\_⟧}) are no different from
the well-order hierarchy of \refsec{hierwp}.

\begin{code}
      `Set : SetForm ℓ
      `⟦_⟧ : Level.SetForm ℓ → SetForm ℓ
      `Desc : Level.SetForm ℓ → SetForm ℓ
      `⟦_⟧₁ : {O : Level.SetForm ℓ} (D R : Level.DescForm ℓ O) → SetForm ℓ
      `μ₁' : (O : Level.SetForm ℓ) (D : Level.DescForm ℓ O) → SetForm ℓ
\end{code}

We now add the pre-closed kind of descriptions (\Con{`Desc}),
and pre-closed kinds for the
interpretation (\Con{`⟦\_⟧₁})
and fixpoint (\Con{`μ₁'}) of descriptions.
Recall that the pre-closed meaning function of types (\Con{`⟦\_⟧}) can
also be considered a function that \textit{lifts} a \textit{type}
from the previous universe to the current universe. Similarly, the
interpretation (\Con{`⟦\_⟧₁}) and
fixpoint (\Con{`μ₁'})
of descriptions both \textit{lift} a description from the previous
universe to the current universe.

Finally, we highlight the difference between the pre-closed
fixpoint (\Con{`μ₁}),
taking a \Data{DescForm} of the \textit{current} universe,
and the pre-flosed \textit{lifting} fixpoint (\Con{`μ₁'}, notice the
``prime'' suffix),
taking a \Field{DescForm} from the \textit{previous} universe.
The former is used to construct algebraic \textit{types}
(like the natural numbers) in the zeroth universe or higher, while
the latter is used to construct algebraic \textit{kinds}
(like heterogenous lists) in the first universe or higher.

If we use \Con{`Π} to quantify over a \Con{`Set},
then the domain (\Var{A}) of
the depenent argument (\Var{B}) will be the meaning of
\Con{`Set}, which is a \Field{TypeForm} of the previous
universe. Thus, if we want to use \Var{A} in the type of \Var{B}, we
must lift it to the current universe with \Con{`⟦\_⟧}.
Similarly, if we use \Con{`Π} to quantify over \Con{`Desc}, then
we can use the argument \Var{A} in the type of \Var{B} by lifting
\Var{A} (a \Field{DescForm}) from the previous universe to the current
universe via \Con{`⟦\_⟧₁} or \Con{`μ₁'}. Distinctively, we could not
apply \Con{`μ₁} to \Var{A}, because \Con{`μ₁} expects a
\Data{DescForm} from the current universe, not a \Field{DescForm} from
the previous universe.

\paragraph{Meaning of Pre-Closed Leveled Types}

Let's define the meaning function for pre-closed leveled types,
having the signature below.

\begin{code}
    ⟦_/_⟧ : (ℓ : Level) → SetForm ℓ → Set
\end{code}

\paragraph{Meaning of Pre-Closed Types}

The meaning of pre-closed types is no different from
the well-order hierarchy version (\refsec{hierwp}),
except we replace the \Con{`W} case with
the \Con{`μ₁} case.

\begin{code}
    ⟦ ℓ / `⊥ ⟧ = ⊥
    ⟦ ℓ / `⊤ ⟧ = ⊤
    ⟦ ℓ / `Bool ⟧ = Bool
    ⟦ ℓ / `Σ A B ⟧ = Σ ⟦ ℓ / A ⟧ (λ a → ⟦ ℓ / B a ⟧)
    ⟦ ℓ / `Π A B ⟧ = (a : ⟦ ℓ / A ⟧) → ⟦ ℓ / B a ⟧
    ⟦ ℓ / `Id A x y ⟧ = Id ⟦ ℓ / A ⟧ x y
    ⟦ ℓ / `μ₁ O D ⟧ = μ₁ ⟦ ℓ / O ⟧ ⟪ ℓ / D ⟫
\end{code}

In the fixpoint case (\Con{`μ₁}), we compute the meaning of the
description argument (\Var{D}) using the mutually defined
meaning of leveled pre-closed descriptions
(\Fun{⟪\_/\_⟫}).

\paragraph{Meaning of Pre-Closed Kinds}

The meaning of each pre-closed kind code is defined using its
corresponding \Data{Level} field,
using the previous universe level \Var{ℓ}.

\begin{code}
    ⟦ ℓ / `Set ⟧ = Level.SetForm ℓ
    ⟦ ℓ / `⟦ A ⟧ ⟧ = Level.⟦ ℓ / A ⟧
    ⟦ ℓ / `Desc O ⟧ = Level.DescForm ℓ O
    ⟦ ℓ / `⟦ D ⟧₁ R ⟧ = Level.⟦ ℓ / D ⟧₁ R
    ⟦ ℓ / `μ₁' O D ⟧ = Level.μ₁' ℓ O D
\end{code}

Note that the arguments of each pre-closed kind code have exactly the
types expected by the \Data{Level} fields,
so meaning translations
(via \Fun{⟦\_/\_⟧} or \Fun{⟪\_/\_⟫}) are unnecessary.

\paragraph{Pre-Closed Leveled Descriptions}

Let's define the meaning function for pre-closed leveled descriptions,
having the signature below.

\begin{code}
    data DescForm (ℓ : Level) (O : SetForm ℓ) : Set where
\end{code}

Note that pre-closed leveled descriptions are parameterized by
\Var{O}, a pre-closed type (\Data{SetForm}) at the same level (\Var{ℓ}) as the current
pre-closed description (\Data{DescForm}), encoding the codomain of the decoding function
for this inductive-recursive description.

\paragraph{Pre-Closed Descriptions}

The leveled pre-closed description constructors are just like the
closed descriptions of \refsec{closed}. The only difference is that we
replace closed constructions (\Data{`Desc}, \Data{`Set}, and
\Fun{⟦\_⟧}) with their pre-closed leveled
counterparts (\Data{DescForm}, \Data{SetForm}, and
\Fun{⟦\_/\_⟧}), at level \Var{ℓ}.

\begin{code}
      `ι : (o : ⟦ ℓ / O ⟧) → DescForm ℓ O
      `σ : (A : SetForm ℓ) (D : ⟦ ℓ / A ⟧ → DescForm ℓ O) → DescForm ℓ O
      `δ : (A : SetForm ℓ) (D : (o : ⟦ ℓ / A ⟧ → ⟦ ℓ / O ⟧) → DescForm ℓ O)
        → DescForm ℓ O
\end{code}


\paragraph{Meaning of Pre-Closed Leveled Descriptions}

Let's define the meaning function for pre-closed leveled descriptions,
having the signature below.

\begin{code}
    ⟪_/_⟫ : (ℓ : Level) {O : SetForm ℓ} → DescForm ℓ O → Desc ⟦ ℓ / O ⟧
\end{code}

\paragraph{Meaning of Pre-Closed Descriptions}

The meaning of leveled pre-closed descriptions is also just like the
meaning of closed descriptions in \refsec{closed}.
This time we replace closed meaning functions
(\Fun{⟦\_⟧} and \Fun{⟪\_⟫}) with their pre-closed leveled
counterparts
(\Fun{⟦\_/\_⟧} and \Fun{⟪\_/\_⟫}), at level \Var{ℓ}.


\begin{code}
    ⟪ ℓ / `ι o ⟫ = ι o
    ⟪ ℓ / `σ A D ⟫ = σ ⟦ ℓ / A ⟧ (λ a → ⟪ ℓ / D a ⟫)
    ⟪ ℓ / `δ A D ⟫ = δ ⟦ ℓ / A ⟧ (λ o → ⟪ ℓ / D o ⟫)
\end{code}

\paragraph{Derived Indexed Hierarchy of Universes}

\begin{code}
  level : (ℓ : ℕ) → Level
\end{code}

\begin{code}
  level zero = record
    { SetForm = ⊥
    ; ⟦_/_⟧ = λ()
    ; DescForm = λ O → ⊥
    ; ⟦_/_⟧₁ = λ ()
    ; μ₁' = λ ()
    }
\end{code}

\begin{code}
  level (suc ℓ) = record
    { SetForm = SetForm (level ℓ)
    ; ⟦_/_⟧ = λ A → ⟦ level ℓ / A ⟧
    ; DescForm = DescForm (level ℓ) 
    ; ⟦_/_⟧₁ = λ D R → ⟦ ⟪ level ℓ / D ⟫ ⟧₁ ⟪ level ℓ / R ⟫
    ; μ₁' = λ O D → μ₁ ⟦ level ℓ / O ⟧ ⟪ level ℓ / D ⟫
    }
\end{code}

\begin{code}
  `Set[_] : ℕ → Set
  `Set[ ℓ ] = SetForm (level ℓ)

  ⟦_∣_⟧ : (ℓ : ℕ) → `Set[ ℓ ] → Set
  ⟦ ℓ ∣ A ⟧ = ⟦ level ℓ / A ⟧

  `Desc[_] : (ℓ : ℕ) → `Set[ ℓ ] → Set
  `Desc[ ℓ ] O = DescForm (level ℓ) O

  ⟪_∣_⟫ : (ℓ : ℕ) {O : `Set[ ℓ ]} → `Desc[ ℓ ] O → Desc ⟦ ℓ ∣ O ⟧
  ⟪ ℓ ∣ D ⟫ = ⟪ level ℓ / D ⟫
\end{code}
