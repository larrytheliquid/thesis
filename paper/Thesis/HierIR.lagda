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
module _ where
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

Now that we've defined pre-closed leveled types and descriptions,
\textit{parameterized} by levels (\Data{Level}), we can \textit{derive} closed
leveled types and descriptions, \textit{indexed} by natural numbers
(as a computational family). First, we define \Fun{level} to map each
natural number to a \Data{Level} representing the \textit{previous}
universe (i.e. a natural number $n$ is mapped to universe $n$-1).

\begin{code}
  level : (ℓ : ℕ) → Level
\end{code}

At level 0, there is no previous universe.
Thus, field \Field{SetForm} is bottom,
field \Field{DescForm} is a constant function returning bottom, and
the meaning functions match against their
uninhabited arguments
(signified in Agda by empty parentheses in the argument position).

\begin{code}
  level zero = record
    { SetForm = ⊥
    ; ⟦_/_⟧ = λ()
    ; DescForm = λ O → ⊥
    ; ⟦_/_⟧₁ = λ ()
    ; μ₁' = λ ()
    }
\end{code}

If the universe level is the successor of some natural number, then
the previous closed
type and description fields (\Field{SetForm} and \Field{DescForm})
are the pre-closed types and descriptions
(\Data{SetForm} and \Data{DataForm}), whose parameters are
instantiated with \Fun{level} applied to the predecessor of the input
natural number. The previous closed meaning function for types field
(\Field{⟦\_/\_⟧}) is defined by the previous pre-closed meaning
function for types (\Fun{⟦\_/\_⟧}) in the same fashion.

\begin{code}
  level (suc ℓ) = record
    { SetForm = SetForm (level ℓ)
    ; ⟦_/_⟧ = ⟦_/_⟧ (level ℓ)
    ; DescForm = DescForm (level ℓ) 
    ; ⟦_/_⟧₁ = λ D R → ⟦ ⟪ level ℓ / D ⟫ ⟧₁ ⟪ level ℓ / R ⟫
    ; μ₁' = λ O D → μ₁ ⟦ level ℓ / O ⟧ ⟪ level ℓ / D ⟫
    }
\end{code}

The closed description interpretation and fixpoint fields
(\Field{⟦\_/\_⟧₁} and \Field{μ₁'}) are defined using the open
description interpretation function and fixpoint
(\Fun{⟦\_⟧₁} and \Data{μ₁}) from \refapen{openalg}.


The open description interpretation function (\Fun{⟦\_⟧₁})
expects open description arguments, but the field
\Field{⟦\_/\_⟧₁} has leveled closed description
arguments (\Var{D} and \Var{R}).
Thus, we translate the leveled closed descriptions
(\Var{D} and \Var{R}) using the
leveled description meaning function
(\Fun{⟪\_/\_⟫}) at the predecessor
\Fun{level} (\Var{ℓ}).

Similarly, the open description fixpoint (\Data{μ₁})
expects an open type and an open description,
but the field
\Field{μ₁'} has a leveled closed type argument
(\Var{O}) and a leveled closed description argument
(\Var{D}). The closed type (\Var{O}) is translated
using the leveled type meaning function
(\Fun{⟦\_/\_⟧}), and the closed description (\Var{D})
is translated using the leveled description meaning function
(\Fun{⟪\_/\_⟫}). Both of the leveled meaning functions are translated
at the predecessor \Fun{level} (\Var{ℓ}).

Finally, we can derive indexed closed leveled types
(\Data{`Set[\_]}) from parameterized pre-closed leveled types
(\Data{SetForm}), by instantiating the parameter with the result of
applying \Fun{level} to the input natural number index,
as in \refsec{hierwp}. The leveled closed
type meaning function (\Fun{⟦\_∣\_⟧}) is also derived
from the pre-closed version (\Fun{⟦\_/\_⟧}),
as in \refsec{hierwp}.

\begin{code}
  `Set[_] : ℕ → Set
  `Set[ ℓ ] = SetForm (level ℓ)

  ⟦_∣_⟧ : (ℓ : ℕ) → `Set[ ℓ ] → Set
  ⟦ ℓ ∣ A ⟧ = ⟦ level ℓ / A ⟧
\end{code}

Now, we additionally derive the indexed closed leveled descriptions
(\Data{`Desc[\_]}) from parameterized pre-closed leveled descriptions
(\Data{DescForm}), also by instantiating the parameter with the
result of applying \Fun{level} to the input index. The leveled
closed description meaning function (\Fun{⟪\_∣\_⟫}) is derived from
the pre-closed version (\Fun{⟪\_/\_⟫}) in the same way.

\begin{code}
  `Desc[_] : (ℓ : ℕ) → `Set[ ℓ ] → Set
  `Desc[ ℓ ] O = DescForm (level ℓ) O

  ⟪_∣_⟫ : (ℓ : ℕ) {O : `Set[ ℓ ]} → `Desc[ ℓ ] O → Desc ⟦ ℓ ∣ O ⟧
  ⟪ ℓ ∣ D ⟫ = ⟪ level ℓ / D ⟫
\end{code}


\subsection{Examples}

\paragraph{Identity Function}

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open ClosedHier
 private
\end{code}}

\begin{code}
  id₀ : ⟦ 1 ∣ `Π `Set (λ A → `Π `⟦ A ⟧ (λ a → `⟦ A ⟧)) ⟧
  id₀ A a = a
\end{code}

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open ClosedHier
 private
\end{code}}

\begin{code}
  id₀ : (A : `Set[ 0 ]) (a : ⟦ 0 ∣ A ⟧) → ⟦ 0 ∣ A ⟧ 
  id₀ A a = a
\end{code}

\begin{code}
  id : {ℓ : ℕ} → ⟦ suc ℓ ∣ `Π `Set (λ A → `Π `⟦ A ⟧ (λ a → `⟦ A ⟧)) ⟧
  id A a = a
\end{code}


\paragraph{Initial Algebra}

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open ClosedHier
 private
\end{code}}

\begin{code}
  init₀ : ⟦ 1 ∣ `Π `Set (λ O → `Π (`Desc O) (λ D → 
    `⟦ D ⟧₁ D `→ `μ₁' O D)) ⟧
  init₀ O D xs = init xs
\end{code}

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open ClosedHier
 private
\end{code}}

\begin{code}
  init₀ : (O : `Set[ 0 ]) (D : `Desc[ 0 ] O)
    → ⟦ ⟪ 0 ∣ D ⟫ ⟧₁ ⟪ 0 ∣ D ⟫ → μ₁ ⟦ 0 ∣ O ⟧ ⟪ 0 ∣ D ⟫    
  init₀ O D xs = init xs
\end{code}

\paragraph{Natural Numbers}

\AgdaHide{
\begin{code}
module Nat where
  open import Data.Nat
  open ClosedHier

\end{code}}

\begin{code}
  NatDs₀ : Bool → `Desc[ 0 ] `⊤
  NatDs₀ true = `ι tt
  NatDs₀ false = `δ `⊤ (λ f → `ι (f tt))

  NatD₀ : `Desc[ 0 ] `⊤
  NatD₀ = `σ `Bool NatDs₀
\end{code}

\begin{code}
  `ℕ₀ : `Set[ 0 ]
  `ℕ₀ = `μ₁ `⊤ NatD₀

  ℕ₀ : Set
  ℕ₀ = ⟦ 0 ∣ `ℕ₀ ⟧
\end{code}

\begin{code}
  zero₀ : ℕ₀
  zero₀ = init (true , tt)

  suc₀ : ℕ₀ → ℕ₀
  suc₀ n = init (false , (λ u → n) , tt)
\end{code}

\paragraph{Vectors}

\AgdaHide{
\begin{code}
module _ where
 open Nat
 open Prim
 open Alg
 open ClosedHier
 private
\end{code}}

\begin{code}
  VecDs : `Set[ 0 ] → Bool → `Desc[ 0 ] `ℕ₀
  VecDs A true = `ι zero₀
  VecDs A false =
    `σ `ℕ₀ λ n →
    `σ A λ a →
    `δ `⊤ λ xs →
    `σ (`Id `ℕ₀ (xs tt) n) λ q →
    `ι (suc₀ n)

  VecD : `Set[ 0 ] → `Desc[ 0 ] `ℕ₀
  VecD A = `σ `Bool (VecDs A)
\end{code}

\begin{code}
  `Vec₁ : `Set[ 0 ] → `Set[ 0 ]
  `Vec₁ A = `μ₁ `ℕ₀ (VecD A)
  
  `Vec₂ : (A : `Set[ 0 ]) → ⟦ 0 ∣ `Vec₁ A ⟧ → ℕ₀
  `Vec₂ A = μ₂ ⟪ 0 ∣ VecD A ⟫
  
  `Vec : `Set[ 0 ] → ℕ₀ → `Set[ 0 ]
  `Vec A n = `Σ (`Vec₁ A) (λ xs → `Id `ℕ₀ (`Vec₂ A xs) n)
\end{code}

\begin{code}
  Vec : `Set[ 0 ] → ℕ₀ → Set
  Vec A n = ⟦ 0 ∣ `Vec A n ⟧

  nil : {A : `Set[ 0 ]} → Vec A zero₀
  nil = init (true , tt) , refl
  
  cons : {A : `Set[ 0 ]} {n : ℕ₀} (a : ⟦ 0 ∣ A ⟧) (xs : Vec A n) → Vec A (suc₀ n)
  cons {n = n} a (xs , refl) = init (false , n , a , (λ u → xs) , refl , tt) , refl
\end{code}


\paragraph{Heterogenous Lists}
