\AgdaHide{
\begin{code}
module _ where
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Function hiding ( id )
open import Appendix
open import Data.List
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
 open import Data.Product
 open Prim  hiding ( Σ )
 open Alg
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

The \textit{Closed Inductive-Recursive Types} universe
examples in \refsec{closedeg} correspond to examples that we can
demonstrate in the zeroth universe of our hierarchy.
The \textit{Closed Inductive-Recursive Types} universe does not
include the kinds \Con{`Set} and \Con{`Desc}, hence all of the
signatures (e.g. \Fun{NatDs}, \Fun{`ℕ}, etc.) used to construct the
examples were defined \textit{externally} to the universe
(using types, like function space, of our Agda metalanguage).

We can port all of the examples in \refsec{closedeg} to the zeroth
universe of our hierarchy by patching them using the table below. For
each definition (in its signature and body),
replace occurrences of the left table column
with the right table column.

\begin{center}
 \begin{tabular}{||c | c ||} 
 \hline
 Closed Types Universe &
 Universe 0 in Hierarchy \\ [0.5ex] 
 \hline\hline

 \Data{`Set} &
 \Fun{`Set[ \Num{0} ]} \\ 
 \hline

 \Data{`Desc} &
 \Fun{`Desc[ \Num{0} ]} \\ 
 \hline

 \Fun{⟦ \Var{A} ⟧} &
 \Fun{⟦ \Num{0} ∣ \Var{A} ⟧} \\ 
 \hline

 \Fun{⟪ \Var{D} ⟫} &
 \Fun{⟪ \Num{0} ∣ \Var{D} ⟫} \\ 
 \hline

 \end{tabular}
\end{center}

However, we can also choose to \textit{internalize} the signatures
used in the examples, as we see below. By ``internalize'' we mean that
each signature can be represented as the leveled type meaning
(\Fun{⟦\_∣\_⟧}), of some closed type, at some level in our hierarchy.

\paragraph{Natural Numbers}

\AgdaHide{
\begin{code}
module Nat where
  open import Data.Nat hiding ( zero ; suc ; ℕ )
  open Prim  hiding ( Σ )
  open Alg
  open ClosedHier
\end{code}}


Let's internalize the signatures used in the natural number examples.
The definition bodies remain the same as those in \refsec{closedeg}, so we
only present the signatures below.
First, we internalize the signatures of the closed description and
type \textit{kinds} (i.e. at universe level 1).

\begin{code}
  NatDs : ⟦ 1 ∣ `Bool `→ `Desc `⊤ ⟧
  NatD : ⟦ 1 ∣ `Desc `⊤ ⟧
  `ℕ : ⟦ 1 ∣ `Set ⟧
\end{code}

Crucially, internalizing the kinds above relies on having codes for
closed types (\Con{`Set}) and closed descriptions (\Con{`Desc}).
If an internalized signature needs to refer to a type, it must refer
to the internalized ``backtick'' version of the type.
Because we can internalize \textit{all} signatures, we no longer need
to define non-backtick versions of types (e.g. \Fun{ℕ}). We can always
recover a non-backtick version of a type by applying the meaning
function (\Fun{⟦\_∣\_⟧}) to the backtick version, at the appropriate
level. 

\begin{code}
  zero : ⟦ 0 ∣ `ℕ ⟧
  suc : ⟦ 0 ∣ `ℕ `→ `ℕ ⟧
\end{code}

Above, we internalize the
\textit{value} (i.e. typed at universe level 0)
constructors of the natural numbers. 

\AgdaHide{
\begin{code}
  NatDs true = `ι tt
  NatDs false = `δ `⊤ (λ f → `ι (f tt))
  NatD = `σ `Bool NatDs
  `ℕ = `μ₁ `⊤ NatD
  zero = init (true , tt)
  suc n = init (false , (λ u → n) , tt)
\end{code}}

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

Now, let's internalize the \textit{kinds} used to derive indexed
vectors from inductive-recursive vectors.

\begin{code}
  VecDs : ⟦ 1 ∣ `Set `→ `Bool `→ `Desc `ℕ ⟧
  VecD : ⟦ 1 ∣ `Set `→ `Desc `ℕ ⟧
  `Vec₁ : ⟦ 1 ∣ `Set `→ `Set ⟧
  `Vec₂ : ⟦ 1 ∣ `Π `Set (λ A → `⟦ `Vec₁ A ⟧ `→ `⟦ `ℕ ⟧) ⟧
  `Vec : ⟦ 1 ∣ `Set `→ `⟦ `ℕ ⟧ `→ `Set ⟧
\end{code}

Notice that the decoding function (\Fun{`Vec₂}) quantifies over
the \textit{kind} \Con{`Set}, binding variable \Var{A}. The bound variable
\Var{A} is a \textit{type}, the inhabitant of the \textit{kind}
\Con{`Set}. Hence, in order to ask for argument of
\Fun{`Vec₁} applied to \Var{A}, we must first \textit{lift} this type
to the kind level (using \Con{`⟦\_⟧}). Also recall that \Con{`ℕ} is
defines to be a \textit{type}. Hence, when asking for a
natural number argument, in kind signatures of
\Fun{`Vec₂} and \Fun{`Vec}, we also lift the \Con{`ℕ} type to the kind
level (using \Con{`⟦\_⟧}). 

\begin{code}
  nil : ⟦ 1 ∣ `Π `Set (λ A → `⟦ `Vec A zero ⟧) ⟧
  cons : ⟦ 1 ∣ `Π `Set (λ A → `Π `⟦ `ℕ ⟧ (λ n →
    `⟦ A ⟧ `→ `⟦ `Vec A n ⟧ `→ `⟦ `Vec A (suc n) ⟧)) ⟧
\end{code}

Above, we internalize the
\textit{value}
constructors of the vectors.
Even though the signatures of \Fun{nil} an \Fun{cons} are kinds (at
universe level 1), their codomains return lifted (using \Con{`⟦\_⟧})
vector \textit{types} (at universe level 0).
For similar reasons, the natural number argument of \Fun{cons} is
actually a value of \textit{type} \Con{`ℕ}, which has merely been
lifted to the kind level to fit in the signature of \Con{cons}.

To determine what level an argument or codomain lives at, substract
the number of liftings (i.e. nested occurrences of \Con{`⟦\_⟧}) from
the level of the signature (i.e. the number to the left of the pipe in
the meaning function). For example, the codomain of \Con{nil} is
1 minus 1 lifting, thus \Con{nil} returns a value of \textit{type}
(i.e. universe level 0) \Fun{`Vec}, even though its signature is
kinded (i.e. at universe level 1).

Finally, note that both \Fun{nil} and \Fun{cons} have explicit type
arguments, and \Fun{cons} also has an explicit natural number
argument. To change these to be implicit arguments, we would need to
update our universe to an implicit version of the \Con{`Π} code.

\AgdaHide{
\begin{code}
  VecDs A true = `ι zero
  VecDs A false =
    `σ `ℕ λ n →
    `σ A λ a →
    `δ `⊤ λ xs →
    `σ (`Id `ℕ (xs tt) n) λ q →
    `ι (suc n)
  VecD A = `σ `Bool (VecDs A)
  `Vec₁ A = `μ₁ `ℕ (VecD A)
  `Vec₂ A = μ₂ ⟪ 0 ∣ VecD A ⟫
  `Vec A n = `Σ (`Vec₁ A) (λ xs → `Id `ℕ (`Vec₂ A xs) n)
  nil A = init (true , tt) , refl
  cons A n a (xs , refl) = init (false , n , a , (λ u → xs) , refl , tt) , refl
\end{code}}

\paragraph{Heterogenous Lists}

Previously, we defined types, like the natural numbers, whose
signatures were kinds (at universe level 1). Now, we give an example
of defining a kind, the heterogenous lists, whose
signature is a superkind (at universe level 2).
Defining the \textit{kind} of heterogenous lists is not possible
in the \textit{Closed Inductive-Recursive Types} universe of
\refsec{closed}, which only supports \textit{types}. First, let's
review the kind of heterogenous lists.

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\begin{code}
  data HList : Set₁ where
    nil : HList
    cons : (A : Set) → A → HList → HList
\end{code}

\AgdaHide{
\begin{code}
module _ where
 open Prim  hiding ( Σ )
 open Alg
 open ClosedHier
 private
\end{code}}

The signatures of the closed description and closed type, used to
define heterogenous lists, are superkinded at universe level 2.

\begin{code}
  HListDs : ⟦ 2 ∣ `Bool `→ `Desc `⊤ ⟧
  HListDs true = `ι tt
  HListDs false =
    `σ `Set λ A →
    `σ `⟦ A ⟧ λ a →
    `δ `⊤ λ xs →
    `ι tt

  HListD : ⟦ 2 ∣ `Desc `⊤ ⟧
  HListD = `σ `Bool HListDs

  `HList : ⟦ 2 ∣ `Set ⟧
  `HList = `μ₁ `⊤ HListD
\end{code}

Notice that the descriptin of the first argument of the \Fun{cons}
constructor (the \Con{false} case of \Fun{HListDs}) takes
a type as an argument (\Con{`Set}), and the second argument
takes a value of the lifting of that type.
We can also see that \Fun{`HList} is a closed \textit{kind}, because
it is classified as a \Con{`Set} at universe level 2. The meaning of
\Con{`Set} at universe level 2 is the \Data{SetForm} of the previous
universe level, or \Fun{Set[ \Var{1} ]}. Hence, closed \Fun{`HList} is
classified as a closed kind (\Fun{Set[ \Var{1} ]}), just like
open \Data{HList} is classified as an open kind (\Data{Set₁}).

\begin{code}
  nil : ⟦ 1 ∣ `HList ⟧
  nil = init (true , tt)

  cons : ⟦ 1 ∣ `Π `Set (λ A → `⟦ A ⟧ `→ `HList `→ `HList) ⟧
  cons A a xs = init (false , A , a , (λ u → xs) , tt)
\end{code}

Above, we define the
\textit{kind} (i.e. universe level 1)
constructors of the heterogenous lists. We know that \Fun{nil} and
\Fun{cons} construct kinds, because their codomains do not have any
liftings (i.e. occurrences of \Con{`⟦\_⟧}),
so 1 - 0 leaves the codomains at universe level 1,
the level of kinds.

\paragraph{Identity Function}

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open ClosedHier
 private
\end{code}}

In \refsec{hierweg}, we demonstrate internalizing the
signature of the identify function in level 0 of the
\textit{Closed Hierarchy of Well-Order Universes}.
We can still do this in our
\textit{Closed Hierarchy of Inductive-Recursive Universes},
as the internalized type below demonstrates.

\begin{code}
  id : ⟦ 1 ∣ `Π `Set (λ A → `Π `⟦ A ⟧ (λ a → `⟦ A ⟧)) ⟧
  id A a = a
\end{code}

For reference, we also present the external type signature that the
meaning of our internal type above expands to.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open ClosedHier
 private
\end{code}}

\begin{code}
  id : (A : `Set[ 0 ]) (a : ⟦ 0 ∣ A ⟧) → ⟦ 0 ∣ A ⟧ 
  id A a = a
\end{code}

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open ClosedHier
 private
  id : (ℓ : ℕ) → ⟦ suc ℓ ∣ `Π `Set (λ A → `Π `⟦ A ⟧ (λ a → `⟦ A ⟧)) ⟧
  id ℓ A a = a
\end{code}}

\paragraph{Dependent Pair}

As a sanity check for the construction of our
\textit{Closed Hierarchy of Inductive-Recursive Universes}
(\refsec{hierir}), we should be able to internalize each signature
(whether it be a type or kind) of every constructor of every datatype
in the universe. This sanity check can be found in \refapen{intern}.

As one illustrative example, we show how to internalize the pair
constructor of dependent pairs. In open type theory
(\refapen{openalg}), the pair
constructor has the following type.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open ClosedHier
 private
  data Σ : (A : Set) (B : A → Set) → Set where
\end{code}}

\begin{code}
   _,_ : {A : Set} {B : A → Set} (a : A) → B a → Σ A B
\end{code}

Below, we define \Fun{pair'} to be pair constructor \Con{init},
while internalizing the kind signature of \Con{\_,\_}.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open Prim
 open ClosedHier
 private
\end{code}}

\begin{code}
  pair' : ⟦ 1 ∣ `Π `Set (λ A → `Π (`⟦ A ⟧ `→ `Set) (λ B →
    `Π `⟦ A ⟧ (λ a → `Π `⟦ B a ⟧ (λ b →
    `Σ `⟦ A ⟧ (λ a → `⟦ B a ⟧))))) ⟧
  pair' A B a b = a , b
\end{code}

Internalizing the kind of the pair constructor (\Con{,}) as
\Fun{pair'} takes advantage of being able to quantify over
closed types (\Con{`Set}),
and the closed type meaning function (\Con{`⟦\_⟧}), used to lift types
to the kind level. Really, it is just a slightly more involved
example of internalizing the signature of the identity function
(\Fun{id}).

Note that we must use explicit function arguments for
\Var{A} and \Var{B}, as our universe does not currently support
an implicit version of dependent functions (\Con{`Π}).
For reference, we also present the external type signature that the
meaning of our internal type above expands to.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open Prim
 open ClosedHier
 private
\end{code}}

\begin{code}
  pair' : (A : `Set[ 0 ]) (B : ⟦ 0 ∣ A ⟧ → `Set[ 0 ])
    (a : ⟦ 0 ∣ A ⟧) (b : ⟦ 0 ∣ B a ⟧)
    → Σ ⟦ 0 ∣ A ⟧ (λ a → ⟦ 0 ∣ B a ⟧)
  pair' A B a b = a , b
\end{code}

\paragraph{Initial Algebra}

As our final example, we internalize the signature of the initial
algebra constructor (\Con{init}) of fixpoints. The internalization of
the signature for \Con{init} is unique, as it quantifies over the
closed kind of \textit{descriptions} (\Con{`Desc}), and must be
defined with description-lifting operations. First, review the type of
the \Con{init} constructor in open type theory (\refapen{openalg}).

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open Prim
 open Alg hiding ( μ₁ ; init )
 private
  data μ₁ : (O : Set) (D : Desc O) → Set₁ where
\end{code}}

\begin{code}
   init : {O : Set} {D : Desc O} → ⟦ D ⟧₁ D → μ₁ O D
\end{code}

Below, we define \Fun{init'} to be \Con{init}, while internalizing the
kind signature of \Con{init}.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open Alg
 open ClosedHier
 private
\end{code}}

\begin{code}
  init' : ⟦ 1 ∣ `Π `Set (λ O → `Π (`Desc O) (λ D → 
    `⟦ D ⟧₁ D `→ `μ₁' O D)) ⟧
  init' O D xs = init xs
\end{code}

We internalize the \Var{D} argument by quantifying over a closed
description (\Con{`Desc}). Because \Var{D} is a description from the
previous universe, the subsequent argument uses
the lifting description interpretation function
(\Con{`⟦\_⟧₁}). Similarly, the codomain uses the lifting fixpoint
constructor (\Con{`μ₁'}). Importantly, the codomain of \Con{init} is
internalized with the prime-variant of closed fixpoint constructor
(\Con{`μ₁'}), defined over descriptions of the previous universe, not
the non-prime fixpoint constructor (\Con{`μ₁}), defined over
descriptions of the current universe.

It is not obvious that the definition of our hierarchy needs
fixpoints of descriptions in
the current (\Con{`μ₁}) and previous (\Con{`μ₁'}) universes. It is also
not obvious that the hierarchy needs to internalize the description
intepretation function (\Con{`⟦\_⟧₁}),
for descriptions of the previous universe.
However, our sanity check, in \refapen{intern},
exposes that both \Con{`μ₁'} and \Con{`⟦\_⟧₁} are necessary to
internalize the kind signature of the \Con{init} constructor.
For reference, we also present the external type signature that the
meaning of our internal type above expands to.

\AgdaHide{
\begin{code}
module _ where
 open import Data.Nat
 open Alg
 open ClosedHier
 private
\end{code}}

\begin{code}
  init' : (O : `Set[ 0 ]) (D : `Desc[ 0 ] O)
    → ⟦ ⟪ 0 ∣ D ⟫ ⟧₁ ⟪ 0 ∣ D ⟫ → μ₁ ⟦ 0 ∣ O ⟧ ⟪ 0 ∣ D ⟫    
  init' O D xs = init xs
\end{code}

\paragraph{Lifting Functions}

We conclude this section by reflecting upon the internalization of the
kind signatures for the pair (\Con{\_,\_}) and initial algebra
(\Con{init}) constructors (as \Fun{pair'} and \Fun{init'}), in the
examples above.

The former is evidence that we need to quantify over
the kind of closed types (\Con{`Set}), and then lift the quantifier to
the kind level using the
closed meaning function of types (\Con{`⟦\_⟧}).

The latter is evidence that we need to quantify over
the kind of closed descriptions (\Con{`Desc}),
and then lift the quantifier to
the kind level using the
closed interpretation function (\Con{`⟦\_⟧₁}) of
descriptions, and the (lifting)
closed fixpoint operator (\Con{`μ₁'}) of descriptions.

Hence, our sanity check in \refapen{intern}, that the signature of all
datatype constructors can be internalized in our closed universe
hierarchy, drives the need for quantification over closed kinds
(\Con{`Set} and \Con{`Desc}). In turn, quantification over closed
kinds drives results in types (i.e. the previous universe), which
drives the need for lifting functions appropriate to each kind
(\Con{`⟦\_⟧}, \Con{`⟦\_⟧₁}, and \Con{`μ₁'}).
Thus, we recognize the sanity check in \refapen{intern} as a good way
to measure whether we have appropriately closed our hiearchy,
and are grateful for the structure that the check provides to the
definition of our hierarchy.
