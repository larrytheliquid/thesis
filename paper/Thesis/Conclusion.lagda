\AgdaHide{
\begin{code}
module _ where
open import Function
open import Appendix
open import Data.Nat
open Prim
\end{code}}

\chapter{Future Work}\label{ch:future}

This dissertation demonstrates that 
leveled fully generic programming is possible,
using a universe modeling a closed dependently typed language
supporting user-declared datatypes.
But, there is still much work left to do!
We discuss a small slice of this
future work, below. 

\section{Universe Polymorphism}

\AgdaHide{
\begin{code}
module _ where
 open Alg
 open ClosedHier
 private
  postulate
\end{code}}


In \refsec{hierireg}, we define the \textit{type} (in universe 0) of
closed natural numbers, whose signature is a \textit{kind}
(in universe 1).

\begin{code}
   `ℕ : ⟦ 1 ∣ `Set ⟧
\end{code}

In \refsec{count0}, we define fully generic \Fun{count}
over all values of all types (in universe 0), whose signature is also
a kind (in universe 1). When we use the type of natural numbers in the
kind signature of \Fun{count}, it must be lifted to the kind level
via \Con{`⟦\_⟧}.

\begin{code}
   count : ⟦ 1 ∣ `Π `Set (λ A → `⟦ A ⟧ `→ `⟦ `ℕ ⟧) ⟧
\end{code}

In \refsec{count1}, we define fully generic \Fun{Count}
over all types of all kinds (in universe 1), whose signature is
a superkind (in universe 2). When we use the type of natural numbers in the
superkind signature of \Fun{Count}, it must be lifted to the kind
level by using \Con{`⟦\_⟧} twice.

\begin{code}
   Count : ⟦ 2 ∣ `Π `Set (λ A → `⟦ A ⟧ `→ `⟦ `⟦ `ℕ ⟧ ⟧) ⟧
\end{code}

Types like dependent pairs (\Con{`Σ}) are built into the universe,
and appear at every level of the hiearchy. Therfore, we must handle the
\Con{`Σ} case of \Fun{Count} (in universe 1) in exactly the same way that we
handled it for \Fun{count} (in universe 0). Furthermore, if we want to
count all kinds of superkinds (in universe 2), we must define yet
fully generic counting function (and so on, for every level).
We could eliminate a lot of duplications by defining both algebraic
datatypes and functions \textit{universe polymorphically},
so they can be instantiated at any level of the universe.

\AgdaHide{
\begin{code}
module _ where
 open Alg
 open ClosedHier
 private
  postulate
\end{code}}

\begin{code}
   `ℕ : (ℓ : ℕ) → ⟦ suc ℓ ∣ `Set ⟧
   count : (ℓ : ℕ) → ⟦ suc ℓ ∣ `Π `Set (λ A → `⟦ A ⟧ `→ `ℕ (suc ℓ)) ⟧
\end{code}

Notice that the natural number codomain of \Fun{count} does not need
to be lifted, because we can just request a version of the natural
numbers at the \Con{suc}ccesor to level \Var{ℓ}. Also notice that we
can define \Fun{count} once at every level, so we do not need to
separately define \Fun{Count}.

Unfortunately, universe polymorphic
definitions rely on quantifying over levels in our metalanguage.
In other words, universe polymorphic definitions do not model fully
generic programs that we could write in our modeled closed dependently
typed language. For future work, we would like to add universe level
quantification as a code of our universe, so that the types of
definitions like \Fun{`ℕ} and \Fun{count} can be \textit{internalized}
(i.e. made to appear within the brackets).


\section{Large Induction-Recursion}

In this dissertation,
we close over inductive-recursive types (in \refsec{closed}),
but they are \textit{small}. Inductive-recursive types are small
if the codomain of the
decoding function can be any type, but it cannot be any kind
(like \Con{`Set} or \Con{`Desc}). We are not sure if it is possible to
define a closed universe of \textit{large} inductive-recursive types,
but we would like to try. It may be the case that we need a more
expressive type theory,
like Homotopy Type Theory~\cite{hottbook},
to close over large inductive-recursive types of
Martin-L{\"o}f’s type theory~\cite{martinintuitionistic}.

If we are able to close over large inductive-recursive types, then we
would need to encode indexed inductive-recursive algebraic types. This is
because the isomorphism between indexed types and inductive-recursive
types only holds in the small case~\cite{smallir}, so
inductive-recursive algebraic types would not be enough.

Finally, note that we cannot achieve large induction-recursion simply
by moving up a universe level. At universe level 1, the codomain of
a small decoding function could be any kind, but a large decoding
function would allow the codomain to be any superkind.

\section{High-Level Generic Programming}

In \refchap{fullyg}, we mention that we
can hide our algebraic encodings via smart constructors and pattern
synonyms, when defining \textit{concrete} functions
(i.e. over concrete datatypes).
However, we need to understand the underlying
\Con{init}ial-algebra base encoding,
when defining \textit{fully generic functions}.

McBride~\cite{Goguen06eliminatingdependent}
defines how to elaborate dependent pattern
matching, a high-level language feature, to eliminators, which can be
considered low-level induction principles of a core language.
We would like to explore implementing a closed dependently typed
language. It would be nice if we had a high-level feature for writing
fully generic functions, that could be elaborated to the fully generic
functions of this dissertations, which explicitly match on low-level
encodings (like the \Con{init}ial algebra).

Just like McBride allows users to define functions by dependent
pattern matching, without understanding how to program directly with
eliminators, we would like users to be able to define fully generic
functions, without understanding our closed universe model.
Finally, note that Dagand~\cite{dagand2012elaborating} has already
shown how to elaborate high-level datatype declarations to their
description-based (\Data{Desc}) encodings.

\section{Termination of Intensional Closed Type Theory}

In our related work (\refchap{related}), we discus
how Coquand~\cite{coquand:realizability} proves that an operational
semantics of type theory, consisting of the natural numbers closed
under dependent function formation, terminates.

The logical relation of this termination proof can be considered an
extended version of the closed universe model of natural numbers
closed under dependent function formation. We would like to
explore extending our model of closed inductive-recursive types
(\refapen{closed}) to a logical relation
(following Coquand's approach), and proving that an
operational semantics of closed type theory, supporting user-declared
datatypes (via \Data{Desc} and \Data{μ₁}), terminates.

\section{Inductive Definitions over Infinitary Domain}

Our fully generic \Fun{count} (\refsec{gcount}),
\Fun{lookup} (\refsec{glookup}), and
\Fun{ast} (\refsec{gast}) functions all treat the case of inductive
arguments of the initial algebra as a special case of infinitary
arguments. Being able to pattern matching against the domain of an
infinitary argument,
and ensuring that it is the unit type (\Con{`⊤}), demonstrates the
power of closed type theory (because we can match against a type).

In our previous work~\cite{diehl:gupdate}, we have also defined
higher-order domain supplements (\refsec{domsup}),
that allow us to write fully generic
functions over higher-order data (like the body of functions, or truly
infinitary arguments). However, neither the definition of \Fun{count}
in \refsec{gcount} (which requires matching against \Con{`⊤}), nor the
fully generic functions
using higher-order domain supplements~\cite{diehl:gupdate}, are
defined by \textit{induction} on the higher-order domains
(like the domain of functions or the domain of infinitary arguments).
In the future, we would like to explore what horizens have opened up
to us, now that our closed universe allows us to write functions
by induction on closed higher-order domains.

\chapter{Conclusion}\label{ch:conclusion}

Generic programming, within dependently typed programming languages,
over a universe closed under a fixed collection of type formers
(e.g. \refsec{closedvecu}) has a rich history.
If we consider such a universe to be a model of a
\textit{closed} dependently typed programming language, then users of that
language may use its fixed collection of types, but may not declare
their own domain-specific types.

Inspired by categorical models of algebraic semantics, which model
algebraic datatypes as least-fixed points of pattern functors,
type theorists have also defined formal models (i.e. in type theory)
of algebraic semantics. We can view strictly-positive polynomial
functors (\Data{Desc}) as codes of a universe,
whose meaning is their fixpoints (\Data{μ₁}).
Generic dependently typed programming over this algebraic universe
also has a rich history. Algebraic semantics is modeled as an
\textit{open} universe, which grows as users of the underlying open
type theory declare new datatypes.

The \textit{first} major contribution of this dissertation
(\refchap{closed})
is creating a closed
universe, modeling the types of a
\textit{closed} dependently typed programming
language that supports user-declared datatypes (\Data{`Desc}).
We still do this by
defining a universe closed under a fixed collection of type formers,
but one of the type formers is a \textit{closed} variant of
the fixpoint operator (\Con{`μ₁}) from algebraic semantics. This
variant is parameterized by a mutually defined \textit{closed} variant of
strictly-positive polynomial functors (\Data{`Desc}).

The \textit{second} major contribution of this dissertation
(\refchap{fullyg}) is demonstrating what we call
\textit{fully generic programming}. Fully generic functions are
defined over a closed universe including user-declared datatypes.
They can be defined once, working over all current datatypes,
but they continue to work as users declare
additional datatypes in the future.

The \textit{third} major contribution of this dissertation
(\refchap{hier})
is extending the model of closed types (supporting user-declarations)
to also model closed kinds, closed superkinds, etc. Hence, we model a
closed \textit{hierarchy} of universes supporting user-declared
datatypes. The closed hierarchy of universes models a
closed dependently typed programming language with a universe
hierarchy, supporting user-declared datatypes at every level of the
hierarchy. We also demonstrate leveled fully generic programming, or
writing fully generic functions at any level in the universe
hierarchy (over values, types, kinds, superkinds, etc.).
This achieves our goal, of modeling fully generic programming in a
closed dependently typed programming language, supporting
user-declared datatypes.

