\AgdaHide{
\begin{code}
module _ where
open import Data.Nat hiding (zero ; suc)
open import Relation.Binary.PropositionalEquality
open import Function
open import Appendix
\end{code}}

\chapter{Fully Generic Functions}\label{ch:fullyg}

In this chapter\footnote{
  This chapter is
  adapted from work by myself and Sheard~\cite{diehl:gupdate},
  as explained in \refsec{previous}.
} we formally model fully generic programming in a
closed dependently typed language. We write fully generic functions in
the universe of \refsec{closed},
supporting user-declared datatypes while remaining closed.

Thus far we have focused on defining concrete datatypes in our
universe of (inductive-recursive) algebraic types.
\textit{Smart constructors} (defined as functions, first demonstrated
in \refsec{nondepalgtps}), for the type former and constructors of a
concrete algebraic datatype, allow us
to \textit{construct} concrete types and their values while hiding
their generic encoding in terms of initial algebra
semantics. Similarly, \textit{pattern synonyms}
(demonstrated in \refsec{nondepalgtps}),
for constructors of
concrete types encoded using initial algebra semantics,
allow us to
\textit{deconstruct} generically encoded values by writing
functions defined by pattern matching
while hiding underlying algebraic encodings.

While smart constructors and pattern synonyms shelter users from
generic encodings when they construct and deconstruct
\textit{concrete} datatypes, fully generic programming requires users
to understand how to generically construct and deconstruct \textit{encoded}
datatypes, by applying and matching against the \Con{init}ial algebra
constructor of \Data{μ₁}. By definition, fully generic functions can
be applied to (and may return) values of any user-declared type, thus
understanding the underlying generic encoding
(or something isomorphic to it) is necessary. In this
chapter we define three fully generic functions:
\begin{enumerate}
\item \Fun{count}, in \refsec{gcount}, counting the number of nodes
  in a generically encoded value.
\item \Fun{lookup}, in \refsec{glookup}, looking up any subnode of
  a generically encoded value.
\item \Fun{ast}, in \refsec{gast}, marshalling any generically
  encoded value to an abstract syntax tree (AST), defined as a rose
  tree.
\end{enumerate}

\paragraph{Major Ideas}

The purpose of this chapter is to demonstrate examples of fully
generic programming over the universe defined in
\refsec{closed} (which also appears in \refapen{closed}). Traditional
generic programs (as explained in the introduction
of \refchap{intro}) only recurse into inductive constructor
arguments. We could write a traditional generic \Fun{size} function,
like the one in \refsec{introsize}, over the open universe of
inductive-recursive types in \refsec{iralgagda}. We could also write
other traditional generic functions that only need to recurse into
inductive constructor arguments, such as \Fun{map} and
\Fun{fold}.

In contrast, this chapter focuses on writing fully generic
programs, like the \Fun{count} function of \refsec{introcount}. Fully
generic programs can recurse into \textit{both} the inductive and
non-inductive arguments of constructors. In \refsec{gcount}, we define
a fully generic \Fun{count} function over the closed universe of
\refsec{closed}, modeling a dependently typed language supporting
user-declared types. 
Functions that marshal data into another format
(such as binary, JSON, XML, etc.)
are a prime example of fully generic programming. When marshaling
data, it is not enough to marshal just the
\textit{inductive structure} of values, we also want to marshal all of
the \textit{non-inductive} values contained in the structure.

\refsec{gast} features a fully generic function (\Fun{ast}) that
marshals data into a common rose tree format, used to visualize values
with Graphviz~\cite{graphviz}.
The primary thing to notice in this chapter is that the definitions of
generic functions recurse into non-inductive arguments. This includes
recursion into both components of the built-in type of pairs
(in the \Con{`Σ} case of closed built-in types \Data{`Set}),
and recursion into
non-inductive constructor arguments (in the \Con{`σ} case of
closed functor descriptions \Data{`Desc}).

\section{Fully Generic Count}\label{sec:gcount}

In this section, we develop a fully generic \Fun{count} function
that counts the number of nodes that make up a generically encoded
value. The \Fun{count} function is used in the type of the
subsequently-defined generic \Fun{lookup} in \refsec{glookup}.
The \Fun{count} function is used as the maximum bound for
the index argument of \Fun{lookup}.

\subsection{Generic Types}

Before covering the details of implementing \Fun{count}, we return
to the introduction of our dissertation to clarify our intuition about
the type signatures of fully generic functions.
In \refsec{naivegfun}, we hinted that any fully
generic function can be defined by mutually defining a function over
all types and another function over all descriptions (whose fixpoint
is a special case of the function over all types). 

$$
(\Var{A} : \Data{Type})~
(\Var{a} : \AgdaFun{⟦}~\AgdaVar{A}~\AgdaFun{⟧})
→ ...
$$
$$
(\Var{D} : \Data{Desc})~
(\Var{x} : \AgdaData{μ}~\AgdaVar{D})
→ ...
$$

Specializing this template to a generic \Fun{count}, and
making some changes to work with our closed universe of
\refsec{closed} (discussed below), results in the following two
mutually defined functions.

\AgdaHide{
\begin{code}
module _ where
 open Prim
 open Alg
 open Closed
 private
  postulate
\end{code}}

\begin{code}
   count : (A : `Set) → ⟦ A ⟧ → ℕ
   countμ : {O : `Set} (D : `Desc O) → μ₁ ⟦ O ⟧ ⟪ D ⟫ → ℕ
\end{code}

The intuition (presented in \refsec{naivegfun} of the introduction)
behind the closed \Fun{count} function is largely correct. The only
difference is that we have renamed \Data{Type} to \Data{`Set}, to
notationally emphasize that its interpretation as a \Data{Set} is
obtained by ``removing the backtick''.

However, the intuition behind the closed \Fun{countμ} function is
simplified in the introduction. A minor difference is that we must
add an \Var{O} parameter, to account for the codomain of the
inductive-recursive decoding function.

The first major difference is that
the intuition from the introduction leads to defining \Fun{countμ}
over all \textit{open} descriptions (\Data{Desc}), but fully generic
programming demands that we define it over all \textit{closed}
descriptions (\Data{`Desc}). Let's remind ourselves of the definition
(from \refsec{iralgagda})
of the type component of the fixpoint operator:

\AgdaHide{
\begin{code}
module _ where
 open Prim
 open Alg hiding ( μ₁ )
 private
\end{code}}

\begin{code}
   data μ₁ (O : Set) (D : Desc O) : Set where
     init : ⟦ D ⟧₁ D → μ₁ O D
\end{code}

Recall that \Data{μ₁} expects \Var{O} to be the kind of open types
(\Data{Set}), and \Var{D} to be the kind of open descriptions
(\Data{Desc}). When we write the type of a generic function, like
\Fun{countμ}, we quantify over all closed types \Var{O}
(of type \Data{`Set}), and all closed descriptions 
\Var{D} (of type \Data{`Desc}).

The third argument to \Fun{countμ}
is the result of applying the type meaning function (\Fun{⟦\_⟧}) to
the closed type (\Con{`μ₁} \Var{O} \Var{D}), which definitionally
reduces to \Data{μ₁} applied the
type meaning (\Fun{⟦\_⟧}) of \Var{O}
and the description meaning (\Fun{⟪\_⟫}) of \Var{D}.
This models values of closed types within our open metalanguage,
Agda (using open types like \Data{μ₁}).

The second major difference between the types we use for fully
generic programming, and the types behind the intuition in the
introduction, is that we cannot directly define a function like
\Fun{countμ} over all closed descriptions.
The problem is that the
inductive hypothesis is not general enough in the
infinitary (hence, also inductive) \Con{`δ} case.
If we tried to write \Fun{countμ} directly, we would not remember
the original inductive description when we reach the \Con{`δ} case,
because \Fun{countμ} would be defined by recursively destructing
the description argument.

Instead of mutually
defining \Fun{count} with \Fun{countμ} (a function over all algebraic
types), we mutually define
\Fun{count} with \Fun{counts} (a function over all
arguments of algebraic types, isomorphic to \Fun{countμ}).
The \Fun{counts} function has an extra description argument, \Var{R},
that stays constant to remember the original description as the
\Var{D} description argument is recursively destructed.

\AgdaHide{
\begin{code}
module _ where
 open Prim
 open Alg
 open Closed
 private
  postulate
\end{code}}

\begin{code}
   counts : {O : `Set} (D R : `Desc O) → ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫ → ℕ
\end{code}

Recall that \Fun{⟦\_⟧₁} (defined below, for reference)
is the type component of the interpretation
function for descriptions. It appears as the sole argument to the
\Con{init}ial algebra constructor of \Data{μ₁}. Because \Data{μ₁} \Var{O} \Var{D} is
isomorphic to \Fun{⟦} \Var{D} \Fun{⟧₁} \Var{D}, defining \Fun{counts}
is an acceptable alternative to defining \Fun{countμ}.

\AgdaHide{
\begin{code}
module _ where
 open Prim
 open Alg hiding ( ⟦_⟧₁ )
 private
\end{code}}

\begin{code}
   ⟦_⟧₁ : {O : Set} (D R : Desc O) → Set
   ⟦ ι o ⟧₁ R = ⊤
   ⟦ σ A D ⟧₁ R = Σ A (λ a → ⟦ D a ⟧₁ R)
   ⟦ δ A D ⟧₁ R = Σ (A → μ₁ _ R) λ f → ⟦ D (λ a → μ₂ R (f a)) ⟧₁ R
\end{code}

The interpretation function (\Fun{⟦\_⟧₁}) recurses over the first argument (\Var{D}) to
determine the type of constructor arguments, while holding the second
argument (\Var{R}) constant. This allows
\Fun{⟦\_⟧₁} to remember the original \textit{complete} description
(\Var{R}) of the algebraic type, even though it is destructing a copy
of it (\Var{D}) as it recurses.

By remembering the original description
(\Var{R}), the open \Con{δ} case can request an infinitary (hence, also
inductive) argument as the first argument to \Data{Σ}.
For analogous reasons, \Fun{counts} is generically defined over
all descriptions (\Var{D}), but also a copy (\Var{R}) of the original
\textit{complete} description that it can use to count infinitary
arguments in the closed \Con{`δ} case.

In summary, we define how to generically count values of the closed
universe in terms of 2 mutually defined functions,
\Fun{count} and \Fun{counts}. The first is defined over all closed
types (\Data{`Set}) and the second is defined over all closed
descriptions (\Data{`Desc}).

\subsection{Counting All Values}\label{sec:count}

First, let's define \Fun{count} fully generically for all values of
all types (of \refapen{closed}).
This involves calling \Fun{counts} in the \Con{`μ₁} case,
defined mutually (in \refsec{counts}) over all arguments of the
\Con{init}ial algebra.
Below, we restate the type of \Fun{count}, and then define
\Fun{count} by case analysis and recursion over all of its closed
types. 

\AgdaHide{
\begin{code}
module Count where
 open Prim
 open Alg
 open Closed
 mutual
\end{code}}

\begin{code}
  count : (A : `Set) → ⟦ A ⟧ → ℕ
\end{code}

Recall that we wish to define \Fun{count} as the sum of all
constructors and the recursive \Fun{count} of all constructor
arguments. It may be helpful to review \Fun{count} for the
\textit{fixed} closed universe in the introduction
(\refsec{introcount}), to see how it compares to our new \Fun{count},
defined over an \textit{extendable} closed universe
(by user-declared datatypes).

\paragraph{Dependent Pair}

We \Fun{count} a dependent pair by summing the recursive
\Fun{count} of both its components (\Var{a} and \Var{b}),
plus 1 to also count the pair constructor (\Con{,}).

\begin{code}
  count (`Σ A B) (a , b) = 1 + count A a + count (B a) b
\end{code}

Notice that the
\textit{dependent} type of the second component (\Var{b}) is computed by
applying the codomain of the dependent pair (\Var{B}) to the
first component (\Var{a}).

\paragraph{Algebraic Fixpoint}

We \Fun{count} an algebraic fixpoint by recursively counting its
arguments (\Var{xs}) using \Fun{counts}, plus 1 to account
for the \Con{init} constructor.

\begin{code}
  count (`μ₁ O D) (init xs) = 1 + counts D D xs
\end{code}

When we initially call \Fun{counts},
\Var{D} is used for both of its arguments. However, as \Fun{counts}
recurses, the first description argument will be destructed while the
second (original) description argument is held constant.

\paragraph{Remaining Values}

All constructors of the remaining types (such as \Data{Bool}) do not
have arguments, so we \Fun{count} them as 1 (for their constructor,
plus 0 for their arguments).
Note that this includes functions (the \Con{`Π} case),
which we treat as a black box by counting the $\lambda$ constructor as
1, without recursively counting its body.

\begin{code}
  count A a = 1
\end{code}

\subsection{Counting Algebraic Arguments}\label{sec:counts}

Second, let's define \Fun{counts} fully generically for all
arguments of the \Con{init}ial algebra. This involves calling
\Fun{count} in the \Con{`σ} and \Con{`δ} cases,
defined mutually (in \refsec{count}) over all values of all types.
Below, we restate the type of \Fun{counts}, and then define
\Fun{counts} by case analysis and recursion over all of its closed
descriptions (for reference, the declaration of \Data{Desc}
appears in \refapen{openalg}). 

\begin{code}
  counts : {O : `Set} (D R : `Desc O) → ⟦ ⟪ D ⟫ ⟧₁ ⟪ R ⟫ → ℕ
\end{code}

Recursion is performed over the first description
argument (\Var{D}), while the second argument (\Var{R}) is kept
constant, so we have access to the original description in
the inductive \Con{`δ} case.

Finally, our intention is to \Fun{count} an algebraic value
\Con{init} \Var{xs} as 1 (for \Con{init}) plus the recursive sum of all of its
arguments (for \Var{xs}). Even though \Var{xs} is technically implemented as a
sequence of dependent pairs (\Con{,}), we will not add 1 for each
pair constructor (\Con{,}), which we choose to view as part of the encoding
rather than something to be counted. Hence, \Fun{counts} treats its argument
\Var{xs} as a single $n$-tuple, rather than several nested
pairs.\footnote{
  Although we are hiding the nested-pairs (of the initial algebra)
  aspect of the encoding, we are exposing the encoding when counting
  constructors. Constructors are encoded as a dependent pair,
  representing a disjoint union. Our \Fun{count} function counts the
  boolean and the pair constructor, rather than hiding that aspect of
  the encoding. We could create a separate universe of codes
  that explicitly represents constructors, along with a new meaning
  function mapping to the underlying \Data{Desc}riptions,
  so that our generic \Fun{count} could hide the encoding
  of constructors as derived disjoint unions. However, we chose not to do
  so to make the presentation easier to follow.
  }

\paragraph{Non-Inductive Argument}

When we come across a non-inductive argument in a sequence of
arguments, we sum the \Fun{count} of the non-inductive argument
(\Var{a}) with the \Fun{counts} of the remainder of the sequence of
arguments (\Var{xs}). 

\begin{code}
  counts (`σ A D) R (a , xs) = count A a + counts (D a) R xs
\end{code}

Note that \Var{a} is counted using our mutually
defined \Fun{count} over all values, and \Var{xs} is recursively counted
(via \Fun{counts})
using the description resulting from
applying the \textit{dependent} description \Var{D} (of \Con{`σ})
to the value \Var{a}. The original description \Var{R} is
passed to \Fun{counts} unchanged.

\paragraph{Inductive Argument}

When we come across an inductive argument, in a sequence of
arguments, we sum the \Fun{count} of the inductive argument
(\Var{x}) with the \Fun{counts} of the remainder of the sequence of
arguments (\Var{xs}).

\begin{code}
  counts (`δ `⊤ D) R (f , xs) = count (`μ₁ _ R) (f tt) +
    counts (D (μ₂ ⟪ R ⟫ ∘ f)) R xs
\end{code}
  
Inductive arguments are a special case of infinitary arguments where
the domain of the infinitary function is the unit type (\Data{⊤}).
The first argument to the \textit{closed description} \Con{`δ} is a
\textit{closed type}. Because the first argument is a closed type, we
can pattern match against the closed unit type (\Con{`⊤}). This allows
us to distinguish how we count \textit{inductive} arguments from how
we count \textit{infinitary} arguments, and is \textit{only possible} because
our universe is \textit{closed} (i.e., if the argument had kind
\Data{Set}, it would be open and we could not pattern match against
it)!

The inductive argument is obtained by applying the infinitary argument
\Var{f} to the trivial value \Con{tt}. But what type should we
use to \Fun{count} it? Because it is an \textit{inductive}
(hence, algebraic) value, the type should be the fixpoint (\Con{`μ₁})
applied to some description. We kept the original description
(\Var{R}) to count inductive arguments for exactly this case.

The remaining sequence of arguments (\Var{xs}) is recursively counted
(via \Fun{counts}) using the description resulting from
applying the \textit{dependent} description \Var{D} (of \Con{`δ})
to the \textit{composition} of the decoding function fixpoint
component (\Fun{μ₂}) and the infinitary value \Var{f}.
Recall (from \refsec{iralgmod}) that the \Var{D} argument of \Con{`δ}
is a description that
depends on the \textit{decoding function} for our inductive-recursive type.
The \textit{type} of the decoding function is the \textit{implicit} composition
of the decoding fixpoint component (\Fun{μ₂}) and the infinitary value
\Var{f} (the nature of the implicit composition is explained
in \refsec{iralgmod}). In our generic function above, we \textit{explicitly} create
the \textit{value} of this decoding function to satisfy the implicit
expectation in the type of its description.

\paragraph{Infinitary Argument}

When we come across an infinitary argument, in a sequence of
arguments, we add 1 to the \Fun{counts} of the remainder of the
sequence of arguments (\Var{xs}).
This counts the infinitary $\lambda$ constructor as 1, treating it as
a black box, analogous to how we \Fun{count} the \Con{`Π} case as 1.


\begin{code}
  counts (`δ A D) R (f , xs) = 1 + counts (D (μ₂ ⟪ R ⟫ ∘ f)) R xs
\end{code}

The remaining sequence of arguments (\Var{xs}) is recursively counted
just like the inductive (\Con{`δ} \Con{`⊤}) case, where the dependent description \Var{D}
is applied to the composition of the fixpoint interpretation component
(\Fun{μ₂}) and the infinitary argument (\Var{f}).

\paragraph{Last Argument}

Every sequence of algebraic constructor arguments terminates in the
trivial value \Con{tt} of type unit (\Data{⊤}), which we count as 1.

\begin{code}
  counts (`ι o) R tt = 1
\end{code}

We could choose to count the trivial (\Con{tt}) last argument as
0, hiding the aspect of the encoding that every sequence of arguments
is terminated by \Con{tt}. However, we choose to count \Con{tt} as 1
because the subsequently defined generic function,
\Fun{lookup} in \refsec{glookup},
treats the result of \Fun{count} as
an \textit{index} into all values and subvalues of a type.\footnote{
  Given our generic encoding of \textit{inductive-recursive} types,
  the ability to \Fun{count} or \Fun{lookup} the trivial
  value (\Con{tt}) may not seem useful. Nevertheless, we include this
  functionality because it becomes useful when generalizing our
  universe to include \textit{indexed} algebraic types. In the initial
  algebra semantics for indexed types, the final unit type (\Data{⊤})
  is replaced by the identity type (\Data{Id}), used as a constraint
  on the index of the algebraic type. Being able to
  \Fun{count} and \Fun{lookup} the constraint is important in the
  indexed universe.
}

\subsection{Examples}\label{sec:gcount:egs}

\AgdaHide{
\begin{code}
module Data where
  open Prim
  open Alg
  open Closed
  open Count
  NatDs : Bool → `Desc `⊤
  NatDs true = `ι tt
  NatDs false = `δ `⊤ (λ f → `ι (f tt))

  NatD : `Desc `⊤
  NatD = `σ `Bool NatDs

  `ℕ : `Set
  `ℕ = `μ₁ `⊤ NatD

  suc : ⟦ `ℕ ⟧ → ⟦ `ℕ ⟧
  suc n = init (false , (λ u → n) , tt)
\end{code}}

Now that we've defined \Fun{count} fully generically, let's run it on
some examples to better understand how it works.
The key lesson to take away is that \Fun{count} and \Fun{counts}
use a \textit{depth-first} traversal to count values and subvalues.

\paragraph{Natural Numbers}

First, we consider counting the closed encoding of the natural number 0.
It may be helpful to review the closed definition of the natural
numbers in \refsec{closedeg}.
The natural number 0 is encoded (below) by \Fun{zero}
as the \Con{init}ial algebra
applied to a dependent pair (\Con{,}) consisting of the boolean
\Con{true} (selecting the zero-constructor
branch of the dependent description used to encode the natural
numbers), and the unit value (\Con{tt}).

\begin{code}
  zero : ⟦ `ℕ ⟧
  zero = init (true , tt)
\end{code}

We generically \Fun{count} the closed \Fun{zero} by summing 1 for
the \Con{init}ial algebra constructor, 1 for the \Con{true} argument,
and 1 for the terminating unit argument (\Con{tt}), resulting in 3.\footnote{
  Once again, this is an encoding-aware \Fun{count}, because it is
  used to \textit{index} which nodes (in a generically encoded
  data structure) to \Fun{lookup} (in \refsec{glookup}).
  It would also be possible to
  define an encoding-unaware \Fun{count}, that does not count \Con{true}
  (encoding constructor choice) and \Con{tt} (encoding the end of the
  sequence of constructors).
  Encoding-unaware \Fun{count} could be generically
  defined over a universe
  of constructor-aware descriptions, equipped with an interpretation
  function to translate constructor-aware descriptions into our
  constructor-unaware descriptions.
  Applying an encoding-unaware \Fun{count}
  to \Fun{zero} would result in 0, as it would not count constructor
  choice data (like \Con{true}) or argument sequence data (like
  \Con{tt}).
}

\AgdaHide{
\begin{code}
  _ :
\end{code}}

\begin{code}
   count `ℕ zero ≡ 3 
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}

Next, let's define the closed natural number 1. We can define
\Fun{one} by applying our closed \Fun{suc}cessor
(from \refsec{closedeg}) to our closed \Fun{zero}.

\begin{code}
  one : ⟦ `ℕ ⟧
  one = suc zero
\end{code}

Expanding these definitions results in the closed encoding of 1
below.

\AgdaHide{
\begin{code}
  _ :
\end{code}}

\begin{code}
   one ≡ init (false , (λ _ → init (true , tt)) , tt)
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}

The \Con{false} value in the closed \Fun{one} definition selects the
successor branch of the description, and the next argument contains
the inlined definition of \Fun{zero}, wrapped in a function ignoring
its trivial unit argument. Recall that \textit{inductive}
natural numbers are
encoded as \textit{trivially infinitary} types,
using the unit type (\Data{⊤}) as the domain of the infinitary
function. The \textbf{Inductive} case of \Fun{counts} is able to
recursively count
the inductive body of the \Fun{suc}cessor (i.e., \Fun{zero}) because it
is able to pattern match against the closed type \Con{`⊤} to
distinguish counting inductive (or trivially-infinitary)
arguments from counting (truly) infinitary arguments.

\AgdaHide{
\begin{code}
  _ :
\end{code}}

\begin{code}
   count `ℕ one ≡ 6
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}

Finally, we \Fun{count} closed \Fun{one} as 6, adding up 1 for each
constructor appearing in the encoded definition
(\Con{init}, \Con{false}, \Con{init}, \Con{true}, \Con{tt}, and
\Con{tt}), from left to right.
The reason behind that order is that \Fun{count} and \Fun{counts}
recursively add 1 for each encoded constructor by doing a
\textit{depth-first} traversal. To help visualize the traversal, and
aid in the legibility of encoded values, refer to
\reffig{one}.
The edges of \reffig{one} are labeled according to a
depth-first traversal of nodes (where 0 is an implicit edge for the
root node). Because \Fun{count} (and \Fun{counts})
traverses in a depth-first manner, each edge represents the aggregate
count at the time \Fun{count} is called for the corresponding node.
Note that the result of applying \Fun{count} to the root node is 1
plus the final edge (1 + 5, above).\footnote{
  All algebraic types in figures hide the infinitary $\lambda$
  constructor at inductive argument positions,
  because \Fun{count} (whose depth-first traversal the
  Figure represents) implicitly applies trivially infinitary functions
  to \Con{tt} in the \textbf{Inductive} (\Con{`δ}) case.
  }

\begin{figure}[ht]
\centering
\includegraphics[scale=0.8]{one.pdf}
\caption{The natural number 1, as a closed algebraic type.}
\label{fig:one}
\end{figure}

The depth-first labeling of edges pointing to nodes that \Fun{count}
performs makes it an ideal function to index positions of arguments in
generically encoded values. For example, in \reffig{one} we can see value
\Fun{zero} at edge 2, and value \Fun{one} at edge 0 (the root node).
Finally, let's define closed \Fun{two}.

\begin{code}
  two : ⟦ `ℕ ⟧
  two = suc one
\end{code}

\begin{figure}[ht]
\centering
\includegraphics[scale=0.8]{two.pdf}
\caption{The natural number 2, as a closed algebraic type.}
\label{fig:two}
\end{figure}

\Fun{Count}ing closed \Fun{two} results in 9, as can be seen in
\reffig{two} (by adding 1 to the final edge 8).
In \reffig{two}, \Fun{two} appears at edge 0,
\Fun{one} appears at edge 2, and \Fun{zero} appears at
edge 4.

\AgdaHide{
\begin{code}
  _ :
\end{code}}

\begin{code}
   count `ℕ two ≡ 9
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}

\AgdaHide{
\begin{code}
  VecDs : `Set → Bool → `Desc `ℕ
  VecDs A true = `ι zero
  VecDs A false =
    `σ `ℕ λ n →
    `σ A λ a →
    `δ `⊤ λ xs →
    `σ (`Id `ℕ (xs tt) n) λ q →
    `ι (suc n)

  VecD : `Set → `Desc `ℕ
  VecD A = `σ `Bool (VecDs A)

  `Vec₁ : `Set → `Set
  `Vec₁ A = `μ₁ `ℕ (VecD A)
  
  `Vec₂ : (A : `Set) → ⟦ `Vec₁ A ⟧ → ⟦ `ℕ ⟧
  `Vec₂ A = μ₂ ⟪ VecD A ⟫
  
  `Vec : `Set → ⟦ `ℕ ⟧ → `Set
  `Vec A n = `Σ (`Vec₁ A) (λ xs → `Id `ℕ (`Vec₂ A xs) n)

  cons : {A : `Set} {n : ⟦ `ℕ ⟧} (a : ⟦ A ⟧) (xs : ⟦ `Vec A n ⟧) → ⟦ `Vec A (suc n) ⟧
  cons {n = n} a (xs , refl) = init (false , n , a , (λ u → xs) , refl , tt) , refl
\end{code}}

\paragraph{Vectors}

Now let's encode the closed 0-length empty vector (\texttt{[]}).
Again, it may be helpful to review the closed definition of
vectors in \refsec{closedeg}.
Recall that indexed vectors are encoded as a dependent pair whose first
component is an inductive-recursive \Fun{`Vec₁}
(like a list, but with natural number arguments and
index constraints on inductive occurrences), and whose second
component constrains (via the equality type \Data{Id}) the
decoding (via \Fun{`Vec₂}, or the length function) of the first component
to be the appropriate index.

Below, the closed empty vector \texttt{[]} is encoded
by \Fun{nil} as such a dependent pair, where the first component
is an \Con{init}ial algebra value (of type \Fun{`Vec₁}),
and the second component is a proof (using \Con{refl}, the
constructor of equality type \Data{Id}) that \Fun{`Vec₂} applied to the
first component is indeed \Fun{zero}
(the expected length of the empty vector, as specified
by its type).

\begin{code}
  nil : {A : `Set} → ⟦ `Vec A zero ⟧
  nil = init (true , tt) , refl
\end{code}

Our examples count vectors of pairs of strings.
The generic \Fun{count} of the empty vector (i.e., \Fun{nil}) of pairs
of strings is 5, the sum of 1 for \Con{init}, \Con{true}, \Con{tt},
(\Con{,}), and \Con{refl}.

\AgdaHide{
\begin{code}
  _ :
\end{code}}

\begin{code}
   count (`Vec (`String `× `String) zero) nil ≡ 5
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}

Next, let's define length-1 closed vector of pairs of strings
\texttt{[("a", "x")]}. We can define
\Fun{vec1} by applying our closed \Fun{cons} constructor
(from \refsec{closedeg}) to our closed \Fun{zero} constructor.

\AgdaHide{
\begin{code}
module _ where
 open Prim
 open Alg
 open Closed
 open Data
 private
\end{code}}

\begin{code}
  vec1 : ⟦ `Vec (`String `× `String) one ⟧
  vec1 = cons ("a" , "x") nil
\end{code}

Expanding these definitions results in the closed encoding of
\texttt{[("a", "x")]} below.

\AgdaHide{
\begin{code}
  _ :
\end{code}}

\begin{code}
   vec1 ≡ (init
            ( false
            , init (true , tt)
            , ("a" , "x")
            , (λ _ → init (true , tt))
            , refl
            , tt)
           , refl)
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}

To understand this, it is worth remembering that indexed vectors
(\Fun{`Vec}) are defined as a constraint paired with an
inductive-recursive (but not indexed)
version of the vector (\Fun{`Vec₁}). Below, we directly define
the indexed vector \Fun{vec1} (of type \Fun{`Vec}),
without using the smart constructors
\Fun{cons} and \Fun{nil}, in terms
of the auxiliary definition \Fun{vec1₁} for the
inductive-recursive (\Fun{`Vec₁})
left component of the pair (of type \Fun{`Vec₁}).

\begin{figure}[ht]
\centering
\includegraphics[scale=0.7]{vec1.pdf}  
\caption{The length-1 vector of pairs of strings
  \texttt{[("a", "x")]}, as a closed algebraic type.}
\label{fig:vec1}
\end{figure}

\AgdaHide{
\begin{code}
module VecEg where
  open Prim
  open Alg
  open Closed
  open Count
  open Data

  nil₁ : ⟦ `Vec₁ (`String `× `String) ⟧
  nil₁ = init (true , tt)

  cons₁ : {A : `Set} {n : ⟦ `ℕ ⟧} (a : ⟦ A ⟧) (xs : ⟦ `Vec A n ⟧) → ⟦ `Vec₁ A ⟧
  cons₁ {n = n} a (xs , refl) = init (false , n , a , (λ u → xs) , refl , tt)
\end{code}}

\begin{code}
  vec1₁ : ⟦ `Vec₁ (`String `× `String) ⟧
  vec1₁ = init
    ( false
    , init (true , tt)
    , ("a" , "x")
    , (λ _ → init (true , tt))
    , refl
    , tt)

  vec1 : ⟦ `Vec (`String `× `String) one ⟧
  vec1 = vec1₁ , refl
\end{code}

To understand how \Fun{vec1} is counted (as 15), we refer to
our visual presentation in \reffig{vec1}, depicting
the depth-first traversal of \Fun{count}.
The root node is \Fun{vec1} (of type \Fun{`Vec}),
the dependent pair. Node 14 is the
constraint (of type \Data{Id})
that the left component has length \Fun{one}.
Node 1 is the inductive-recursive \Fun{vec1₁} (of type \Fun{`Vec₁}).

We establish
the convention that suffixing a term or constructor by \texttt{₁} refers to the
inductive-recursive (of type \Fun{`Vec₁}) equivalent of the
constraint pair of type \Fun{`Vec}. For example, \Fun{nil₁}
refers to an empty inductive-recursive vector of type \Fun{`Vec₁},
the left component of the constraint pair \Fun{nil}
of type \Fun{`Vec} (mirroring the
relationship between \Fun{vec1₁} and \Fun{vec1}, above).

In \reffig{vec1} (and all of our figures),
we draw boxes around the outermost occurrence
of an inductive value. For example, the root node does not have a box
around it, because it is a non-inductive pair (of type \Con{`Σ}).
However, node 1 has a box around it, for the inductive
\Fun{`Vec₁} value (\Fun{vec1₁}). Within a box, any occurrence
of \Con{init} represents an inductive occurrence whose type shares the
type of the box. For example, node 9 is a \Fun{nil₁} value of
type \Fun{`Vec₁}. Recall that each inductive argument of the
inductive-recursive \Fun{`Vec₁} is packaged with a constraint
on its length (calculated by the
inductive-recursive decoding function \Fun{`Vec₂}).
Node 12 is the constraint that the length
of node 9 (encoding the inductive occurrence of
\Fun{nil₁} within the box for \Fun{vec1₁}, at node 1) is 0.

Node 2 is \Con{false}, representing the choice of the \Fun{cons₁}
constructor in the description of \Fun{`Vec₁}.
Node 6 is the non-inductive pair (\Con{\_,\_}) of strings
\Str{"a"} and \Str{"b"} contained by the vector.
Node 3 contains a box
around it, meaning it is an occurrence of an inductive type distinct
from \Fun{`Vec₁}. Specifically, node 3 is the natural number
\Fun{zero}, constrained to equal the length of
the empty vector (\Fun{nil₁}) at node 9,
in the type of the constraint (\Con{refl}) at node 12. Finally, nodes 5, 11, and 13
all represent the terminating unit (\Con{tt}) of an algebraic sequence
of arguments.


\AgdaHide{
\begin{code}
  _ :
\end{code}}

\begin{code}
   count (`Vec (`String `× `String) one) vec1 ≡ 15
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}

Finally, let's define the length-2 closed vector of pairs of strings
\texttt{[("a", "x"), ("b", "y")]}. We can define
\Fun{vec2} with our closed constructors \Fun{nil} and \Fun{cons}
of closed \Fun{Vec}tors.

\begin{code}
  vec2 : ⟦ `Vec (`String `× `String) two ⟧
  vec2 = cons ("a" , "x") (cons ("b" , "y") nil)
\end{code}

\afterpage{
\begin{sidewaysfigure}[ht]
\centering
\includegraphics[scale=0.6]{vec2.pdf}  
\caption{The length-2 vector of pairs of strings
  \texttt{[("a", "x"), ("b", "y")]},
  as a closed algebraic type.}
\label{fig:vec2}
\end{sidewaysfigure}
\clearpage
}

The fully generic \Fun{count} of \Fun{vec2} is 28, as justified
by \reffig{vec2}.
In \reffig{vec2}, node 12 is the length-1 \Str{"b"} and \Str{"y"}
component of type \Fun{`Vec₁}. Node 14 is the natural number
\Fun{zero}, the length of \Fun{nil₁} at node 20. Node 3 is the natural
number \Fun{zero}, the length of the \Str{"b"} and \Str{"y"} vector
at node 12.

\AgdaHide{
\begin{code}
  _ :
\end{code}}

\begin{code}
   count (`Vec (`String `× `String) two) vec2 ≡ 28
\end{code}

\AgdaHide{
\begin{code}
  _ = refl
\end{code}}

We conclude this section by reflecting on how
the relationship between algebraically defined length-indexed
vectors and their algebraically defined natural numbers is elegantly
captured in \reffig{vec2}. Notice how natural numbers
(nodes 3 and 14) appear at the same level, and have the same
height, as their vector equivalents (nodes 12 and 20).
This visually demonstrates how the natural number argument of
\Con{cons} is mirrored by the structure of the inductive argument of
\Con{cons}, enforced by their relationship in the definition of
the indexed type of vectors. 

%% \subsection{Generic Lemmas}

\AgdaHide{
\begin{code}
module Split where
 open Prim
 open Alg
 open Closed
 open Count
 open import Data.Sum
 open import Data.Nat
 open import Data.Fin renaming ( zero to here ; suc to there ) hiding ( _+_ )

 splitFin : (n m : ℕ) → Fin (n + m) → Fin n ⊎ Fin m
 splitFin zero m i = inj₂ i
 splitFin (suc n) m here = inj₁ here
 splitFin (suc n) m (there i) with splitFin n m i
 ... | inj₁ j = inj₁ (there j)
 ... | inj₂ j = inj₂ j

 splitΣ : (A : `Set) (B : ⟦ A ⟧ → `Set)
   (a : ⟦ A ⟧) (b : ⟦ B a ⟧) →
   Fin (count A a + count (B a) b) →
   Fin (count A a) ⊎ Fin (count (B a) b)
 splitΣ A B a b i = splitFin (count A a) (count (B a) b) i

 splitσ : {O : `Set} (A : `Set) (D : ⟦ A ⟧ → `Desc O) (R : `Desc  O)
   (a : ⟦ A ⟧) (xs : ⟦ ⟪ D a ⟫ ⟧₁ ⟪ R ⟫) →
   Fin (count A a + counts (D a) R xs) →
   Fin (count A a) ⊎ Fin (counts (D a) R xs)
 splitσ A D R a xs i = splitFin (count A a) (counts (D a) R xs) i

 splitδ : {O : `Set} (D : ⟦ O ⟧ → `Desc O) (R : `Desc  O)
   (x : μ₁ ⟦ O ⟧ ⟪ R ⟫) (xs : ⟦ ⟪ D (μ₂ ⟪ R ⟫ x) ⟫ ⟧₁ ⟪ R ⟫) →
   Fin (count (`μ₁ O R) x + counts (D (μ₂ ⟪ R ⟫ x)) R xs) →
   Fin (count (`μ₁ O R) x) ⊎ Fin (counts (D (μ₂ ⟪ R ⟫ x)) R xs)
 splitδ D R x xs i = splitFin (count (`μ₁ _ R) x) (counts (D (μ₂ ⟪ R ⟫ x)) R xs) i

\end{code}}

