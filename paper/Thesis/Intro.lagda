\AgdaHide{
\begin{code}
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Bool
open import Data.Nat
open import Data.List renaming ( [] to nil ; _∷_ to cons )
open import Data.Fin hiding ( _+_ ; _<_ )
open import Data.Vec hiding ( lookup )
open import Relation.Binary.PropositionalEquality
module _ where
\end{code}}

\chapter{Introduction}\label{ch:intro}

In this dissertation we expand the class of functions that can be
written generically for all types, in a type-safe manner,
within a dependently typed
language~\cite{martinintuitionistic,genericwithdtp}.
Below, we contrast typical
generic programming~\cite{generic1,generic2}
with the approach we describe in this thesis,
which we call \textit{fully generic programming}.

\paragraph{Generic Programming}
Typical generic programming captures the pattern of folding an
algebra through the \textit{inductive} occurrences of an algebraic
datatype.
For example, we could write a generic \AgdaFun{size} function, that
can be applied to \textit{any} datatype.
For any constructor of any datatype, \AgdaFun{size}
returns 1 plus the sum of:
\begin{itemize}
\item The number of non-inductive arguments.
\item The \textit{recursive} sum of the number of inductive arguments.
\end{itemize}
Applying \AgdaFun{size}
to a single-element list containing a pair of
booleans (\texttt{(True, False):[]})
results in 3: the sum of
the \AgdaCon{cons} constructor,
the pair,
and the \AgdaCon{nil} constructor. Because the pair is a non-inductive
argument from the perspective of the list, its size is counted
atomically as 1 (it would be counted as 1 even if it were a value of
an \textit{inductive} datatype other than lists, like a tree,
since it is not inductive with respect to lists).

\paragraph{Fully Generic Programming}
Fully generic programming (\refsec{fullygeneric}) captures the pattern of folding an
algebra through both the \textit{non-inductive} and \textit{inductive}
occurrences of an algebraic datatype.
For example, we could write a fully generic \AgdaFun{count} function that
can also be applied to \textit{any} datatype.
For any constructor of any datatype, \AgdaFun{count}
returns 1 plus the sum of:
\begin{itemize}
\item The \textit{recursive} sum of the number of non-inductive arguments.
\item The \textit{recursive} sum of the number of inductive arguments.
\end{itemize}
Applying \AgdaFun{count}
to a single-element list containing a pair of
booleans (\texttt{(True, False):[]})
results in 5: the sum of
the \AgdaCon{cons} constructor,
the pair (\AgdaCon{,}) constructor,
the two booleans constructors,
and the \AgdaCon{nil} constructor.
Notably, \AgdaFun{count} (unlike \AgdaFun{size}) additionally
recurses through the components of the pair.

In the remainder of this introduction we
provide an overview of dependently typed languages
and motivate our work (\refsec{deplang}),
give an example of fully generic programming over a limited collection
of datatypes (\refsec{fullyeg}),
describe the class of datatypes that we have been able to extend
the fully generic programming approach to (\refsec{algclass}),
and finally cover our thesis statement and contributions
(\refsec{thesis}).


\section{Dependently Typed Languages \& Motivation}\label{sec:deplang}

A standard dependently typed
language~\cite{martin1975intuitionistic,nordstrom1990programming} is
\textit{purely functional} (meaning the absence of side effects),
\textit{total}
(meaning all inductively defined functions
terminate and cover all possible inputs), and has a
type system that captures the notion of \textit{dependency}.
In this thesis we use the dependently typed language
Agda~\cite{lang:agda} for all of our developments.

\subsection{Curry-Howard Isomorphism}

A single term language is used to write programs at the value and type
levels. The combination of
total programming at the type level and a
notion of dependency between types allows any proposition of
intuitionistic logic to be expressed as a type.
A value (or equivalently, a total program) inhabiting a
type encoding a proposition serves as its intuitionistic proof. This
correspondence between values \& types, and proofs \& propositions, is known
as the \textit{Curry-Howard isomorphism}~\cite{curryhoward}.
For example, below we compare universally quantified
propositions to dependent function types, and existentially
propositions to dependent pair types.
$$
\forall x.~ \mrm{P}(x) \approx (\Var{x} : \Var{A}) \arr \Fun{P}~\Var{x}
$$
$$
\exists x.~ \mrm{Q}(x) \approx \Data{Σ}~\Var{A}~(\lambda~\Var{x} \arr \Fun{Q}~\Var{x})
$$

  \AgdaHide{
\begin{code}
module _ {A : Set} where
 private
  postulate
\end{code}}

Using the Curry-Howard isomorphism, we can encode logical
\textit{preconditions} and \textit{postconditions} at the type level.
For example, below
we give the type of a \Fun{lookup} function over lists with a
\textit{precondition} constraining the natural number (\Var{n}) index
to be less than the length of the list (\Var{xs}) being looked
up. This allows an otherwise partial lookup function to be defined
totally by preventing out-of-bounds indexing.

\begin{code}
   lookup : (n : ℕ) (xs : List A) → n < length xs → A
\end{code}

As another example, we give the type of an \Fun{append} function over lists with
a \textit{postcondition} constraining the length of the output list
(\Var{zs}) to be equal to the sum of the lengths of the input lists
(\Var{xs} and \Var{ys}).

\begin{code}
   append : (xs ys : List A) → Σ (List A) (λ zs → length zs ≡ length xs + length ys)
\end{code}

The types of \Fun{append} and \Fun{lookup} correspond to the following
two logical propositions respectively.
$$
\forall n, xs.~ n < \card{xs} \imp \exists x
$$
$$
\forall xs, ys.~ \exists zs.~ \card{zs} = \card{xs} + \card{ys}
$$

\subsection{Indexed Types}

The less-than (\AgdaData{<}) precondition and equality
(\AgdaData{≡}) postcondition in the examples above
are \textit{relations} in the language of logic,
and are called
\textit{indexed types}~\cite{indexed1,indexed2}
in the language of dependent types.
Indexed types are (commonly) types whose arguments are values (rather
than types). For example, less-than (\AgdaData{<})
takes two natural number (\Data{ℕ}) arguments, and
equality (\AgdaData{≡}) takes two values of some type \Var{A}.
Rather than constraining a datatype (like
lists) using relations after-the-fact, we can create
more specific (i.e. \textit{indexed})
variants of datatypes that encode certain
properties before-the-fact.

\AgdaHide{
\begin{code}
module _ {A : Set} where
 private
  postulate
\end{code}}

For example, the type of vectors (\Data{Vec} \Var{A} \Var{n})
is like a length-indexed version of lists. Compared to lists, the type
former of vectors gains an additional natural number parameter (\Var{n})
constraining its length. Because the property of the length of a vector
is encoded at the type level, we can write a variant of \Fun{append}
where calls to \Fun{length} have been replaced by an index.

\begin{code}
   append : (m n : ℕ) (xs : Vec A m) (ys : Vec A n) → Vec A (m + n)
\end{code}

Additionally, the explicit equality proof
(\Data{≡}) postcondition can be dropped in favor of expressing the
postcondition directly in the index position of the output vector.
In other words, the \textit{extrinsic} equality postcondition has been
dropped in favor of an \textit{intrinsic}
property about the codomain of \Fun{append}.

Another example of an indexed type is the type of finite sets
(\Data{Fin} \Var{n}), indexed by a natural number constraining
the size of the finite set. A finite set
is like a subset of the of the natural numbers from 0 to \Var{n} - 1. 
This subset property
(whose maximum value is \Var{n} - 1) is the perfect datatype to act as
an \textit{intrinsic} version of the \textit{extrinsic} less-than
(\Data{<}) precondition of \Fun{lookup}. Hence, we can rewrite an
intrinsic-precondition version of \Fun{lookup} using vectors and finite sets
as follows.

\begin{code}
   lookup : (n : ℕ) (xs : Vec A n) (i : Fin n) → A
\end{code}

\subsection{Motivation}

Programmers of non-dependently typed languages already struggle with the
issue of needing to define logically similar versions of functions
(like \Fun{count}, \Fun{lookup}, \Fun{update}, etc.)
for their various algebraic types
(e.g. natural numbers, lists, binary trees, etc.).
This problem is more pronounced in a dependently typed language, where
programmers also define indexed variants of types
(e.g. finite sets, vectors, balanced binary trees, etc.)
that intrinsically capture preconditions and postconditions.

Rather than punishing programmers for creating new datatypes,
our \textbf{motivation} is to reward them with
\textit{fully generic functions}
(like \Fun{count}, \Fun{lookup}, \Fun{update}, etc.), which are new
mechanisms for \textit{code reuse}.
Fully generic functions are predefined once-and-for-all to work with
any datatype of the language, whether it is defined now or will be
defined in the future.
Programmers defining new types should be able to \textit{apply} fully generic
functions to them, and programmers should also be able to
\textit{define} fully generic functions themselves.

\section{A Taste of Fully Generic Programming}\label{sec:fullyeg}

Ordinary generic programming in dependently typed
languages~\cite{martinintuitionistic,genericwithdtp}
is accomplished using a construction known as a universe
(\refsec{universes}). Rather than explaining how universes work in
detail (which we do in \refsec{universes}) in this introduction,
we develop our dependently typed Agda examples using
universes in parallel with examples in
Haskell~\cite{lang:haskell} using
type classes~\cite{typeclasses1,typeclasses2}.
Later we learn why our analogy with
Haskell type classes
makes sense, as \textit{ad hoc polymorphism} (\refsec{adhoc}) is a
form of generic programming.

Below we first develop the \Fun{size} function using generic
programming (in Haskell and Agda),
and then develop the \Fun{count} function using
\textit{fully} generic programming
(albeit over a fixed and small language,
and also in Haskell and Agda),
both described in the introduction (\refch{intro}).

\subsection{Generic Programming}

Recall (from \refch{intro}) that \Fun{size} returns the sum of all
inductive constructors, inductive arguments, and non-inductive
arguments. Notably, \Fun{size} \textit{only} recurses into
inductive arguments.

\paragraph{Haskell}

In Haskell, we start by defining a type class (\texttt{Size})
for the \texttt{size} function.

\begin{verbatim}
class Size a where
  size :: a -> Int
\end{verbatim}

The \texttt{size} of a boolean is just 1. This is because it has no other
non-inductive or inductive arguments to sum.

\begin{verbatim}
instance Size Bool where
  size b = 1
\end{verbatim}

The \texttt{size} of a pair is 3, which is the sum of the pair constructor (1)
and both of its non-inductive arguments (1 + 1).

\begin{verbatim}
instance Size (a, b) where
  size (a, b) = 3
\end{verbatim}

The \texttt{size} of an empty list is just 1, because it has no arguments. The
\texttt{size} of a ``cons'' is the sum of the ``cons'' constructor (1), its
single non-inductive argument (1), and the \textit{recursive} \texttt{size} of
its single inductive argument.

\begin{verbatim}
instance Size [a] where
  size [] = 1
  size (x : xs) = 2 + size xs
\end{verbatim}

Note that the \texttt{Size} type class is just ad hoc polymorphism by
\textit{overloading} (\refsec{overloading}), as each of its instances
can be defined independently because they only recurse into inductive
arguments.

\paragraph{Agda}

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

In Agda, we start by declaring a new type (\Data{Size}),
which is the syntactic reification of the types we
wish to generically program \Fun{size} for. Unlike the Haskell
version, we must choose the types for which we will provide
``instances'' upfront.

\begin{code}
  data Size : Set₁ where
    `Bool : Size
    `Pair : (A B : Set) → Size
    `List : (A : Set) → Size
\end{code}

Each constructor of \Data{Size} is not a type, but rather an
encoding of a type. Next, we define a function (\Fun{⟦\_⟧}) that
interprets each encoded \Data{Size} type as an actual
Agda type (i.e. a \Data{Set}). 

\begin{code}
  ⟦_⟧ : Size → Set
  ⟦ `Bool ⟧ = Bool
  ⟦ `Pair A B ⟧ = A × B
  ⟦ `List A ⟧ = List A
\end{code}

We can generically define \Fun{size} as a \textit{dependent} function from
a code (\Var{A} : \Data{Size}), to a
value of the encoded type (\Fun{⟦} \Var{A} \Fun{⟧}),
to a number (\Data{ℕ}). We case-analyze the first (\Data{Size}) argument
of \Fun{size} to distinguish each different
``instance''. After that, each second argument and body follows the
same logic as the instances in the Haskell version above.

\begin{code}
  size : (A : Size) → ⟦ A ⟧ → ℕ
  size `Bool b = 1
  size (`Pair A B) (a , b) = 3
  size (`List A) nil = 1
  size (`List A) (cons x xs) = 2 + size (`List A) xs
\end{code}

A significant difference with the Haskell version is that
we explicitly supply the encoded type in recursive calls
(i.e. \Con{`List} \Var{A} in the \Con{cons} case).
\footnote{It is possible to make this an implicit argument so the Agda
  surface language also infers it. However, the argument would still
  be explicit in the underlying core language that the surface
  language elaborates to.
  }

\subsection{Fully Generic Programming}\label{sec:introcount}

Recall (from \refch{intro}) that \Fun{count} returns the sum of all
inductive constructors, non-inductive constructors, inductive
arguments, and non-inductive arguments. Notably, \Fun{count} recurses
into inductive \textit{and} non-inductive arguments.

\paragraph{Haskell}

Again, we start by defining a Haskell type class (\texttt{Count})
for the \texttt{count} function.

\begin{verbatim}
class Count a where
  count :: a -> Int
\end{verbatim}

The \texttt{count} of a boolean is still 1, because it has no
arguments.

\begin{verbatim}
instance Size Bool where
  size b = 1
\end{verbatim}

The \texttt{count} of a pair is the sum of the pair constructor (1),
and the \textit{recursive} \texttt{count} of
both of its non-inductive arguments.
Notably, \texttt{count} (unlike \texttt{size})
recurses into its non-inductive arguments.

\begin{verbatim}
instance (Count a, Count b) => Count (a, b) where
  count (a, b) = 1 + count a + count b
\end{verbatim}

The \texttt{count} of an empty list is still 1. The
\texttt{count} of a ``cons'' is the sum of the ``cons'' constructor (1),
the \textit{recursive} \texttt{count} of its single non-inductive
argument, and the \textit{recursive} \texttt{count} of
its single inductive argument.
Notably, \texttt{count} (unlike \texttt{size})
recurses into its non-inductive argument.

\begin{verbatim}
instance (Count a) => Count [a] where
  count [] = 1
  count (x : xs) = 1 + count x + count xs
\end{verbatim}

The \texttt{Count} instances for pairs and lists are able to recurse
into their non-inductive arguments because they have type class
premises
(e.g. the left of the arrow in
\texttt{(Count a) => Count [a]} in the list instance)
for their type parameters. This allows instances of one type
to recurse into instances of other types, and is called ad hoc
polymorphism by \textit{coercion} (\refsec{coercion}). The etymology of
the name is the idea that \texttt{count} for lists can be defined by
``coercing'' the meaning of \texttt{count} for the parameterized type
to the type of lists.

\paragraph{Agda}

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

In Agda, we declare a new type (\Data{Count}),
reifying the types over which we will
generically program \Fun{count}.
Unlike \Data{Size}, \Data{Count} is an \textit{inductive} type, as
the arguments to \Con{`Pair} and \Con{`List} are inductive
(i.e. the \Var{A} and \Var{B} arguments have type \Data{Count} below,
but they have type \Data{Set} in the \Data{Size} datatype).

\begin{code}
  data Count : Set where
    `Bool : Count
    `Pair : (A B : Count) → Count
    `List : (A : Count) → Count
\end{code}

The types encoded by \Data{Count} are interpreted
(by the \Fun{⟦\_⟧} function) as actual Agda
types. The \Fun{⟦\_⟧} function interprets the \textit{inductive}
arguments of \Con{`Pair} and \Con{`List}
(representing datatype parameters) \textit{recursively}.

\begin{code}
  ⟦_⟧ : Count → Set
  ⟦ `Bool ⟧ = Bool
  ⟦ `Pair A B ⟧ = ⟦ A ⟧ × ⟦ B ⟧
  ⟦ `List A ⟧ = List ⟦ A ⟧
\end{code}

In Haskell, the \texttt{Count} instances for pairs and lists
have \texttt{Count} type class premises for their type
parameters.
This allows \texttt{count} to recurse into non-inductive arguments of
the parameterized types.
In Agda, \Fun{count} can recurse into non-inductive
arguments (in addition to the inductive arguments)
because its parameterized types are
encoded inductively in \Data{Count}.

\begin{code}
  count : (A : Count) → ⟦ A ⟧ → ℕ
  count `Bool b = 1
  count (`Pair A B) (a , b) = 1 + count A a + count B b
  count (`List A) nil = 1
  count (`List A) (cons x xs) = 1 + count A x + count (`List A) xs
\end{code}

The logic of \Fun{count} closely follows that of the \texttt{count}
instances, except encoded types are explicitly supplied in recursive
calls. Significantly, \Fun{count} has access to \Data{Count} type
encodings (\Var{A} and \Var{B})
in the pair (\Con{,}) and \Con{cons} cases, and these type encodings
are supplied to recursive calls of non-inductive arguments
(\Var{a}, \Var{b}, and \Var{x}).
Finally, \Fun{count} still recurses into the inductive argument
\Var{xs} in the \Con{cons} case using the encoded type
\Con{`List} \Var{A}.


\subsection{Universes}\label{sec:naivegfun}

%% \Data{Count} is \textit{inductively defined} (\refsec{indu}) and
%% \textit{closed} (\refsec{closedu}).

In Agda, generic programming (like the \Fun{count} function) is
accomplished using a \textit{universe} (\refsec{universes}). A
universe is the combination of a type of
\textit{codes} for types
(e.g. \Data{Count}) and a
\textit{meaning}
function (e.g. \Fun{⟦\_⟧})
mapping codes to actual types. Generic functions (over all types of
the universe) are dependent function parameterized
over all type codes (\Data{Code} below)
and the meaning (\Fun{Meaning} below)
of the particular code
supplied.
$$
(\AgdaVar{c} : \AgdaData{Code})~
(\Var{m} : \AgdaFun{Meaning}~\AgdaVar{c})
→ ...
$$

\paragraph{Fixed Types Universe}

We have a seen how to perform a limited version of
\textit{fully generic programming}, in
which recursion into both \textit{non-inductive} and
\textit{inductive} arguments is possible, in the \Fun{count} example
using the \Data{Count} universe.
The problem with the \Data{Count} universe is that it is
\textit{fixed} to a particular collection of types, chosen ahead of
time.

We can add more types (as in \refsec{closedu})
to this universe (like natural numbers,
vectors, finite sets, dependent pairs, dependent functions, etc),
naming the new type of codes \Data{Type}, until
it contains enough types to model a dependently typed language with a
primitive collection of built-in types. Fully generic programming over
this universe then models fully generic programming over the entire
language modeled by the universe:
$$
(\Var{A} : \Data{Type})~
(\Var{a} : \AgdaFun{⟦}~\AgdaVar{A}~\AgdaFun{⟧})
→ ...
$$

However, most modern dependently typed language allow users to declare
new algebraic datatypes. The \Data{Type} universe does not model a
language with datatype declarations, as users can only work with the
built-in types that have been \textit{fixed} ahead of time.

\paragraph{Extensible Algebraic Types Universe}

Alternatively, we may define a universe that models algebraic
datatypes (as in \refsec{depalg}).
We call the type of codes for this universe
\Data{Desc}, as they \textit{describe} algebraic datatype declarations.
The meaning function for this universe, named \Data{μ}, interprets a
declaration as the declared type.
\footnote{As we see in the next section, another way to think about
  \Data{Desc} is a reification of pattern functors from initial
  algebra semantics, whose least fixed point is calculated by
  \Data{μ}.
  }
The \Data{Desc} universe models an \textit{extensible} collection of
algebraic datatypes.
Generic programming over this universe allows users to write functions
that can be applied to any algebraic datatype a user might declare
(whether the type is already declared now or will be declared in the future):
$$
(\Var{D} : \Data{Desc})~
(\Var{x} : \AgdaData{μ}~\AgdaVar{D})
→ ...
$$

Actually, dependently typed languages can only contain the
\textit{strictly positive} (\refsec{inft}) subset of algebraic
datatypes (this restriction keeps the language total, hence consistent
as a logic under the Curry-Howard isomorphism).
A consequence of defining
\Data{Desc} as a strictly positive datatype is that generic
programming over it corresponds to
\textit{ordinary generic programming}
(like the \Fun{size} function),
in which recursion is restricted to \textit{inductive} arguments.

\paragraph{Fixed Types \textit{Closed Under} Algebraic Extension Universe}

A primary contribution of this thesis is defining a universe that
combines the fixed collection of built-in types universe
(\Data{Type}) with the extensible collection of algebraic datatypes
universe (\Data{Desc}), in a way that supports
\textit{fully generic programming}
(while remaining consistent under the Curry-Howard isomorphism).

One important property of what makes fully generic programming possible
in \Data{Count} is that the arguments to its codes
(i.e. the arguments to \Con{`Pair} and \Con{`List}) are
\textit{inductive}. This makes \Data{Count} a universe of booleans
\textit{closed under} pair formation and list formation. Closure
properties are an important defining feature of a universe.

The key to defining our combined universe it to make the
\Data{Type} universe not only closed under expected types
(like dependent pairs and dependent functions),
but also closed under
\textit{algebraic datatype formation} (\Data{μ}) from
datatype declarations (\Data{Desc}).
The details of how to make this work are beyond the scope of this
introduction (see \refsec{closed} for the full construction). However,
the central idea has to do with
defining the \Data{Type} and \Data{Desc} universes \textit{mutually}.
Thus, fully generic programming over this mutual universe
corresponds to writing \textit{mutually} dependent functions over the
following type signatures:
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

Essentially, in our mutual universe \Data{Type}
is closed under \Data{Type} formers (like \Con{`μ})
that can have \Data{Desc} arguments,
and \Data{Desc}
is closed under \Data{Desc} formers that can have \Data{Type}
arguments.
The consequence of our \textit{closed} universe is that it
models a dependently typed language supporting
datatype declarations \textit{and} fully generic programming.

\subsection{Fully Generic versus Deriving}

Finally, we would like to make an analogy:
Having access to fully generic functions (e.g \Fun{count}) defined for
all possible types is like \texttt{deriving} a type class instance for a
datatype in Haskell. In both cases, users get to declare a new
datatype and have access to functions operating over it
(i.e. fully generic \Fun{count} or derived \texttt{count}) for free.

The big difference is that users of a closed but extensible
dependently typed language (like a variant of Agda)
may define fully generic functions
themselves. Furthermore, because these are ordinary dependent
functions defined within the language they are ensured to be type-safe.
In contrast, users of
a non-dependently typed language like Haskell must rely on compiler
writers to provide them with derivable functions.

\section{Class of Supported Datatypes}\label{sec:algclass}

Previously (\refsec{fullyeg}) we introduced the idea of
\textit{fully generic programming} over a mutually defined
universe, encoding a fixed
collection of primitive types \textit{and} an extensible collection of
algebraic datatypes.
This section addresses the following question: What properties of
algebraic datatypes should we support to adequately describe all
possible types definable in a dependently typed language like Agda?

We explain why we choose
\textit{inductive-recursive} types, instead of indexed types,
as the answer to this question.
Non-expert readers may wish to skim this section and come back to it
after finishing \parttitle{prelude}.

\subsection{Dependent Algebraic Types}

We certainly want to support algebraic
datatypes with \textit{dependencies} between their
arguments. In a non-dependent language like Haskell the types of all
arguments to constructors of an algebraic datatype can be defined
independently. In Agda, the \textit{types}
of subsequent constructor arguments can depend on the
\textit{values} of previous constructor arguments.
There are 2 common generic encodings (i.e. semantic models)
of dependent algebraic datatypes:
\begin{itemize}
\item{\textbf{Containers} (\refsec{wtypes})} These are data structures that represent
  types using an analogy of \textit{shapes} (capturing inductive
  structure) and \textit{positions} (capturing contained values).
  The least fixed points of containers~\cite{containers}
  are \textit{well-orderings}~\cite{wtypes},
  or \Data{W} types.
\item{\textbf{Dependent Polynomials} (\refsec{depalg})} These are
  \textit{pattern functors}~\cite{deppolyfunc}
  from initial algebra semantics, whose
  least fixed point is returned by the \Data{μ} operator. The
  \Data{Desc} type of \refsec{fullyeg} is a syntactic reification of
  dependent polynomial pattern functors,
  whose meaning function is
  \Data{μ} when considered as a universe of dependent algebraic types.
\end{itemize}

A universe closed under \Data{W} types, supporting fully generic
programming, is trivial to define (\refsec{wuni}). Unfortunately,
while \Data{W} types adequately encode algebraic types in
Extensional Type Theory (as implemented by
NuPRL~\cite{lang:nuprl}),
they inadequately~\cite{winad} (\refsec{inad}) encode
first-order algebraic types in
Intensional Type Theory (as implemented by Agda~\cite{lang:agda}).
For this reason, we choose \textbf{dependent polynomials} to model
dependent algebraic types.

\subsection{Indexing versus Induction-Recursion}

Besides supporting algebraic types with dependencies between
arguments, Agda also supports algebraic types capturing
\textit{intrinsic} correctness properties.
There are 2 main special kinds of algebraic types used to
capture intrinsic correctness properties:
\begin{itemize}
\item{\textbf{Indexed Types} (\refsec{indx})}
  These are collections of algebraic types, indexed
  by some type \AgdaVar{I}, such that each type in the collection may
  vary for any particular value of \AgdaVar{I}.
  For example, \Data{Vec}tors of \Var{A} values are indexed by the natural
  numbers and map to lists whose lengths are constrained to equal the
  natural number index.
\item{\textbf{Inductive-Recursive Types} (\refsec{irtypes})} These are
  algebraic datatypes mutually defined with a \textit{decoding function}
  whose domain is the algebraic type and codomain is some type
  \AgdaVar{O}. For example,
  \Data{Arith}metic expressions (\refsec{irtypes}) of
  ``Big Pi'' formulae, mutually defined with an \Fun{eval}uation
  function returning the number they encode. The upper bound of
  ``Big Pi'' arithmetic expressions is calculated using the mutually
  defined evaluation function. 
\end{itemize}

Somewhat surprisingly,
indexed types~\cite{indexed1,indexed2}
and
inductive-recursive types~\cite{inductionrecursion1,inductionrecursion2}
define isomorphic classes of datatypes~\cite{smallir}. That is, any indexed type
(like \Data{Vec}) can be defined as an inductive-recursive type, and
any inductive-recursive type (like \Data{Arith}) can be defined as an
indexed type.

Thus, picking either indexed or inductive-recursive types is adequate
to capture all of the algebraic types we would like to encode in our
closed universe. We choose \textbf{inductive-recursive} types because
there is little research on using them to even do ordinary generic
programming.

\subsection{Smallness versus Largeness}

There are 2 more significant reasons why picking
induction-recursion to showcase generic programming is important. The
first is merely an issue of encoding, but the second emphasizes that
the isomorphism between indexed and inductive-recursive does not scale
to ``large'' cases, defined below:
\begin{itemize}
\item{\textbf{Intensionality}}
  Even though indexed and inductive-recursive types are isomorphic,
  encoding ``naturally'' inductive-recursive types
  (like \Data{Arith}) as indexed types means reasoning about the
  low-level encoding rather than the high-level intended type
  definition. Similarly, writing generic functions over
  inductive-recursive types produces more ``natural'' results when
  applied to ``naturally'' inductive-recursive types, as opposed to
  encoded indexed types.
\item{\textbf{Largeness}}
  In this thesis we only cover \textit{small} closed universe fully
  generic programming, meaning the codomain of the inductive-recursive
  decoding function is a type (like the natural numbers).
  In contrast, \textit{large} inductive-recursive types may have
  kinds (\Data{Set}) as the codomain of their decoding functions. The
  isomorphism between indexed and inductive-recursive types no longer
  applies in the large case. Therefore, fully
  generic programming over small inductive-recursive types may serve
  as a guide for how to do it in the large case (where one cannot
  simply use indexed types and apply the isomorphism).
\end{itemize}

Our arguments (the intensionality of functions and the
lack of an isomorphism in the large case) could also be used to
justify choosing indexed types (where we consider ``naturally''
indexed types and large type indices). Once again, we choose
inductive-recursive because they are less studied in the generic
programming literature.

Finally, because the isomorphism fails in the large case, the ideal
choice would be to use
\textbf{indexed inductive-recursive}~\cite{indexedinductionrecursion}
algebraic types. These are a 3rd option for expressing intensional
correctness properties of datatypes, where both indexing and
induction-recursion are expressed naturally.
\footnote{Interestingly, even indexed inductive-recursive types are
  isomorphic to indexed types and inductive-recursive types in the
  small case~\cite{smallir}.
}
While it is \textit{not technically challenging} to extend
our work on fully generic programming over closed universes to indexed
inductive-recursive types, we do not do this for \textit{pedagogical}
reasons. The necessary background material to explain this combined
approach, and the resulting complexity it introduces in generic
functions and examples, would obscure our lessons on how
to define closed universes and perform fully generic programming.

\section{Thesis}\label{sec:thesis}

Now we cover our thesis statement, contributions, and outline the
remainder of the dissertation.

\subsection{Thesis Statement}

\textbf{Fully generic programming},
supporting functions defined by recursion into
all non-inductive and inductive constructor arguments of all types in
the universe, is possible over a universe that:
\begin{itemize}
\item{(\refsec{closedu})} Models a
  \textbf{dependently typed language}
  (or type theory, supporting the Curry-Howard isomorphism)
  with datatype declarations.
\item{(\refsec{iralg})} Adequately (in intensional type theory)
  models \textbf{small inductive-recursive algebraic types}
  via initial algebra semantics
  (in contrast to the inadequate model of first-order types
  in the universe of \refsec{closedw}).

\item{(\refsec{fullygeneric})} Supports the
  elimination of all values by:
  \begin{itemize}
    \item{(\refsec{indu})} being \textbf{inductively defined},
      allowing types to be closed under other types.
    \item{(\refsec{closedu})} being \textbf{closed}, by not 
      containing values defined using \Data{Set} or \Data{Level}.
    \item{(\refsec{autonomous})} being \textbf{autonomous}, by only
      containing values whose types are in the universe.
    \item{(\refsec{concrete})} being \textbf{concrete}, by only
      containing types that have some elimination form.
  \end{itemize}

\end{itemize}

\subsection{Contributions}

We make the following 3 \textit{primary contributions} to the field of generic
programming using dependently typed languages:
\begin{enumerate}

\item{\textbf{Defining} (\refch{closed})}
  a \textit{closed universe}, as an adequate model of a
  dependently typed language with datatype declarations for
  inductive-recursive types, supporting fully generic programming.

\item{\textbf{Examples} (\refch{fullyg})}
  of writing \textit{fully generic functions} over all
  \textit{values} of our universe, including \Fun{count}, \Fun{lookup},
  \Fun{update}, and \textit{marshalling} (\Fun{ast}) to an abstract
  syntax tree.

\item{\textbf{Extending} (\refch{hier})}
  our closed universe to a
  \textit{closed hierarchy of universes}, supporting fully generic
  functions (like an updated version of \Fun{ast})
  over all \textit{types} in the universe hierarchy
  (in addition to values), via fully generic programming over all
  universe \textit{levels}.

\end{enumerate}

\subsection{Outline}

The dissertation is broken up into 4 parts,
the \textbf{Prelude},
a part on \textbf{Open Type Theory},
a part on \textbf{Closed Type Theory},
and the \textbf{Postlude}:

\subsubsection{\parttitle{prelude}}

The prelude reviews background information on dependently typed
programming, and serves
as a mini-version of our dissertation, in a simplified but
unfortunately inadequate setting.

\paragraph{\chaptitle{intro}}
This chapter concludes the introduction.
We already reviewed dependently typed languages, and how code reuse
serves as our motivation (\refsec{deplang}). We also demonstrated what
fully generic programming looks like in a limiting setting, and
compared how it works in Agda with how it works in Haskell
(\refsec{fullyeg}). Finally, we explained why we chose
inductive-recursive types as the class of algebraic types we wish to
write fully generic functions over (\refsec{algclass}).

\paragraph{\chaptitle{univ}}
We review the concept of types (\refsec{types}) and universes
(\refsec{universes}) in type theory. In particular, we classify both
types and universes according to a detailed account of various
properties they can have.

\paragraph{\chaptitle{generic}}
We clarify what we mean by \textit{generic programming}
(i.e. programming over many types, using various forms of
polymorphism~\cite{paramadhocpoly}),
because the meaning of this term is overloaded.
We compare and contrast generic
programming as parametric polymorphism (\refsec{parapoly}) and
ad hoc polymorphism (\refsec{adhoc}). Additionally, we introduce the
idea of \textit{concreteness} (\refsec{abscon}) to help clarify what
we mean by \textit{fully} generic programming. Programming
total functions in type theory can be non-trivial, especially as the
class of types we program over expands during generic programming, so
review techniques to make total programming possible (\refsec{totality}).

\paragraph{\chaptitle{closedtt}}
This chapter serves as a mini-version of our thesis, giving examples
of closed type theories (i.e. those that do not contain \Data{Set})
supporting fully generic programming.
We present (\refsec{closedvecu})
the closed type theory of \textit{Closed Vector Types}, modeling a
language with a built-in collection of types related to vector
operations. We show how to write a fully generic \Fun{sum} function
over the language of \textit{Closed Vector Types}.
Then we present (\refsec{closedw}) the closed type theory of
\textit{Closed Well-Order Types}, modeling a language with
algebraic datatype declarations. Unfortunately, while this closed
universe model is easy to define and supports fully generic
programming, the \Data{W} type it
uses to model algebraic types is inadequate for our purposes.

\subsubsection{\parttitle{open}}

In this part we focus on modeling algebraic datatypes in
\textit{open type theory}, whose collection of types grows as more
types are declared. While algebraic types defined using \Data{W} are
inadequate (in open type theory and closed type theory), types defined
using \textit{initial algebra semantics} are not.
This part explains how to model initial algebra semantics in type
theory (by defining the \Data{Desc} and \Data{μ} types),
which is much more involved than defining the \Data{W} type.

\paragraph{\chaptitle{open}}
In this chapter we progress through a series of initial algebra
semantics for incrementally more expressive classes of datatypes,
starting with non-dependent algebraic types and ending with
inductive-recursive types.
We motivate the (formal) type theory models with
their category theory equivalents. We also give examples of modeling
values, not just types, using initial algebra semantics.

\subsubsection{\parttitle{closed}}

In this part we switch back to closed type theory, returning back to
the setting from which we diverged in \refsec{wuni},
but this time using an adequate equivalent of the language of
\textit{Closed Well-Order Types}. We also go one step further,
defining a closed \textit{hierarchy} of closed types.

\paragraph{\chaptitle{closed}}
In this chapter we define the closed type theory
of \textit{Closed Inductive-Recursive Types}. This adapts the previous
initial algebra semantics from an open type theory setting to a closed
type theory setting. We define the
\textit{Closed Inductive-Recursive Types} in Agda, serving as a
formal model of a closed dependently typed language supporting
datatype declarations. 

\paragraph{\chaptitle{fullyg}}
In this chapter we provide examples of writing fully generic functions over
\textit{Closed Inductive-Recursive Types}. These functions can be
applied to values of any type in our model, can recurse into
non-inductive and inductive arguments, and can eliminate any value in
our model. Significantly, our generic functions are examples of how to
deal with dependencies among \textit{inductive} arguments, as such
dependencies only exist for inductive-recursive types.

\paragraph{\chaptitle{hier}}
Up to this point we have worked with a closed type theory modeling the
first universe of a hierarchy, which contains values but not types.
In this chapter we show how to extend a closed type theory to a
hierarchy of universes, which contains types (in addition to values)
at every level of the hierarchy beyond the first.
The chapter reviews how to model a hierarchy of
\textit{Closed Well-Order Types}, and then defines a model of the
hierarchy of \textit{Closed Inductive-Recursive Types}. We
highlight the subtleties necessary to adequately define a hierarchy
containing algebraic types modeled using initial algebra semantics.

In this chapter we also show how to extend \textit{fully generic functions}
to also be \textit{universe-level generic}. We call such functions
\textit{leveled fully generic functions}, and they can be applied to
any type at any level of the universe hierarchy . Importantly, leveled
fully generic programming is possible because our universe hierarchy
model is closed (i.e. the hierarchy still does not contain \Data{Set},
but additionally does not contain \Data{Level}).

\subsubsection{\parttitle{postlude}}

Finally, we address
\textbf{\chaptitle{related}},
\textbf{\chaptitle{future}},
and state our \textbf{\chaptitle{conclusion}}.

