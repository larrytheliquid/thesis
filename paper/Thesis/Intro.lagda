AgdaHide{
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

\section{Dependently Typed Languages \& Motivation}\label{sec:deplang}

A standard dependently typed language is
\textit{purely functional} (meaning the absence of side effects),
\textit{total}
(meaning all inductively defined functions
terminate and cover all possible inputs), and has a
type system that captures the notion of \textit{dependency}.
In this thesis we use the dependently typed language Agda~\cite{TODO}
for all of our developments.

\subsection{Curry-Howard Isomorphism}

A single term language is used to write programs at the value and type
levels. The combination of total programming at the type level and a
notion of dependency betweeen types allows any proposition of
intuitionistic logic to be expressed as a type.
A value (or equivalently, a total program) inhabiting a
type encoding a proposition serves as its intuitionistic proof. This
correspondence between values \& types and proofs \& propositions is known
as the \textit{Curry-Howard Isomorphism}~\cite{TODO}.
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

Using the Curry-Howard Isomorphism, we can encode logical
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
and are called \textit{indexed types} in the language of dependent
types.
Rather than constraining a datatype like
lists using relations after-the-fact, we can create
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
constraining its length. Because the property of of lengths of vectors
is encoded at the type level, we can write a variant of \Fun{append}
where calls to \Fun{length} have been replaced by an index.

\begin{code}
   append : (m n : ℕ) (xs : Vec A m) (ys : Vec A n) → Vec A (m + n)
\end{code}

Additionally, the explicit equality proof
(\Data{≡}) postcondition can be dropped in favor of expressing the
postcondition directly in the index position of the output vector.
In other words, the \textit{extrinsic} equality postcondition has been
dropped in favor of an \textit{intrinsic}~\cite{TODO}
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
to intrinsically capture preconditions and postconditions.

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

Ordinary generic programming in dependently typed languages is
accomplished using a construction known as a universe
(\refsec{universes}). Rather than explaining how universes work in
detail (which we do in \refsec{universes}) in this introduction,
we develop our dependently typed Agda examples using
universes in parallel with examples in Haskell using
type classes~\ref{TODO}. Later we learn why our analogy with
Haskell~\cite{TODO} type classes~\cite{TODO}
makes sense, as \textit{ad hoc polymorphism} (\refsec{adhoc}) is a
form of generic programming.

Below we first develop the \Fun{size} function using generic
programming, and then develop the \Fun{count} function using
\textit{fully} generic programming
(albeit over a fixed and small language),
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

\subsection{Fully Generic Programming}

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
the arguments to \Con{`Pair} and \Con{`List} are inductive.

\begin{code}
  data Count : Set where
    `Bool : Count
    `Pair : (A B : Count) → Count
    `List : (A : Count) → Count
\end{code}

The types encoded by \Data{Count} can are interpreted
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


\subsection{Universes}

%% \Data{Count} is \textit{inductively defined} (\refsec{indu}) and
%% \textit{closed} (\refsec{closedu}).

In Agda, generic programming (like the \Fun{count} function) is
accomplished using a \textit{universe} (\refsec{universes}). A
universe is the combination of a type of \textit{codes} for types
(e.g. \Data{Count}) and a \textit{meaning} function (e.g. \Fun{⟦\_⟧})
mapping codes to actual types. Generic functions (over all types of
the universe) are dependent function parameterized
over all type codes and the meaning of the particular code
supplied.
$$
(\AgdaVar{x} : \AgdaData{Code}) → \AgdaFun{Meaning}~\AgdaVar{x} → ...
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
that can be applied to any algebraic datatype a user might declare:
$$
(\Var{D} : \Data{Desc})~
(\Var{x} : \AgdaData{μ}~\AgdaVar{D})
→ ...
$$

Actually, dependently typed languages can only contain the
\textit{strictly positive} (\refsec{inft}) subset of algebraic
datatypes (this restriction keeps the language total, hence consistent
as a logic under the Curry-Howard Isomorphism).
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
\textit{fully generic programming}.

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
introduction (see \refsec{TODO} for the full construction). However,
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

\section{Class of Supported Datatypes}\label{sec:algclass}

\subsection{Algebraic Types}

\subsection{Type Families}

\section{Thesis \& Contributions}\label{sec:thesis}



