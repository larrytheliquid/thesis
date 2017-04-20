\AgdaHide{
\begin{code}
module _ where
open import Function
open import Appendix
open import Data.Nat hiding ( zero ; suc ; _+_ )
open Prim
open Alg
open ClosedHier
open import HierIR
open Nat
\end{code}}

\section{Leveled Fully Generic Functions}\label{sec:lgcount}

\refchap{fullyg} demonstrates writing fully generic functions
(like \Fun{count}, \Fun{lookup} and \Fun{ast}) over all
\textit{values} of the
\textit{Closed Inductive-Recursive Types}
universe (of \refsec{closed}). In this section, we show how to write
\textit{leveled} fully generic functions, or fully generic functions
at any level of the
\textit{Closed Hierarchy of Inductive-Recursive Universes}
(of \refsec{hierir}).

In \refsec{count0}, we patch fully generic \Fun{count}
(of \refsec{count}), converting it to work in level 0 of our hierarchy,
over all \textit{values} of types.
Subsequently, in \refsec{count1}, we define fully generic \Fun{Count}
in level 1 of our hierarchy,
over all \textit{types} of kinds.
As we shall see, the \Fun{Count} function at level 1 must be defined
in terms of the \Fun{count} function at level 0,
because the values of level 0 are lifted to the type level 1,
which is expected because our universes form a \textit{hierarchy}.

We only patch \Fun{count} to work at level 0 (and extend it
to work at level 1) but other fully generic functions
(like \Fun{lookup} and \Fun{ast})
can be similarly defined as \textit{leveled} fully generic functions.
Leveling a function primarily involves 2 things:
\begin{enumerate}
\item The type of the fully generic function must be
  \textit{internalized} as a kind (of the next universe level).
\item Additional cases must be handled, for the closed kinds
  \Con{`Set} and \Con{`Desc}, and their associated
  lifting functions (\Con{`⟦\_⟧}, \Con{`⟦\_⟧₁}, and \Con{`μ₁'}).
\end{enumerate}

\AgdaHide{
\begin{code}
module Nat0 where
\end{code}}

\begin{figure}[ht]
\centering
\begin{code}
  one : ⟦ 0 ∣ `ℕ ⟧
  one = suc zero

  two : ⟦ 0 ∣ `ℕ ⟧
  two = suc one

  _+_ : ⟦ 0 ∣ `ℕ `→ `ℕ `→ `ℕ ⟧
  init (true , tt) + m = m
  init (false , n , tt) + m = n tt + m
\end{code}
\AgdaHide{
\begin{code}
  infixl 6 _+_
\end{code}}
\caption{Closed natural number definitions in universe level 0.}
\label{fig:nat0}
\end{figure}

\subsection{Counting in Universe Zero}\label{sec:count0}

Step 1 of patching
\Fun{count} (over all values in \refsec{count}) and
\Fun{counts} (over all algebraic arguments in \refsec{counts}),
to be defined in level 0 of our hierarchy,
is \textit{internalizing} their signatures, as follows.

\AgdaHide{
\begin{code}
module _ where
 private
  postulate
\end{code}}

\begin{code}
    count : ⟦ 1 ∣ `Π `Set (λ A → `⟦ A ⟧ `→ `⟦ `ℕ ⟧) ⟧
    counts : ⟦ 1 ∣ `Π `Set (λ O → `Π (`Desc O) (λ D → `Π (`Desc O) (λ R →
      `⟦ D ⟧₁ R `→ `⟦ `ℕ ⟧))) ⟧
\end{code}

\begin{figure}[ht]
\centering
\AgdaHide{
\begin{code}
module Count0 where
  open Nat0
  mutual
\end{code}}
\begin{code}
    count : ⟦ 1 ∣ `Π `Set (λ A → `⟦ A ⟧ `→ `⟦ `ℕ ⟧) ⟧
    count (`Σ A B) (a , b) = one + count A a + count (B a) b
    count (`μ₁ O D) (init xs) = one + counts O D D xs
    count `Set ()
    count (`Desc ()) ()
    count (`⟦ () ⟧) a
    count (`⟦ () ⟧₁ ()) xs
    count (`μ₁' () ()) x
    count A a = one
    
    counts : ⟦ 1 ∣ `Π `Set (λ O → `Π (`Desc O) (λ D → `Π (`Desc O) (λ R →
      `⟦ D ⟧₁ R `→ `⟦ `ℕ ⟧))) ⟧
    counts O (`σ A D) R (a , xs) = count A a + counts O (D a) R xs
    counts O (`δ `⊤ D) R (f , xs) = count (`μ₁ O R) (f tt) +
      counts O (D (`μ₂ R ∘ f)) R xs
    counts O (`δ A D) R (f , xs) = one + counts O (D (`μ₂ R ∘ f)) R xs
    counts O (`ι o) R tt = one
\end{code}
\caption{Fully generic counting of values (\Fun{count})
  and algebraic arguments (\Fun{counts})
  in universe level 0.}
\label{fig:count0}
\end{figure}

Because \Fun{count} and \Fun{counts} quantify over kinds
(\Con{`Set} and \Con{`Desc}, respectively), they have internalized
\textit{kind} signatures (universe level 1). However, the \Var{A}
argument of \Fun{count}, and the returned natural number (\Fun{`ℕ}) codomain are
\textit{types}, because they are lifted using \Con{`⟦\_⟧}. Similarly,
\Con{`⟦\_⟧₁} is used to lift the last argument of \Fun{counts} from
the type level to the kind level.
Hence, \Fun{count} and \Fun{counts} operate on \textit{values},
classified by \textit{types}, albeit lifted to the kind level in the
signatures of \Fun{count} and \Fun{counts}.

Both \Fun{count} and \Fun{counts} now return \textit{internalized}
natural numbers (\Fun{`ℕ}), hence we must patch the body
of \Fun{count} from \refsec{count} and \Fun{counts} from
\refsec{counts}, according to the table below. The left column of the
table contains values \textit{external} to our closed hierarchical
type theory, and the right side contains their \textit{internal}
equivalents.\footnote{
  We use the closed definition of natural numbers at level
  0 from \refsec{hierireg}, and the closed definitions of
  \Fun{one} and \Fun{+}, appearing in the right column of the table,
  are defined in \reffig{nat0}.
  }

\begin{center}
 \begin{tabular}{||c | c ||} 
 \hline
 Closed Types Universe &
 Universe 0 in Hierarchy \\ [0.5ex] 
 \hline\hline

 \Num{1} : \Data{ℕ} &
 \Fun{one} : \Fun{⟦ \Num{0} ∣ `ℕ ⟧} \\ 
 \hline

 \Fun{+} : \Data{ℕ} → \Data{ℕ} → \Data{ℕ} &
 \Fun{+} : \Fun{⟦ \Num{0} ∣ `ℕ `→ `ℕ `→ `ℕ ⟧} \\ 
 \hline

 \end{tabular}
\end{center}

The definitions of \Fun{count} and \Fun{counts} in universe level 0,
which are the result of patching their equivalents in
\refsec{count} and \refsec{counts}, are in \reffig{count0}.
Recall that step 2 of the patching process is to handle cases for the
closed kinds (\Con{`Set} and \Con{`Desc}), and their lifting
functions (\Con{`⟦\_⟧}, \Con{`⟦\_⟧₁}, and \Con{`μ₁'}), in
the definition of \Fun{count}.

In \reffig{count0}, if the first argument of \Fun{count} is
\Con{`Set}, then the second argument is its meaning (or
lifting). However, at universe level 0 the meaning of \Con{`Set}
is \Data{⊥}, so the second argument is empty parenthess,
which is Agda syntax for matching against an uninhabited argument.
This makes sense intuitively, because \Fun{count} at level 0 is
defined over \textit{values}, hence we do not need to define a case
for counting \textit{types} (inhabitants of \Con{`Set}).
The same is true for the \Con{`Desc} case. Finally, each lifting
function constructor (\Con{`⟦\_⟧}, \Con{`⟦\_⟧₁}, and \Con{`μ₁'}) takes a
closed type or description as one of its arguments. Because we know
closed types and descriptions are not inhabited at universe level 0,
we also do not need to define cases for the lifting functions.

\subsection{Counting in Universe One}\label{sec:count1}

\begin{figure}[ht]
\centering
\AgdaHide{
\begin{code}
module Count1 where
  open Nat0
  open Count0
  mutual
\end{code}}
\begin{code}
    Count : ⟦ 2 ∣ `Π `Set (λ A → `⟦ A ⟧ `→ `⟦ `⟦ `ℕ ⟧ ⟧) ⟧
    Count (`Σ A B) (a , b) = one + Count A a + Count (B a) b
    Count (`μ₁ O D) (init xs) = one + Counts O D D xs
    Count `Set A = CountSet A
    Count (`Desc O) D = CountDesc O D
    Count (`⟦ A ⟧) a = count A a
    Count (`⟦ D ⟧₁ R) xs = counts _ D R xs
    Count (`μ₁' O D) (init xs) = one + counts O D D xs
    Count A a = one

    Counts : ⟦ 2 ∣ `Π `Set (λ O → `Π (`Desc O) (λ D → `Π (`Desc O) (λ R →
      `⟦ D ⟧₁ R `→ `⟦ `⟦ `ℕ ⟧ ⟧))) ⟧
    Counts O (`σ A D) R (a , xs) = Count A a + Counts O (D a) R xs
    Counts O (`δ `⊤ D) R (f , xs) = Count (`μ₁ O R) (f tt) +
      Counts O (D (`μ₂ R ∘ f)) R xs
    Counts O (`δ A D) R (f , xs) = one + Counts O (D (`μ₂ R ∘ f)) R xs
    Counts O (`ι o) R tt = one
\end{code}
\caption{Fully generic counting of values (\Fun{Count})
  and algebraic arguments (\Fun{Counts})
  in universe level 1.}
\label{fig:count1}
\end{figure}

\begin{figure}[ht]
\centering
\begin{code}
    CountSet : ⟦ 1 ∣ `Set  `→ `⟦ `ℕ ⟧ ⟧
    CountSet (`Σ A B) = two + CountSet A
    CountSet (`Π A B) = two + CountSet A
    CountSet (`Id A x y) = one + CountSet A + count A x + count A y
    CountSet (`μ₁ O D) = one + CountSet O + CountDesc O D
    CountSet (`Desc ())
    CountSet (`⟦ () ⟧)
    CountSet (`⟦ () ⟧₁ ())
    CountSet (`μ₁' () ())
    CountSet A = one

    CountDesc : ⟦ 1 ∣ `Π `Set (λ O → `Desc O  `→ `⟦ `ℕ ⟧) ⟧
    CountDesc O (`ι o) = one + count O o
    CountDesc O (`σ A D) = two + CountSet A
    CountDesc O (`δ A D) = two + CountSet A
\end{code}
\caption{Fully generic counting of types (\Fun{CountSet})
  and algebraic arguments (\Fun{CountDesc})
  in universe level 1.}
\label{fig:Count1}
\end{figure}
