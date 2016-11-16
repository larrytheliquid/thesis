\AgdaHide{
\begin{code}
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product
module _ where
 data List {ℓ} (A : Set ℓ) : Set ℓ where
   nil : List A
   cons : A → List A → List A
\end{code}}

\section{Generic Programming}

%% TODO makes sense to have param poly and uni poly both
%% be generic, bc param is also a universe

%% TODO Generic & generic

\AgdaHide{
\begin{code}
module _ where
 private
\end{code}}

\subsection{Generic Programming}

\textit{Generic programming} is the act of writing
functions that can be applied to values of a collection of types
(a \textit{universe}).
types. Given a collection of types, a \textit{generic function} can be
applied to values of any type in the collection. A generic
function is valuable because a single definition can replace many
specialized, or concrete, definitions (one for each type the generic
function is defined over).

\paragraph{Parametrically Polymorphic Functions}

A popular form of generic programming in non-dependent languages is
writing \textit{parametrically polymorphic functions}.

\begin{code}
  append : {A : Set} → List A → List A → List A
  append = {!!}
\end{code}


\paragraph{Universe Polymorphic Functions}


%% gp: fun that works for many datatypes
%% parametric poly vs gp
%% fully generic functions like `any`
%% but for closed type theories

\AgdaHide{
\begin{code}
module _ where
 private
  data ListStar : Set where
    `Base : ListStar
    `List : ListStar → ListStar
  
  ⟦_⟧ : ListStar → Set → Set
  ⟦ `Base ⟧ X = X
  ⟦ `List A ⟧ X = List (⟦ A ⟧ X)
\end{code}}

\begin{code}
  Append : ListStar → Set → Set
  Append `Base X = List X
  Append (`List A) X = List (⟦ A ⟧ X)

  append : ∀{X} (A : ListStar) → ⟦ A ⟧ X → ⟦ A ⟧ X → Append A X
  append `Base x y = cons x (cons y nil)  
  append (`List A) nil ys = ys
  append (`List A) (cons x xs) ys = cons x (append (`List A) xs ys)
\end{code}

\begin{code}
  Maps : (A : ListStar) (X Y : Set) → ⟦ A ⟧ X → Set
  Maps `Base X Y x = X → Y
  Maps (`List A) X Y nil = ⊤
  Maps (`List A) X Y (cons xs xss) = Maps A X Y xs × Maps (`List A) X Y xss

  maps : ∀{X Y} (A : ListStar) (a : ⟦ A ⟧ X) → Maps A X Y a → ⟦ A ⟧ Y
  maps `Base x f = f x
  maps (`List A) nil tt = nil
  maps (`List A) (cons xs xss) (fs , fss) = cons (maps A xs fs) (maps (`List A) xss fss)
\end{code}


