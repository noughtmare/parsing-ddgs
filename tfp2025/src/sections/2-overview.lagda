\begin{code}[hide]
{-# OPTIONS --cubical --guarded #-}
module 2-overview where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Data.Nat
open import Cubical.Data.Maybe
open import Cubical.Data.List
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Agda.Builtin.Unit
open import Cubical.Relation.Nullary.Base
open import Cubical.Foundations.Function
open import Cubical.Relation.Nullary

data Token : Set where

--------------------------------------------------------------------------------
-- Vendored Guarded Prelude (trusted code, best skipped on first read):

module Prims where
  primitive
    primLockUniv : Set₁

open Prims renaming (primLockUniv to LockU) public

private
  variable
    l : Level
    A B : Set l

postulate
  Tick : LockU

▹_ : ∀ {l} → Set l → Set l
▹ A = (@tick x : Tick) -> A

map▹ : (A → B) → ▹ A → ▹ B
map▹ f x t = f (x t)

▸_ : ∀ {l} → ▹ Set l → Set l
▸ A = (@tick x : Tick) → A x

next : A → ▹ A
next x = λ _ → x

postulate
  dfix : ∀ {l} {A : Set l} → (▹ A → A) → ▹ A
  pfix : ∀ {l} {A : Set l} (f : ▹ A → A) → dfix f ≡ next (f (dfix f))

fix : ∀ {l} {A : Set l} → (▹ A → A) → A
fix f = f (dfix f)

-- End of trusted code
--------------------------------------------------------------------------------


\end{code}

\section{Languages}

In this section, we recapitulate the basic definitions from previous work by Elliot~\cite{conal-languages} and .

A language is a set of strings $\mathbb{2}^{(\af{List}~\af{Token})}$.


\begin{code}[hide]
Lang : Set₁
\end{code}
\begin{code}
Lang = List Token → Set
\end{code}

This type has a very rich structure. It forms an ... algebra with union and intersection and a semiring with union and sequential composition.

Going beyond work by Elliot, we can try to define context-free grammars.
Unfortunately, we quickly run into issues due to nontermination. It is not easy
to show that a grammar defined in this way is well-founded. To solve this issue
we can use guarded type theory, in our case provided by guarded cubical Agda.
This allows us to define arbitrary fixed points of languages.

\begin{code}
delay : ▹ Lang → Lang
delay L word = ▸ (λ tick → L tick word) 
\end{code}

\begin{code}
fix₀ : (Lang → Lang) → Lang
fix₀ f = fix (λ L → f (delay L))
\end{code}