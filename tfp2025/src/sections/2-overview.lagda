\begin{code}[hide]
module 2-overview where

open import Data.Nat
open import Data.Maybe
open import Data.List
open import Data.Empty as ⊥
open import Data.Sum
open import Data.Product
open import Data.Bool
open import Data.Unit
open import Function
open import Relation.Nullary

data Token : Set where

-- -- Vendored Guarded Prelude (trusted code, best skipped on first read):
-- 
-- module Prims where
--   primitive
--     primLockUniv : Set₁
-- 
-- open Prims renaming (primLockUniv to LockU) public
-- 
-- private
--   variable
--     l : Level
--     A B : Set l
-- 
-- postulate
--   Tick : LockU
-- 
-- ▹_ : ∀ {l} → Set l → Set l
-- ▹ A = (@tick x : Tick) -> A
-- 
-- map▹ : (A → B) → ▹ A → ▹ B
-- map▹ f x t = f (x t)
-- 
-- ▸_ : ∀ {l} → ▹ Set l → Set l
-- ▸ A = (@tick x : Tick) → A x
-- 
-- next : A → ▹ A
-- next x = λ _ → x
-- 
-- postulate
--   dfix : ∀ {l} {A : Set l} → (▹ A → A) → ▹ A
--   pfix : ∀ {l} {A : Set l} (f : ▹ A → A) → dfix f ≡ next (f (dfix f))
-- 
-- fix : ∀ {l} {A : Set l} → (▹ A → A) → A
-- fix f = f (dfix f)
-- 
-- -- End of trusted code
-- --------------------------------------------------------------------------------


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

\begin{code}
∅ : Lang
∅ _ = ⊥
\end{code}

Going beyond work by Elliot, we can try to define context-free grammars.
Unfortunately, we quickly run into issues due to nontermination. It is not easy
to show that a grammar defined in this way is well-founded. To solve this issue
we can use guarded type theory, in our case provided by guarded cubical Agda.
This allows us to define arbitrary fixed points of languages.

\begin{code}
fueled : (Lang → Lang) → ℕ → Lang
fueled f 0 = ∅
fueled f (suc n) = f (fueled f n)
\end{code}

\begin{code}
fix : (Lang → Lang) → Lang
fix f w = ∃[ n ] fueled f n w
\end{code}