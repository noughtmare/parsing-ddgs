{-# OPTIONS --cubical --guarded #-}
module GuardedParser where

open import Cubical.Foundations.Prelude hiding (_[_↦_])
open import Cubical.Foundations.Transport
open import Cubical.Data.Nat
open import Cubical.Data.Maybe
open import Cubical.Relation.Nullary.Base

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

▸_ : ∀ {l} → ▹ Set l → Set l
▸ A = (@tick x : Tick) → A x

next : A → ▹ A
next x _ = x

postulate
  dfix : ∀ {l} {A : Set l} → (▹ A → A) → ▹ A
  pfix : ∀ {l} {A : Set l} (f : ▹ A → A) → dfix f ≡ next (f (dfix f))

fix : ∀ {l} {A : Set l} → (▹ A → A) → A
fix f = f (dfix f)

-- End of trusted code

variable ℓ : Level

data Symbol : Set where
  ‵+ : Symbol
  ‵x : Symbol

open import Cubical.Data.List
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty

String : Set
String = List Symbol

Lang : Set₁
Lang = String → Set

variable w : String

data T (A : Lang) : Lang where -- Delay monad
  ret : A w → T A w
  step : ▹ (T A w) → T A w

_>>=T_ : ∀ {A B : Lang} → T A w → (A w → T B w) → T B w
T.ret a >>=T k = k a
T.step τ >>=T k = T.step (λ α → τ α >>=T k)

data Option (A : Set) : Set where
  none : Option A
  some : A → Option A

data Gram (A : Set) : Set where
  ∅ ε : Gram A
  `_ : Symbol → Gram A
  _∪_ _*_ : (_ _ : Gram A) → Gram A
  V : A → Gram A
  μ : Gram (Option A) → Gram A

variable G : Gram A

⟦_⟧ : Gram A → (A → Lang) → Lang
⟦_⟧ = λ G Γ → T (⟦ G ⟧′ Γ) where
    ⟦_⟧′ : Gram A → (A → Lang) → Lang
    ⟦ ∅ ⟧′ Γ _ = ⊥
    ⟦ ε ⟧′ Γ w = w ≡ []
    ⟦ ` c ⟧′ Γ w = w ≡ (c ∷ [])
    ⟦ G₁ ∪ G₂ ⟧′ Γ w = ⟦ G₁ ⟧ Γ w ⊎ ⟦ G₂ ⟧ Γ w
    ⟦ G₁ * G₂ ⟧′ Γ w = Σ String λ u → Σ String λ v → (w ≡ u ++ v) × ⟦ G₁ ⟧ Γ u × ⟦ G₂ ⟧ Γ v
    ⟦ V x ⟧′ Γ = Γ x
    ⟦ μ G ⟧′ Γ = fix λ x w → ▸ λ α → ⟦ G ⟧ (λ { none → λ w → x α w ; (some x) → Γ x }) w

⟦_⟧₀ : Gram ⊥ → Lang
⟦ G ⟧₀ = ⟦ G ⟧ λ ()

⟦_⟧₁ : Gram (Option ⊥) → Lang → Lang
⟦ G ⟧₁ X = ⟦ G ⟧ λ { none → X }

-- step-to   : {P : Lang} {x : T P w} → step (λ _ → x) → x
-- step-to = ?
-- step-from : {P : Lang} {x : T P w} → x → step (λ _ → x)
-- step-from = ?

⊥-elim : {A : Set ℓ} → ⊥ → A
⊥-elim ()

▹⟦⟧-to : {G : Gram A} {f : A → Lang} → ▹ (⟦ G ⟧ f w) → ⟦ G ⟧ f w
▹⟦⟧-to = step

▹⟦⟧-from : {G : Gram A} {f : A → Lang} → ⟦ G ⟧ f w → ▹ (⟦ G ⟧ f w)
▹⟦⟧-from (ret x) = next (ret x)
▹⟦⟧-from (step x) = x

▹⟦⟧-to∘from : {f : A → Lang} {x : ⟦ G ⟧ f w} → ▹⟦⟧-to {G = G} (▹⟦⟧-from {G = G} x) ≡ x
▹⟦⟧-to∘from {x = ret x} = {!!}
▹⟦⟧-to∘from {x = step x} = refl

map⟦_⟧ : {Γ : A → Lang} (G : Gram A) → (F : A → Lang → Lang) (f : (x : A) {w : String} → Γ x w → F x (Γ x) w) → ⟦ G ⟧ Γ w → ⟦ G ⟧ (λ x → F x (Γ x)) w
map⟦ ∅ ⟧ F f x = x
map⟦ ε ⟧ F f x = x
map⟦ ` x₁ ⟧ F f x = x
map⟦ G ∪ G₁ ⟧ F f x = x >>=T λ where
  (inl x) → ret (inl (map⟦ G ⟧ F f x))
  (inr x) → ret (inr (map⟦ G₁ ⟧ F f x))
map⟦ G * G₁ ⟧ F f x = x >>=T λ where
  (u , v , refl , x , y) → ret (u , v , refl , map⟦ G ⟧ F f x , map⟦ G₁ ⟧ F f y)
map⟦ V v ⟧ F f x = x >>=T λ where
  x → ret (f v x)
map⟦ μ G ⟧ F f x = x >>=T λ where
  x → ret λ α → map⟦ G ⟧ (λ { none → λ x → x ; (some x) → F x }) {!!} (x α) 

to : {G : Gram (Option ⊥)} → ⟦ μ G ⟧₀ w → ⟦ G ⟧₁ ⟦ μ G ⟧₀ w 
to {G = G} x = x >>=T λ x → step λ α → x α >>=T λ x → ret {!x!}

-- ∅ ε : Lang
-- ∅ _ = ⊥
-- ε w = (w ≡ [])
-- 
-- ‵_ : Symbol → Lang
-- (‵ c) w = (w ≡ (c ∷ []))
-- 
-- _∪_ _*_ : (_ _ : Lang) → Lang
-- (P ∪ Q) w = P w ⊎ Q w
-- (P * Q) w = Σ String λ u → Σ String λ v → P u × Q v
-- 
-- μ : (Lang → Lang) → Lang
-- μ P = fix (λ x w → ▸ λ α → P (x α) w)

-- ≡-D : {P : Lang → Lang} → (▸ λ α₁ → (dfix (λ x w′ → ▸ (λ α₂ → P (x α₂) w′)) α₁)) ≡ ▹ (μ P w)
-- ≡-D {w} {P = P} i = ▸ λ α → T (pfix (λ x w′ → ▸ (λ α₂ → P (x α₂) w′)) i α) w

-- to : {P : Lang → Lang} → μ P w → ▹ (P (μ P) w)
-- to {w} {P} = λ where
--   x → λ α → transport (cong (λ X → P X w) (λ i → pfix (λ x w → ▸ λ α → P (x α) w) i α)) (x α)

-- ≡-D : ▸ (λ α → T (dfix ValueF α)) ≡ ▹ D
-- ≡-D i = (@tick α : Tick) → T (pfix ValueF i α)
