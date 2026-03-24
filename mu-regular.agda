{-# OPTIONS --guardedness #-}
module mu-regular where

open import Data.Sum
open import Data.Vec as Vec hiding (_++_ ; lookup)
open import Relation.Nullary.Decidable as Dec
open import Data.Fin
open import Data.Nat hiding (_*_ ; _⊔_)
open import Data.Product
open import Data.Empty
open import Data.Char as Char
open import Relation.Binary.PropositionalEquality
open import Data.List as List hiding (lookup)
open import Function
open import Level using (Level ; _⊔_)

String : Set
String = List Char

module ◇ where
    Lang : Set₁
    Lang = String → Set

    ∅ : Lang
    ∅ _ = ⊥

    ‵_ : Char → Lang
    (‵ c) w = w ≡ c ∷ []

    ε : Lang
    ε w = w ≡ []

    _∪_ : Lang → Lang → Lang
    (P ∪ Q) w = P w ⊎ Q w

    _*_ : Lang → Lang → Lang
    (P * Q) w = ∃[ u ] ∃[ v ] w ≡ u ++ v × P u × Q v

    _·_ : Set → Lang → Lang
    (A · P) w = A × P w

    ν : Lang → Set
    ν L = L []

    δ : Char → Lang → Lang
    (δ c L) w = L (c ∷ w)

variable
  ℓ ℓ′ : Level
  A : Set

data Exp (n : ℕ) : Set₁ where
  ∅ : Exp n
  ε : Exp n
  ‵_ : Char → Exp n
  _∪_ : Exp n → Exp n → Exp n
  _*_ : Exp n → Exp n → Exp n
  _·_ : Dec A → Exp n → Exp n
  var : Fin n → Exp n
  μ : Exp (suc n) → Exp n

variable n m : ℕ

rnsuc : (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
rnsuc f zero = zero
rnsuc f (suc i) = suc (f i)

shift : (Fin n → Fin m) → Exp n → Exp m
shift Γ ∅ = ∅
shift Γ ε = ε
shift Γ (‵ c) = ‵ c
shift Γ (P ∪ Q) = shift Γ P ∪ shift Γ Q
shift Γ (P * Q) = shift Γ P * shift Γ Q
shift Γ (x · Q) = x · shift Γ Q
shift Γ (var i) = var (Γ i)
shift Γ (μ P) = μ (shift (rnsuc Γ) P)

fin : ∀{ℓ} {A : Set ℓ} → A → (Fin n → A) → Fin (suc n) → A
fin X f zero = X
fin X f (suc i) = f i

substE : (Fin n → Exp m) → Exp n  → Exp m
substE Γ ∅ = ∅
substE Γ ε = ε
substE _ (‵ c) = ‵ c
substE Γ (P ∪ Q) = substE Γ P ∪ substE Γ Q
substE Γ (P * Q) = substE Γ P * substE Γ Q
substE Γ (x · P) = x · substE Γ P
substE Γ (var i) = Γ i
substE Γ (μ P) = μ (substE (fin (var zero) (shift suc ∘ Γ)) P)

singleton : ∀{ℓ} {A : Set ℓ} → A → Fin 1 → A
singleton x zero = x

variable w : String

⟦_⊢_⟧ : Vec ◇.Lang n → Exp n → ◇.Lang

data □⟦_⊢_⟧ (Γ : Vec ◇.Lang n) (P : Exp n) : ◇.Lang where
  □_ : ⟦ Γ ⊢ P ⟧ w → □⟦ Γ ⊢ P ⟧ w

⟦ _ ⊢ ∅ ⟧ = ◇.∅
⟦ _ ⊢ ε ⟧ = ◇.ε
⟦ _ ⊢ ‵ c ⟧ = ◇.‵ c
⟦ Γ ⊢ P ∪ Q ⟧ = ⟦ Γ ⊢ P ⟧ ◇.∪ ⟦ Γ ⊢ Q ⟧
⟦ Γ ⊢ P * Q ⟧ = ⟦ Γ ⊢ P ⟧ ◇.* ⟦ Γ ⊢ Q ⟧
⟦ Γ ⊢ _·_ {A} _ P ⟧ = A ◇.· ⟦ Γ ⊢ P ⟧
⟦ Γ ⊢ var i ⟧ = Vec.lookup Γ i
⟦ Γ ⊢ μ P ⟧ = □⟦ Γ ⊢ substE (fin (μ P) var) P ⟧

record Triple (Γ : Vec ◇.Lang n) (L : ◇.Lang) : Set₁ where
  field
    nullable : Dec (◇.ν L)
    derivative : Exp (suc n)
    origin : Exp n
    -- derivative-to : ⟦ Γ ⊢ derivative c ⟧ w → (◇.δ c L) w
    -- derivative-from : (◇.δ c L) w → ⟦ Γ ⊢ derivative c ⟧ w
    -- origin-to : ⟦ Γ ⊢ origin ⟧ w → L w 
    -- origin-from : L w → ⟦ Γ ⊢ origin ⟧ w
open Triple

data Ctx : Vec ◇.Lang n → Set₁ where
  [] : Ctx []
  _∷_ : ∀{x} {xs : Vec ◇.Lang n} → Triple xs x → Ctx xs → Ctx (x ∷ xs)

-- lookupTriple : Vec ◇.Lang n → Fin n → Set₁
-- lookupTriple (x ∷ xs) zero = Triple xs x
-- lookupTriple (x ∷ xs) (suc i) = lookupTriple xs i

variable L L′ : ◇.Lang
variable Γ : Vec ◇.Lang n

shiftTriple : Triple Γ L → Triple (L′ ∷ Γ) L
shiftTriple record { nullable = nullable ; derivative = derivative ; origin = origin } =
    record { nullable = nullable ; derivative = shift suc derivative ; origin = shift suc origin }

lookup : Ctx (L ∷ Γ) → (i : Fin (suc n)) → Triple Γ (Vec.lookup (L ∷ Γ) i)
lookup (x ∷ _) zero = x
lookup (x ∷ Γ) (suc i) = {!shiftTriple (lookup Γ i)!}

data νCtx : Vec ◇.Lang n → Set₁ where
  [] : νCtx []
  _∷_ : Dec (◇.ν L) → νCtx Γ → νCtx (L ∷ Γ)

νlookup : νCtx Γ → (i : Fin n) → Dec (◇.ν (Vec.lookup Γ i))
νlookup = {!!}

Ctx→νCtx : Ctx Γ → νCtx Γ
Ctx→νCtx = {!!}

tsbub : (f : Fin n → Exp m) (Γ : Vec ◇.Lang m) → Vec ◇.Lang n
tsbub {zero} f Γ = []
tsbub {suc n} f Γ = ⟦ Γ ⊢ f zero ⟧ ∷ tsbub (f ∘ suc) Γ

subst-roll : {Γ : Vec ◇.Lang m} {f : Fin n → Exp m} (P : Exp n)
  → ⟦ tsbub f Γ ⊢ P ⟧ w → ⟦ Γ ⊢ substE f P ⟧ w
subst-roll ε x = x
subst-roll (‵ c) x = x
subst-roll (P ∪ Q) (inj₁ x) = inj₁ (subst-roll P x)
subst-roll (P ∪ Q) (inj₂ y) = inj₂ (subst-roll Q y)
subst-roll (P * Q) (u , v , refl , x , y) = u , v , refl , subst-roll P x , subst-roll Q y
subst-roll (s · P) (x , y) = x , subst-roll P y
subst-roll (var zero) x = x
subst-roll (var (suc i)) x = subst-roll (var i) x
subst-roll (μ P) (□ x) = □ {!subst-roll (substE (fin (μ P) var) P) x!}

ν-roll : {Γ : Vec ◇.Lang n} (P : Exp (suc n))
  → ◇.ν ⟦ ◇.∅ ∷ Γ ⊢ P ⟧ → ◇.ν ⟦ Γ ⊢ substE (fin (μ P) var) P ⟧
ν-roll P x = subst-roll P {!x!}

ν⟦_⊢_⟧ : {Γ : Vec ◇.Lang n} → (Γν : νCtx Γ) → (P : Exp n) → Dec (◇.ν ⟦ Γ ⊢ P ⟧)
ν⟦ _ ⊢ ∅ ⟧ = no λ ()
ν⟦ _ ⊢ ε ⟧ = yes refl
ν⟦ _ ⊢ ‵ _ ⟧ = no λ ()
ν⟦ Γ ⊢ P ∪ Q ⟧ = ν⟦ Γ ⊢ P ⟧ ⊎-dec ν⟦ Γ ⊢ Q ⟧
ν⟦ Γ ⊢ P * Q ⟧ = Dec.map′ (λ x → [] , [] , refl , x) (λ { ([] , [] , _ , x) → x }) (ν⟦ Γ ⊢ P ⟧ ×-dec ν⟦ Γ ⊢ Q ⟧)
ν⟦ Γ ⊢ x · P ⟧ = x ×-dec ν⟦ Γ ⊢ P ⟧
ν⟦ Γ ⊢ var i ⟧ = νlookup Γ i
ν⟦ Γ ⊢ μ P ⟧ = Dec.map′ (□_ ∘ subst-roll P ∘ {!!}) {!ν-unroll P!} ν⟦ no (λ ()) ∷ Γ ⊢ P ⟧

variable c : Char

δ_[_⊢_] : {Γ : Vec ◇.Lang n} → Char → (Γδ : Ctx Γ) → Exp n → Exp n
δ c [ _ ⊢ ∅ ] = ∅
δ c [ _ ⊢ ε ] = ∅
δ c [ _ ⊢ ‵ c′ ] with c Char.≟ c′
... | yes _ = ε
... | no _ = ∅
δ c [ Γ ⊢ P ∪ Q ] = δ c [ Γ ⊢ P ] ∪ δ c [ Γ ⊢ Q ]
δ c [ Γ ⊢ P * Q ] = (δ c [ Γ ⊢ P ] * substE (λ i → {!lookup Γ i .origin!}) Q) ∪ (ν⟦ Ctx→νCtx Γ ⊢ P ⟧ · δ c [ Γ ⊢ Q ]) 
δ c [ Γ ⊢ x · P ] = x · δ c [ Γ ⊢ P ]
δ c [ Γ ⊢ var i ] = {!lookup Γ i .derivative!}
δ_[_⊢_] {Γ = Γ′} c Γ (μ P) = μ (δ_[_⊢_] {Γ = ⟦ Γ′ ⊢ μ P ⟧ ∷ Γ′} c (record { nullable = ν⟦ Ctx→νCtx Γ ⊢ μ P ⟧ ; derivative = var zero ; origin = μ P } ∷ Γ) P)




-- -- ◇⟦_⟧ : ◇.Exp → ◇.Lang
-- -- 
-- -- 
-- -- ◇⟦ ◇.∅ ⟧ = ◇.∅
-- -- ◇⟦ ◇.ε ⟧ = ◇.ε
-- -- ◇⟦ P ◇.∪ Q ⟧ = ◇⟦ P ⟧ ◇.∪ ◇⟦ Q ⟧
-- -- ◇⟦ P ◇.* Q ⟧ = ◇⟦ P ⟧ ◇.* ◇⟦ Q ⟧
-- -- ◇⟦ A ◇.· P ⟧ = A ◇.· ◇⟦ P ⟧
-- -- ◇⟦ ◇.∞ P ⟧ = ∞Exp P
-- 
-- -- ⟦_⟧ : Exp n → Vec ◇.Lang n → ◇.Lang
-- -- ⟦ ∅ ⟧ _ = ◇.∅
-- -- ⟦ ε ⟧ _ = ◇.ε
-- -- ⟦ G ∪ G₁ ⟧ Γ = ⟦ G ⟧ Γ ◇.∪ ⟦ G₁ ⟧ Γ
-- -- ⟦ G * G₁ ⟧ Γ = ⟦ G ⟧ Γ ◇.* ⟦ G₁ ⟧ Γ
-- -- ⟦ _·_ {A = A} _ G ⟧ Γ = A ◇.· ⟦ G ⟧ Γ
-- -- ⟦ var i ⟧ Γ = lookup Γ i
-- -- ⟦ μ G ⟧ Γ = ⟦ G ⟧ (⟦ μ G ⟧ Γ ∷ Γ)
-- 
