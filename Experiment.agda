open import Data.List
open import Data.Empty
open import Data.Unit
open import Data.Nat as ℕ
open import Data.Char
open import Data.Vec as Vec hiding (_++_)
open import Data.Fin
open import Data.Product
open import Data.Sum as Sum
open import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Bundles
open import Function

String : Set
String = List Char

Lang : Set₁
Lang = String → Set

data Gram (n : ℕ) : Set₁ where
  ∅    : Gram n
  ε    : Gram n
  char : Char → Gram n
  _·_  : {A : Set} → Dec A → Gram n → Gram n
  _∪_  : Gram n → Gram n → Gram n
  _∗_  : Gram n → Gram n → Gram n
  var  : Fin n → Gram n
  μ    : Gram (suc n) → Gram n

variable
  n : ℕ
  w : String

data ⊤₁ : Set₁ where
  tt : ⊤₁

Env : ℕ → Set₁
Env = Vec Lang

_:::_ : (Env n → Lang) → Env n → Env (suc n)
_:::_ x y = x y ∷ y
infixr 20 _:::_

variable
  Γ Γ′ : Env n
  G G₀ : Gram n

typeOfDec : {A : Set} → Dec A → Set
typeOfDec {A} _ = A

⟦_⟧ₒ : Gram n → Env n → Lang

{-# NO_POSITIVITY_CHECK #-}
data ⟦_⟧ (G : Gram (suc n)) (Γ : Env n) : Lang where
  roll : ⟦ G ⟧ₒ (⟦ G ⟧ ::: Γ) w → ⟦ G ⟧ Γ w

unroll : {G : Gram (suc n)} → ⟦ G ⟧ Γ w → ⟦ G ⟧ₒ (⟦ G ⟧ ::: Γ) w
unroll (roll x) = x

⟦ ∅       ⟧ₒ Γ w = ⊥
⟦ ε       ⟧ₒ Γ w = w ≡ []
⟦ char c′ ⟧ₒ Γ w = w ≡ c′ ∷ []
⟦ x · G   ⟧ₒ Γ w = typeOfDec x × ⟦ G ⟧ₒ Γ w
⟦ G ∪ G₁  ⟧ₒ Γ w = ⟦ G ⟧ₒ Γ w ⊎ ⟦ G₁ ⟧ₒ Γ w 
⟦ G ∗ G₁  ⟧ₒ Γ w = ∃[ u ] ∃[ v ] w ≡ u ++ v × ⟦ G ⟧ₒ Γ u × ⟦ G₁ ⟧ₒ Γ v
⟦ var i   ⟧ₒ Γ w = Vec.lookup Γ i w
⟦ μ G     ⟧ₒ Γ w = ⟦ G ⟧ Γ w

variable
  k : ℕ
  φ : Env n → Env (k ℕ.+ n)

data EnvSlice (n : ℕ) : (k : ℕ) → (Env n → Env (k ℕ.+ n)) → Set₁ where
  []  : EnvSlice n zero (λ x → x)
  _∷_ : (G : Gram (suc k ℕ.+ n)) → EnvSlice n k φ → EnvSlice n (suc k) ((⟦ G ⟧ :::_) ∘ φ)

⟦_⟧ₒ-mapₖ :
  (G : Gram (k ℕ.+ n))
  (e : EnvSlice n k φ)
  (f : ∀{w} → (i : Fin n) → Vec.lookup Γ i w → Vec.lookup Γ′ i w) →
  ⟦ G ⟧ₒ (φ Γ) w → ⟦ G ⟧ₒ (φ Γ′) w

⟦_⟧ₒ-mapₖ ε         e f x = x
⟦_⟧ₒ-mapₖ (char x₁) e f x = x
⟦_⟧ₒ-mapₖ (τ · G)   e f (x , y) = x , ⟦_⟧ₒ-mapₖ G e f y
⟦_⟧ₒ-mapₖ (G ∪ G₁)  e f (inj₁ x) = inj₁ (⟦_⟧ₒ-mapₖ G e f x)
⟦_⟧ₒ-mapₖ (G ∪ G₁)  e f (inj₂ y) = inj₂ (⟦_⟧ₒ-mapₖ G₁ e f y)
⟦_⟧ₒ-mapₖ (G ∗ G₁)  e f (u , v , refl , x , y) = u , v , refl , ⟦_⟧ₒ-mapₖ G e f x , ⟦_⟧ₒ-mapₖ G₁ e f y
⟦_⟧ₒ-mapₖ (var i)       []      f x        = f i x
⟦_⟧ₒ-mapₖ (var zero)    (G ∷ e) f (roll x) = roll (⟦_⟧ₒ-mapₖ G (G ∷ e) f x)
⟦_⟧ₒ-mapₖ (var (suc i)) (_ ∷ e) f x        = ⟦_⟧ₒ-mapₖ (var i) e f x
⟦_⟧ₒ-mapₖ (μ G)     e f (roll x) = roll (⟦_⟧ₒ-mapₖ G (G ∷ e) f x)

⟦_⟧ₒ-map : (G : Gram n) → (∀{w} (i : Fin n) → Vec.lookup Γ i w → Vec.lookup Γ′ i w) → ⟦ G ⟧ₒ Γ w → ⟦ G ⟧ₒ Γ′ w
⟦ ε       ⟧ₒ-map f x = x
⟦ char c′ ⟧ₒ-map f x = x
⟦ d · G   ⟧ₒ-map f (x , y) = x , ⟦ G ⟧ₒ-map f y
⟦ G ∪ G₁  ⟧ₒ-map f (inj₁ x) = inj₁ (⟦ G ⟧ₒ-map f x)
⟦ G ∪ G₁  ⟧ₒ-map f (inj₂ y) = inj₂ (⟦ G₁ ⟧ₒ-map f y)
⟦ G ∗ G₁  ⟧ₒ-map f (u , v , refl , x , y) = u , v , refl , ⟦ G ⟧ₒ-map f x , ⟦ G₁ ⟧ₒ-map f y
⟦ var i   ⟧ₒ-map f x = f i x
⟦ μ G     ⟧ₒ-map f (roll x) = roll (⟦_⟧ₒ-mapₖ G (G ∷ []) f x)

⟦_⟧-map : (G : Gram (suc n)) → (∀{w} (i : Fin n) → Vec.lookup Γ i w → Vec.lookup Γ′ i w) → ⟦ G ⟧ Γ w → ⟦ G ⟧ Γ′ w
⟦ G ⟧-map = ⟦_⟧ₒ-map (μ G)

ν : Lang → Set
ν L = L []

δ : Char → Lang → Lang
(δ c L) w = L (c ∷ w)

νμ→ : (G : Gram (suc n)) → ν (⟦ G ⟧ₒ ((λ _ → ⊥) ∷ Γ)) → ν (⟦ G ⟧ₒ (⟦ G₀ ⟧ ::: Γ))
νμ→ G x = ⟦ G ⟧ₒ-map (λ { zero () ; (suc i) → id }) x

lift⊎₂ : {A B C D : Set} → (A → B → C) → (A ⊎ D) → (B ⊎ D) → (C ⊎ D)
lift⊎₂ f (inj₁ x) (inj₁ y) = inj₁ (f x y)
lift⊎₂ f (inj₁ _) (inj₂ y) = inj₂ y
lift⊎₂ f (inj₂ x) _ = inj₂ x

νμ← : (G : Gram (k ℕ.+ suc n)) (e : EnvSlice (suc n) k φ) →
  ν (⟦ G ⟧ₒ (φ (⟦ G₀ ⟧ ::: Γ))) → ν (⟦ G ⟧ₒ (φ ((λ _ → ⊥) ∷ Γ))) ⊎ ν (⟦ G₀ ⟧ₒ ((λ _ → ⊥) ∷ Γ))
νμ← ε                   e x = inj₁ x
νμ← (x₁ · G)            e (x , y) = Sum.map₁ (x ,_) (νμ← G e y)
νμ← (G ∪ G₁)            e (inj₁ x) = Sum.map₁ inj₁ (νμ← G e x)
νμ← (G ∪ G₁)            e (inj₂ y) = Sum.map₁ inj₂ (νμ← G₁ e y)
νμ← (G ∗ G₁)            e ([] , [] , refl , x , y) = lift⊎₂ (λ x y → [] , [] , refl , x , y) (νμ← G e x) (νμ← G₁ e y)
νμ← {G₀ = G} (var zero) [] (roll x) = inj₂ (Sum.reduce (νμ← G [] x))
νμ← (var (suc i)) [] x = inj₁ x
νμ← (var zero) (G ∷ e) (roll x) = Sum.map₁ roll (νμ← G (G ∷ e) x)
νμ← (var (suc i)) (_ ∷ e) x = νμ← (var i) e x
νμ← (μ G)               e (roll x) = Sum.map₁ roll (νμ← G (G ∷ e) x)

νₒ : (G : Gram n) → ((i : Fin n) → Dec (ν (Vec.lookup Γ i))) → Dec (ν (⟦ G ⟧ₒ Γ))
νₒ ∅        ev = no λ ()
νₒ ε        ev = yes refl
νₒ (char x) ev = no λ ()
νₒ (x · G)  ev = x ×-dec νₒ G ev
νₒ (G ∪ G₁) ev = νₒ G ev ⊎-dec νₒ G₁ ev
νₒ (G ∗ G₁) ev = Dec.map (mk⇔ (λ x → [] , [] , refl , x) (λ { ([] , [] , refl , x) → x })) (νₒ G ev ×-dec νₒ G₁ ev)
νₒ (var i)  ev = ev i
νₒ (μ G)    ev = Dec.map (mk⇔ (roll ∘ νμ→ G) (Sum.reduce ∘ νμ← G [] ∘ unroll)) (νₒ G (λ { zero → no λ () ; (suc i) → ev i }))

