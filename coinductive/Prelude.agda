{-# OPTIONS --guardedness --safe #-}

module Prelude where

open import Agda.Primitive using (Level ; _⊔_)

variable
  ℓ ℓ₁ ℓ₂ : Level
  A B C : Set ℓ

data List (A : Set ℓ) : Set ℓ where
  [] : List A
  _∷_ : A → List A → List A

infixr 20 _∷_

_++_ : List A → List A → List A
[] ++ v = v
(c ∷ u) ++ v = c ∷ (u ++ v)

data ⊥ : Set where

data _≡_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set where
  refl : x ≡ x
infix 19 _≡_

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

record _×_ (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field pl : A
        pr : B
open _×_

infixr 21 _×_
infixr 21 _,_

record ∃ {A : Set ℓ₁} (f : A → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field pl : A
        pr : f pl

data Dec (A : Set) : Set where
  yes : A → Dec A
  no : (A → ⊥) → Dec A

module T where
    data Tok : Set where
        x : Tok
        + : Tok

    _≟_ : (c c′ : Tok) → Dec (c ≡ c′) 
    x ≟ x = yes refl
    x ≟ + = no (λ ())
    + ≟ x = no (λ ())
    + ≟ + = yes refl
open T using (Tok ; _≟_)

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

variable n m : ℕ

data Fin : ℕ → Set where
  zero : Fin (suc n)
  suc : Fin n → Fin (suc n)

data Vec {ℓ : Level} (A : Set ℓ) : ℕ → Set ℓ where
  [] : Vec A zero
  _∷_ : A → Vec A n → Vec A (suc n)

lookup : (xs : Vec A n) → Fin n → A
lookup (x ∷ _) zero = x
lookup (_ ∷ xs) (suc i) = lookup xs i

mapVec : (A → B) → Vec A n → Vec B n
mapVec f [] = []
mapVec f (x ∷ xs) = f x ∷ mapVec f xs

record _↔_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
open _↔_


consrn : ∀{n m} → (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
consrn f zero = zero
consrn f (suc i) = suc (f i)

↔cong : (f : Set → Set) (map : ∀{X Y : Set} → (X → Y) → f X → f Y) → A ↔ B → f A ↔ f B
↔cong f map bi .to x = map (bi .to) x
↔cong f map bi .from x = map (bi .from) x

↔cong₂ : ∀{A₁ A₂ B₁ B₂} (f : Set → Set → Set) (map : ∀{X₁ X₂ Y₁ Y₂ : Set} → (X₁ → Y₁) → (X₂ → Y₂) → f X₁ X₂ → f Y₁ Y₂) → A₁ ↔ B₁ → A₂ ↔ B₂ → f A₁ A₂ ↔ f B₁ B₂
↔cong₂ f map bi₁ bi₂ .to x = map (bi₁ .to) (bi₂ .to) x
↔cong₂ f map bi₁ bi₂ .from x = map (bi₁ .from) (bi₂ .from) x

↔sym : A ↔ B → B ↔ A
to (↔sym bi) = from bi
from (↔sym bi) = to bi

_∘_ : (B -> C) -> (A -> B) -> A -> C
(f ∘ g) x = f (g x)

emaner : (Fin n → Fin m) → Vec A m → Vec A n
emaner {zero} f xs = []
emaner {suc n} f xs = lookup xs (f zero) ∷ emaner (f ∘ suc) xs

lookup-f : ∀{f : Fin n → Fin m} (xs : Vec A m) (i : Fin n) → lookup xs (f i) ≡ lookup (emaner f xs) i 
lookup-f {f = f} xs zero with f zero
... | zero = refl
... | (suc j) = refl
lookup-f {f = f} xs (suc i) = lookup-f xs i

subst : {A : Set ℓ₁} {x y : A} (P : A → Set ℓ₂) → (x ≡ y) → P x → P y
subst _ refl x = x

sym : {x y : A} → x ≡ y → y ≡ x
sym refl = refl

_⊎?_ : Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎? y = yes (inl x)
no x ⊎? yes x₁ = yes (inr x₁)
no x ⊎? no x₁ = no (λ { (inl y) → x y ; (inr y) → x₁ y })

_×?_ : Dec A → Dec B → Dec (A × B)
yes x ×? yes x₁ = yes (x , x₁)
yes x ×? no x₁ = no (λ z → x₁ (_×_.pr z))
no x ×? y = no (λ z → x (_×_.pl z))

⊎mapl : ∀{C} → (A → C) → A ⊎ B → C ⊎ B
⊎mapl f (inl x) = inl (f x)
⊎mapl f (inr x) = inr x

⊎collapse : A ⊎ A → A
⊎collapse (inl x) = x
⊎collapse (inr x) = x

⊎lift2l : ∀{C D} → (A → B → C) → A ⊎ D → B ⊎ D → C ⊎ D
⊎lift2l f (inl x) (inl x₁) = inl (f x x₁)
⊎lift2l f (inl x) (inr x₁) = inr x₁
⊎lift2l f (inr x) y = inr x

↔refl : A ↔ A
to ↔refl x = x
from ↔refl x = x

↔lookup : (f : A → Set) (xs : Vec A n) (i : Fin n) → lookup (mapVec f xs) i ↔ f (lookup xs i)
↔lookup f (x ∷ xs) zero = ↔refl
↔lookup f (x ∷ xs) (suc i) = ↔lookup f xs i


tabulate : (Fin n → A) → Vec A n
tabulate {zero} f = []
tabulate {suc n} f = f zero ∷ tabulate (f ∘ suc)

lookup-tabulate : ∀ n {f : Fin n → B} {i : Fin n} → lookup (tabulate f) i ≡ f i
lookup-tabulate (suc n) {i = zero} = refl
lookup-tabulate (suc n) {i = suc i} = lookup-tabulate n

≡→↔ : A ≡ B → A ↔ B
≡→↔ refl = ↔refl

mapDec : (A ↔ B) → Dec A → Dec B
mapDec bi (yes x) = yes (to bi x)
mapDec bi (no ¬x) = no (λ y → ¬x (from bi y))

data Bool : Set where
  false : Bool
  true : Bool

data ⊤ : Set where
  tt : ⊤

lookup-map : (f : A → B) (v : Vec A n) (i : Fin n) → lookup (mapVec f v) i ≡ f (lookup v i)
lookup-map f (x ∷ v) zero = refl
lookup-map f (x ∷ v) (suc i) = lookup-map f v i

const : A → B → A
const x _ = x
