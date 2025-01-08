{-# OPTIONS --guardedness #-}

open import Agda.Primitive using (Level)

variable
  ℓ : Level
  A B : Set ℓ

data List (A : Set ℓ) : Set ℓ where
  [] : List A
  _∷_ : A → List A → List A

infixr 20 _∷_

_++_ : List A → List A → List A
[] ++ v = v
(c ∷ u) ++ v = c ∷ (u ++ v)

module T where
    data Tok : Set where
        x : Tok
        + : Tok
open T using (Tok)

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

variable n : ℕ

data Fin : ℕ → Set where
  zero : Fin (suc n)
  suc : Fin n → Fin (suc n)

data Vec {ℓ : Level} (A : Set ℓ) : ℕ → Set ℓ where
  [] : Vec A zero
  _∷_ : A → Vec A n → Vec A (suc n)

lookup : (xs : Vec A n) → Fin n → A
lookup (x ∷ _) zero = x
lookup (_ ∷ xs) (suc i) = lookup xs i

data El {A : Set ℓ} : List A → Set ℓ where
  here : ∀{x xs} → El (x ∷ xs)
  there : ∀{x xs} → El xs → El (x ∷ xs)

Lang : Set₁
Lang = List Tok → Set

mutual
    data Gram (n : ℕ) : Set₁ where
        ∅ : Gram n
        ε : Gram n
        ‵_ : Tok → Gram n
        _∪_ : Gram n → Gram n → Gram n
        _∙_ : Gram n → Gram n → Gram n
        var : Fin n → Gram n
        □ : □Gram n → Gram n

    infix 23 ‵_
    infixr 22 _∙_
    infixr 21 _∪_

    record □Gram (n : ℕ) : Set₁ where
        coinductive
        field ! : Gram n

open □Gram using (!)

variable
    Γ Γ′ Γ₁ Γ₂ : Vec Lang n
    G G₁ G₂ : Gram n
    u v w : List Tok
    □G : □Gram n
    c : Tok

module _ where
    open □Gram

    left-right : Gram n
    left-right = let left-right = □ λ { .! → left-right } in
        left-right ∙ left-right

    expr : Gram n
    expr = let open T; expr = □ λ { .! → expr } in
        ‵ x ∪ expr ∙ ‵ + ∙ expr

data _≡_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set where
  refl : x ≡ x
infix 19 _≡_

data ⊥ : Set where

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

record _×_ (A B : Set) : Set where
  constructor _,_
  field pl : A
        pr : B

infixr 21 _×_
infixr 21 _,_

record ∃ {A : Set} (f : A → Set) : Set where
  constructor _,_
  field pl : A
        pr : f pl

⟦_⊢_⟧ : (Γ : Vec Lang n) → Gram n → Lang

data □⟦_⊢_⟧ (Γ : Vec Lang n) (□G : □Gram n) (w : List Tok) : Set where
  □ : ⟦ Γ ⊢ ! □G ⟧ w → □⟦ Γ ⊢ □G ⟧ w

lookupEl : {xs : List A} → El xs → A
lookupEl {xs = []} ()
lookupEl {xs = x ∷ _} here = x
lookupEl {xs = _ ∷ xs} (there i) = lookupEl i

⟦ _ ⊢ ∅ ⟧ _ = ⊥
⟦ _ ⊢ ε ⟧ w = w ≡ []
⟦ _ ⊢ ‵ c ⟧ w = w ≡ c ∷ []
⟦ Γ ⊢ G₁ ∪ G₂ ⟧ w = ⟦ Γ ⊢ G₁ ⟧ w ⊎ ⟦ Γ ⊢ G₂ ⟧ w
⟦ Γ ⊢ G₁ ∙ G₂ ⟧ w = ∃ λ u → ∃ λ v → (w ≡ u ++ v) × ⟦ Γ ⊢ G₁ ⟧ u × ⟦ Γ ⊢ G₂ ⟧ v
⟦ Γ ⊢ var i ⟧ w = lookup Γ i w
⟦ Γ ⊢ □ □G ⟧ w = □⟦ Γ ⊢ □G ⟧ w

x+x+x : ⟦ Γ ⊢ expr ⟧ (let open T in x ∷ + ∷ x ∷ + ∷ x ∷ [])
x+x+x = inr (_ , _ , refl , □ (inl refl) , _ , _ , refl , refl , □ (inr (_ , _ , refl , □ (inl refl) , _ , _ , refl , refl , □ (inl refl))))


data Dec (A : Set) : Set where
  yes : A → Dec A
  no : (A → ⊥) → Dec A

record _↔_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
open _↔_

mapDec : (A ↔ B) → Dec A → Dec B
mapDec bi (yes x) = yes (to bi x)
mapDec bi (no ¬x) = no (λ y → ¬x (from bi y))

data Bool : Set where
  false : Bool
  true : Bool

ν : Lang → Set
ν ℒ = ℒ []

δ : Tok → Lang → Lang
δ c ℒ w = ℒ (c ∷ w)

data ⊤ : Set where
  tt : ⊤

-- data All {A : Set ℓ} (f : A → Set) : List A → Set ℓ where
--   [] : All f []
--   _∷_ : ∀{x xs} → f x → All f xs → All f (x ∷ xs)

-- lookupAll : All f Γ → 

ν⟦_⊢_⟧ : (Γ : Vec Lang n) → Gram n → Set

data ν□G (□G : □Gram n) (Γ : Vec Lang n) : Set where
  □ : ν⟦ Γ ⊢ ! □G ⟧ → ν□G □G Γ

-- lookupAll : ∀{f x} → All f Γ → El Γ x → f x
-- lookupAll = {!!}

ν⟦ Γ ⊢ ∅ ⟧ = ⊥
ν⟦ Γ ⊢ ε ⟧ = ⊤
ν⟦ Γ ⊢ ‵ c ⟧ = ⊥
ν⟦ Γ ⊢ G₁ ∪ G₂ ⟧ = ν⟦ Γ ⊢ G₁ ⟧ ⊎ ν⟦ Γ ⊢ G₂ ⟧
ν⟦ Γ ⊢ G₁ ∙ G₂ ⟧ = ν⟦ Γ ⊢ G₁ ⟧ × ν⟦ Γ ⊢ G₂ ⟧
ν⟦ Γ ⊢ var i ⟧ = ν (lookup Γ i)
ν⟦ Γ ⊢ □ □G ⟧ = ν□G □G Γ

-- ↔refl : A ↔ A
-- to ↔refl x = x
-- from ↔refl x = x

νG-sound : (G : Gram n) → ν⟦ Γ ⊢ G ⟧ → ν ⟦ Γ ⊢ G ⟧
νG-sound ε x = refl
νG-sound (G₁ ∪ G₂) (inl x) = inl (νG-sound G₁ x)
νG-sound (G₁ ∪ G₂) (inr y) = inr (νG-sound G₂ y)
νG-sound (G₁ ∙ G₂) (pl , pr) = [] , [] , refl , νG-sound G₁ pl , νG-sound G₂ pr
νG-sound (var _) x = x
νG-sound (□ □G) (□ x) = □ (νG-sound (! □G) x)

νG-complete : (G : Gram n) → ν ⟦ Γ ⊢ G ⟧ → ν⟦ Γ ⊢ G ⟧
νG-complete ε x = tt
νG-complete (G ∪ G₁) (inl x) = inl (νG-complete G x)
νG-complete (G ∪ G₁) (inr x) = inr (νG-complete G₁ x)
νG-complete (G ∙ G₁) ([] , [] , refl , pl , pr) = νG-complete G pl , νG-complete G₁ pr
νG-complete (var i) x = x
νG-complete (□ □G) (□ x) = □ (νG-complete (! □G) x)

νG-correct : (G : Gram n) → ν⟦ Γ ⊢ G ⟧ ↔ ν ⟦ Γ ⊢ G ⟧
to (νG-correct G) = νG-sound G
from (νG-correct G) = νG-complete G

-- data Ix : List A → A → Set where
--   here : Ix (G ∷ Γ) G
--   there : Ix Γ G → Ix (G₁ ∷ Γ) G

const : A → B → A
const x _ = x

fixG′ : Gram (suc n) → Gram (suc n) → Gram n
fixG′ G₀ ∅ = ∅
fixG′ G₀ ε = ε
fixG′ G₀ (‵ c) = ‵ c
fixG′ G₀ (G₁ ∪ G₂) = fixG′ G₀ G₁ ∪ fixG′ G₀ G₂
fixG′ G₀ (G₁ ∙ G₂) = fixG′ G₀ G₁ ∙ fixG′ G₀ G₂
fixG′ G₀ (var zero) = □ (λ { .! → fixG′ G₀ G₀ })
fixG′ G₀ (var (suc i)) = var i
fixG′ G₀ (□ G) = □ (λ { .! → fixG′ G₀ (! G) })

fixG : Gram (suc n) → Gram n
fixG {n = n} G = fixG′ G G

-- Is fixG really a fixed point? Yes:

fixG-sound : ∀{G₀} G → ⟦ Γ ⊢ fixG′ G₀ G ⟧ w → ⟦ (⟦ Γ ⊢ fixG G₀ ⟧ ∷ Γ) ⊢ G ⟧ w
fixG-sound ε x = x
fixG-sound (‵ x₁) x = x
fixG-sound (G₁ ∪ G₂) (inl x) = inl (fixG-sound G₁ x)
fixG-sound (G₁ ∪ G₂) (inr x) = inr (fixG-sound G₂ x)
fixG-sound (G₁ ∙ G₂) (u , v , refl , x , y) = u , v , refl , fixG-sound G₁ x , fixG-sound G₂ y
fixG-sound (var zero) (□ x) = x
fixG-sound (var (suc i)) x = x
fixG-sound (□ G) (□ x) = □ (fixG-sound (! G) x)

fixG-complete : ∀{G₀} G → ⟦ (⟦ Γ ⊢ fixG G₀ ⟧ ∷ Γ) ⊢ G ⟧ w → ⟦ Γ ⊢ fixG′ G₀ G ⟧ w 
fixG-complete ε x = x
fixG-complete (‵ x₁) x = x
fixG-complete (G₁ ∪ G₂) (inl x) = inl (fixG-complete G₁ x)
fixG-complete (G₁ ∪ G₂) (inr x) = inr (fixG-complete G₂ x)
fixG-complete (G₁ ∙ G₂) (u , v , refl , x , y) = u , v , refl , fixG-complete G₁ x , fixG-complete G₂ y
fixG-complete (var zero) x = □ x
fixG-complete (var (suc i)) x = x
fixG-complete (□ G) (□ x) = □ (fixG-complete (! G) x) 

-- Using this fixed point we can define a finite syntactic representation of grammars,
-- which are indexed by their corresponding (possibly) infinite grammar representation:

data DecGram (n : ℕ) : Gram n → Set₁ where
    ∅ : DecGram n ∅
    ε : DecGram n ε
    ‵_ : (c : Tok) → DecGram n (‵ c)
    _∪_ : DecGram n G₁ → DecGram n G₂ → DecGram n (G₁ ∪ G₂)
    _∙_ : DecGram n G₁ → DecGram n G₂ → DecGram n (G₁ ∙ G₂)
    var : (i : Fin n) → DecGram n (var i)
    μ : DecGram (suc n) G → DecGram n (fixG G)

expr′ : DecGram n _
expr′ = μ (‵ x ∪ var zero ∙ ‵ + ∙ var zero) where open Tok

_⊎?_ : Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎? y = yes (inl x)
no x ⊎? yes x₁ = yes (inr x₁)
no x ⊎? no x₁ = no (λ { (inl y) → x y ; (inr y) → x₁ y })

_×?_ : Dec A → Dec B → Dec (A × B)
yes x ×? yes x₁ = yes (x , x₁)
yes x ×? no x₁ = no (λ z → x₁ (_×_.pr z))
no x ×? y = no (λ z → x (_×_.pl z))

νfix-to : ∀ {G₀} G → ν⟦ (⟦ [] ⊢ ∅ ⟧ ∷ Γ) ⊢ G ⟧ → ν⟦ Γ ⊢ fixG′ G₀ G ⟧
νfix-to ε _ = tt
νfix-to (G₁ ∪ G₂) (inl x) = inl (νfix-to G₁ x)
νfix-to (G₁ ∪ G₂) (inr x) = inr (νfix-to G₂ x)
νfix-to (G₁ ∙ G₂) (pl , pr) = νfix-to G₁ pl , νfix-to G₂ pr
νfix-to (var (suc i)) x = x
νfix-to (□ G) (□ x) = □ (νfix-to (! G) x)

⊎mapl : ∀{C} → (A → C) → A ⊎ B → C ⊎ B
⊎mapl f (inl x) = inl (f x)
⊎mapl f (inr x) = inr x

⊎lift2l : ∀{C D} → (A → B → C) → A ⊎ D → B ⊎ D → C ⊎ D
⊎lift2l f (inl x) (inl x₁) = inl (f x x₁)
⊎lift2l f (inl x) (inr x₁) = inr x₁
⊎lift2l f (inr x) y = inr x

⊎collapse : A ⊎ A → A
⊎collapse (inl x) = x
⊎collapse (inr x) = x

νfix-from : ∀ {G₀} G → ν⟦ Γ ⊢ fixG′ G₀ G ⟧ → ν⟦ (⟦ [] ⊢ ∅ ⟧ ∷ Γ) ⊢ G ⟧ ⊎ ν⟦ (⟦ [] ⊢ ∅ ⟧ ∷ Γ) ⊢ G₀ ⟧
νfix-from ε _ = inl tt
νfix-from (G ∪ G₁) (inl x) = ⊎mapl inl (νfix-from G x)
νfix-from (G ∪ G₁) (inr x) = ⊎mapl inr (νfix-from G₁ x)
νfix-from (G ∙ G₁) (pl , pr) = ⊎lift2l _,_ (νfix-from G pl) (νfix-from G₁ pr)
νfix-from {G₀ = G₀} (var zero) (□ x) = inr (⊎collapse (νfix-from G₀ x))
νfix-from (var (suc i)) x = inl x
νfix-from (□ G) (□ x) = ⊎mapl □ (νfix-from (! G) x)

νfix : ∀ G → ν⟦ (⟦ [] ⊢ ∅ ⟧ ∷ Γ) ⊢ G ⟧ ↔ ν⟦ Γ ⊢ fixG G ⟧
to (νfix G) = νfix-to G
from (νfix G) x = ⊎collapse (νfix-from G x)

ν?′ : DecGram n G → ((i : Fin n) → Dec (ν (lookup Γ i))) → Dec ν⟦ Γ ⊢ G ⟧
ν?′ ∅ Γ = no (λ z → z)
ν?′ ε Γ = yes tt
ν?′ (‵ c) Γ = no (λ z → z)
ν?′ (G₁ ∪ G₂) Γ = ν?′ G₁ Γ ⊎? ν?′ G₂ Γ
ν?′ (G₁ ∙ G₂) Γ = ν?′ G₁ Γ ×? ν?′ G₂ Γ
ν?′ (var i) Γ = Γ i
ν?′ (μ {G = G′} G) Γ = mapDec (νfix G′) (ν?′ G (λ { zero → no λ () ; (suc i) → Γ i })) 

-- ↔sym : A ↔ B → B ↔ A
-- to (↔sym bi) = from bi
-- from (↔sym bi) = to bi

ν? : DecGram n G → ((i : Fin n) → Dec (ν (lookup Γ i))) → Dec (ν ⟦ Γ ⊢ G ⟧)
ν? {G = G} DG Γ = mapDec (νG-correct G) (ν?′ DG Γ)
