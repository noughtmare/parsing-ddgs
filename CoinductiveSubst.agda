{-# OPTIONS --guardedness --safe #-}

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

record ∃ {A : Set} (f : A → Set) : Set where
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

-- data El {A : Set ℓ} : List A → Set ℓ where
--   here : ∀{x xs} → El (x ∷ xs)
--   there : ∀{x xs} → El xs → El (x ∷ xs)

Lang : Set₁
Lang = List Tok → Set

ν : Lang → Set
ν ℒ = ℒ []

δ : Tok → Lang → Lang
(δ c ℒ) w = ℒ (c ∷ w)

mutual
    data Gram (n : ℕ) : Set₁ where
        ∅ : Gram n
        ε : Gram n
        ‵_ : (c : Tok) → Gram n
        _·_ : (A : Set) → (G : Gram n) → Gram n
        _∪_ : (G₁ G₂ : Gram n) → Gram n
        _∙_ : (G₁ G₂ : Gram n) → Gram n
        var : (i : Fin n) → Gram n
        □ : (□G : □Gram n) → Gram n

    infix 23 ‵_
    infixr 22 _∙_
    infixr 21 _∪_

    record □Gram (n : ℕ) : Set₁ where
        coinductive
        constructor delay
        field ! : Gram n

open □Gram using (!)

substG : Gram n → (Fin n → Gram m) → Gram m

subst□G : □Gram n → (Fin n → Gram m) → □Gram m
subst□G □G k .! = substG (□G .!) k

substG ∅ k = ∅
substG ε k = ε
substG (‵ c) k = ‵ c
substG (A · G) k = A · substG G k
substG (G₁ ∪ G₂) k = substG G₁ k ∪ substG G₂ k
substG (G₁ ∙ G₂) k = substG G₁ k ∙ substG G₂ k
substG (var i) k = k i
substG (□ □G) k = □ (subst□G □G k)

zero← : Gram n → Fin (suc n) → Gram n
zero← G zero = G
zero← G (suc i) = var i

substG₀ : Gram (suc n) → Gram n → Gram n
substG₀ G G′ = substG G (zero← G′)

_∘_ : (B -> C) -> (A -> B) -> A -> C
(f ∘ g) x = f (g x)

renameG : (Fin n → Fin m) → Gram n → Gram m
renameG f G = substG G (var ∘ f)

variable
    Γ Γ′ Γ₁ Γ₂ : Vec Lang n
    G G′ G₁ G₂ : Gram n
    u v w : List Tok
    □G : □Gram n
    c : Tok
    ℒ : Lang

cong : ∀{x y} (f : A → B) → x ≡ y → f x ≡ f y
cong _ refl = refl

cong₂ : ∀{x y z w} (f : A → B → C) → x ≡ y → z ≡ w → f x z ≡ f y w
cong₂ _ refl refl = refl

module _ where
    open □Gram

    left-right : Gram n
    left-right = let left-right = □ λ { .! → left-right } in
        left-right ∙ left-right

    expr : Gram n
    expr = let open T; expr = □ λ { .! → expr } in
        ‵ x ∪ expr ∙ ‵ + ∙ expr

⟦_⊢_⟧ : (Γ : Vec Lang n) → Gram n → Lang

data □⟦_⊢_⟧ (Γ : Vec Lang n) (□G : □Gram n) (w : List Tok) : Set where
  □ : ⟦ Γ ⊢ ! □G ⟧ w → □⟦ Γ ⊢ □G ⟧ w

⟦ _ ⊢ ∅ ⟧ _ = ⊥
⟦ _ ⊢ ε ⟧ w = w ≡ []
⟦ _ ⊢ ‵ c ⟧ w = w ≡ c ∷ []
⟦ Γ ⊢ A · G ⟧ w = A × ⟦ Γ ⊢ G ⟧ w
⟦ Γ ⊢ G₁ ∪ G₂ ⟧ w = ⟦ Γ ⊢ G₁ ⟧ w ⊎ ⟦ Γ ⊢ G₂ ⟧ w
⟦ Γ ⊢ G₁ ∙ G₂ ⟧ w = ∃ λ u → ∃ λ v → (w ≡ u ++ v) × ⟦ Γ ⊢ G₁ ⟧ u × ⟦ Γ ⊢ G₂ ⟧ v
⟦ Γ ⊢ var i ⟧ w = lookup Γ i w
⟦ Γ ⊢ □ □G ⟧ w = □⟦ Γ ⊢ □G ⟧ w

⟦_⟧ : Gram zero → Lang
⟦ G ⟧ = ⟦ [] ⊢ G ⟧

mapVec : (A → B) → Vec A n → Vec B n
mapVec f [] = []
mapVec f (x ∷ xs) = f x ∷ mapVec f xs

record _↔_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
open _↔_

⊢subst : (k : Fin n → Gram m) (foo : ∀ {w} i → lookup Γ′ i w ↔ ⟦ Γ ⊢ k i ⟧ w) (G : Gram n) → ⟦ Γ′ ⊢ G ⟧ w ↔ ⟦ Γ ⊢ substG G k ⟧ w
⊢subst k f ε .to x = x
⊢subst k f (‵ c) .to x = x
⊢subst k f (A · G) .to (x , y) = x , ⊢subst k f G .to y
⊢subst k f (G ∪ G₁) .to (inl x) = inl (⊢subst k f G .to x)
⊢subst k f (G ∪ G₁) .to (inr x) = inr (⊢subst k f G₁ .to x)
⊢subst k f (G ∙ G₁) .to (u , v , refl , x , y) = u , v , refl , ⊢subst k f G .to x , ⊢subst k f G₁ .to y
⊢subst k f (var i) .to x = f i .to x
⊢subst k f (□ □G) .to (□ x) = □ (⊢subst k f (□G .!) .to x)
⊢subst k f ε .from x = x
⊢subst k f (‵ c) .from x = x
⊢subst k f (A · G) .from (pl₁ , pr₁) = pl₁ , ⊢subst k f G .from pr₁
⊢subst k f (G ∪ G₁) .from (inl x) = inl (⊢subst k f G .from x)
⊢subst k f (G ∪ G₁) .from (inr x) = inr (⊢subst k f G₁ .from x)
⊢subst k f (G ∙ G₁) .from (u , v , refl , x , y) = u , v , refl , ⊢subst k f G .from x , ⊢subst k f G₁ .from y
⊢subst k f (var i) .from x = f i .from x
⊢subst k f (□ □G) .from (□ x) = □ (⊢subst k f (□G .!) .from x)

⊢subst₀ : (G : Gram _) → ⟦ ⟦ Γ ⊢ G′ ⟧ ∷ Γ ⊢ G ⟧ w → ⟦ Γ ⊢ substG₀ G G′ ⟧ w
⊢subst₀ ε x = x
⊢subst₀ (‵ c) x = x
⊢subst₀ {G′ = G′} (A · G) (pl , pr) = pl , ⊢subst₀ G pr
⊢subst₀ (G ∪ G₁) (inl x) = inl (⊢subst₀ G x)
⊢subst₀ (G ∪ G₁) (inr x) = inr (⊢subst₀ G₁ x)
⊢subst₀ (G ∙ G₁) (u , v , refl , x , y) = u , v , refl , ⊢subst₀ G x , ⊢subst₀ G₁ y
⊢subst₀ (var zero) x = x
⊢subst₀ (var (suc i)) x = x
⊢subst₀ (□ □G) (□ x) = □ (⊢subst₀ (□G .!) x)

⊢subst₀′ : (G : Gram _) → ⟦ Γ ⊢ substG₀ G G′ ⟧ w → ⟦ ⟦ Γ ⊢ G′ ⟧ ∷ Γ ⊢ G ⟧ w
⊢subst₀′ ε x = x
⊢subst₀′ (‵ c) x = x
⊢subst₀′ {G′ = G′} (A · G) (pl , pr) = pl , ⊢subst₀′ G pr
⊢subst₀′ (G ∪ G₁) (inl x) = inl (⊢subst₀′ G x)
⊢subst₀′ (G ∪ G₁) (inr x) = inr (⊢subst₀′ G₁ x)
⊢subst₀′ (G ∙ G₁) (u , v , refl , x , y) = u , v , refl , ⊢subst₀′ G x , ⊢subst₀′ G₁ y
⊢subst₀′ (var zero) x = x
⊢subst₀′ (var (suc i)) x = x
⊢subst₀′ (□ □G) (□ x) = □ (⊢subst₀′ (□G .!) x)

x+x+x : ⟦ Γ ⊢ expr ⟧ (let open T in x ∷ + ∷ x ∷ + ∷ x ∷ [])
x+x+x = inr (_ , _ , refl , □ (inl refl) , _ , _ , refl , refl , □ (inr (_ , _ , refl , □ (inl refl) , _ , _ , refl , refl , □ (inl refl))))


mapDec : (A ↔ B) → Dec A → Dec B
mapDec bi (yes x) = yes (to bi x)
mapDec bi (no ¬x) = no (λ y → ¬x (from bi y))

data Bool : Set where
  false : Bool
  true : Bool

data ⊤ : Set where
  tt : ⊤

variable Γν : Vec Set n

ν⟦_⊢_⟧ : (Γν : Vec Set n) → Gram n → Set

data ν□G (□G : □Gram n) (Γν : Vec Set n) : Set where
  □ : ν⟦ Γν ⊢ ! □G ⟧ → ν□G □G Γν

ν⟦ Γ ⊢ ∅ ⟧ = ⊥
ν⟦ Γ ⊢ ε ⟧ = ⊤
ν⟦ Γ ⊢ ‵ c ⟧ = ⊥
ν⟦ Γ ⊢ A · G ⟧ = A × ν⟦ Γ ⊢ G ⟧
ν⟦ Γ ⊢ G₁ ∪ G₂ ⟧ = ν⟦ Γ ⊢ G₁ ⟧ ⊎ ν⟦ Γ ⊢ G₂ ⟧
ν⟦ Γ ⊢ G₁ ∙ G₂ ⟧ = ν⟦ Γ ⊢ G₁ ⟧ × ν⟦ Γ ⊢ G₂ ⟧
ν⟦ Γ ⊢ var i ⟧ = lookup Γ i
ν⟦ Γ ⊢ □ □G ⟧ = ν□G □G Γ

↔refl : A ↔ A
to ↔refl x = x
from ↔refl x = x

Γν-correct : Vec Lang n → Vec Set n → Set
Γν-correct Γ Γν = ∀ i → lookup Γν i ↔ ν (lookup Γ i)

lookup-map : (f : A → B) (v : Vec A n) (i : Fin n) → lookup (mapVec f v) i ≡ f (lookup v i)
lookup-map f (x ∷ v) zero = refl
lookup-map f (x ∷ v) (suc i) = lookup-map f v i

the-Γν : Vec (Gram m) n → Vec Lang m → Vec Set n
the-Γν Γ Γ′ = mapVec (λ G → ν ⟦ Γ′ ⊢ G ⟧) Γ

the-Γν-correct : (Γ : Vec (Gram m) n) → Γν-correct (mapVec (λ G → ⟦ Γ′ ⊢ G ⟧) Γ) (the-Γν Γ Γ′)
the-Γν-correct (G ∷ Γ) zero = ↔refl
the-Γν-correct (G ∷ Γ) (suc i) = the-Γν-correct Γ i

νG-sound : (G : Gram n) → Γν-correct Γ Γν → ν⟦ Γν ⊢ G ⟧ → ν ⟦ Γ ⊢ G ⟧
νG-sound ε _ x = refl
νG-sound (A · G) ev (x , y) = x , νG-sound G ev y
νG-sound (G₁ ∪ G₂) ev (inl x) = inl (νG-sound G₁ ev x)
νG-sound (G₁ ∪ G₂) ev (inr y) = inr (νG-sound G₂ ev y)
νG-sound (G₁ ∙ G₂) ev (pl , pr) = [] , [] , refl , νG-sound G₁ ev pl , νG-sound G₂ ev pr
νG-sound (var i) ev x = to (ev i) x
νG-sound (□ □G) ev (□ x) = □ (νG-sound (! □G) ev x)

νG-complete : (G : Gram n) → Γν-correct Γ Γν → ν ⟦ Γ ⊢ G ⟧ → ν⟦ Γν ⊢ G ⟧
νG-complete ε _ x = tt
νG-complete (A · G) ev (x , y) = x , νG-complete G ev y
νG-complete (G ∪ G₁) ev (inl x) = inl (νG-complete G ev x)
νG-complete (G ∪ G₁) ev (inr x) = inr (νG-complete G₁ ev x)
νG-complete (G ∙ G₁) ev ([] , [] , refl , pl , pr) = νG-complete G ev pl , νG-complete G₁ ev pr
νG-complete (var i) ev x = from (ev i) x
νG-complete (□ □G) ev (□ x) = □ (νG-complete (! □G) ev x)

νG-correct : (G : Gram n) → Γν-correct Γ Γν → ν⟦ Γν ⊢ G ⟧ ↔ ν ⟦ Γ ⊢ G ⟧
to (νG-correct G bi) = νG-sound G bi
from (νG-correct G bi) = νG-complete G bi

const : A → B → A
const x _ = x

fixG : Gram (suc n) → Gram n

fixG′ : Gram (suc n) → Gram (suc n) → Gram n
fixG′ G₀ ∅ = ∅
fixG′ G₀ ε = ε
fixG′ G₀ (‵ c) = ‵ c
fixG′ G₀ (A · G) = A · fixG′ G₀ G
fixG′ G₀ (G₁ ∪ G₂) = fixG′ G₀ G₁ ∪ fixG′ G₀ G₂
fixG′ G₀ (G₁ ∙ G₂) = fixG′ G₀ G₁ ∙ fixG′ G₀ G₂
fixG′ G₀ (var zero) = □ (λ { .! → fixG G₀ }) -- this is the special case
fixG′ G₀ (var (suc i)) = var i
fixG′ G₀ (□ G) = □ (λ { .! → fixG′ G₀ (! G) })

fixG {n = n} G = fixG′ G G

-- Is fixG really a fixed point? Yes:

unroll : ∀ G → ⟦ Γ ⊢ fixG G ⟧ w → ⟦ (⟦ Γ ⊢ fixG G ⟧ ∷ Γ) ⊢ G ⟧ w

unroll′ : ∀ G {G₀} → ⟦ Γ ⊢ fixG′ G₀ G ⟧ w → ⟦ (⟦ Γ ⊢ fixG G₀ ⟧ ∷ Γ) ⊢ G ⟧ w
unroll′ ε x = x
unroll′ (‵ x₁) x = x
unroll′ (A · G) (x , y) = x , unroll′ G y
unroll′ (G₁ ∪ G₂) (inl x) = inl (unroll′ G₁ x)
unroll′ (G₁ ∪ G₂) (inr x) = inr (unroll′ G₂ x)
unroll′ (G₁ ∙ G₂) (u , v , refl , x , y) = u , v , refl , unroll′ G₁ x , unroll′ G₂ y
unroll′ (var zero) (□ x) = x
unroll′ (var (suc i)) x = x
unroll′ (□ G) (□ x) = □ (unroll′ (! G) x)

unroll G = unroll′ G

roll : ∀ G → ⟦ (⟦ Γ ⊢ fixG G ⟧ ∷ Γ) ⊢ G ⟧ w → ⟦ Γ ⊢ fixG G ⟧ w 

roll′ : ∀{G₀} G → ⟦ (⟦ Γ ⊢ fixG G₀ ⟧ ∷ Γ) ⊢ G ⟧ w → ⟦ Γ ⊢ fixG′ G₀ G ⟧ w 
roll′ ε x = x
roll′ (‵ x₁) x = x
roll′ (A · G) (x , y) = x , roll′ G y
roll′ (G₁ ∪ G₂) (inl x) = inl (roll′ G₁ x)
roll′ (G₁ ∪ G₂) (inr x) = inr (roll′ G₂ x)
roll′ (G₁ ∙ G₂) (u , v , refl , x , y) = u , v , refl , roll′ G₁ x , roll′ G₂ y
roll′ (var zero) x = □ x
roll′ (var (suc i)) x = x
roll′ (□ G) (□ x) = □ (roll′ (! G) x) 

roll G = roll′ G

mapFix : ∀ G {G′} → (∀{Γ w} → ⟦ Γ ⊢ G ⟧ w → ⟦ Γ ⊢ G′ ⟧ w) → ⟦ Γ ⊢ fixG G ⟧ w → ⟦ Γ ⊢ fixG G′ ⟧ w

mapFixi : ∀ G {G₀ G′} → (∀{ℒ w} → ⟦ ℒ ∷ Γ ⊢ G ⟧ w → ⟦ ℒ ∷ Γ ⊢ G′ ⟧ w) → ⟦ Γ ⊢ fixG′ G₀ G ⟧ w → ⟦ Γ ⊢ fixG′ G₀ G′ ⟧ w
mapFixi G {G₀} {G′} f x = roll′ G′ (f (unroll′ G x))

mapFixo : ∀{G₀ G₀′} (G : Gram _) → (∀{Γ w} → ⟦ Γ ⊢ G₀ ⟧ w → ⟦ Γ ⊢ G₀′ ⟧ w) → ⟦ Γ ⊢ fixG′ G₀ G ⟧ w → ⟦ Γ ⊢ fixG′ G₀′ G ⟧ w
mapFixo ε f x = x
mapFixo (‵ x₁) f x = x
mapFixo (_ · G) f (x , y) = x , mapFixo G f y
mapFixo (G ∪ G₁) f (inl x) = inl (mapFixo G f x)
mapFixo (G ∪ G₁) f (inr x) = inr (mapFixo G₁ f x)
mapFixo (G ∙ G₁) f (u , v , refl , x , y) = u , v , refl , mapFixo G f x , mapFixo G₁ f y
mapFixo {G₀ = G₀} {G₀′} (var zero) f (□ x) = □ (mapFix G₀ {G₀′} f x)
mapFixo (var (suc i)) f x = x
mapFixo (□ G) f (□ x) = □ (mapFixo (! G) f x)

mapFix G {G′} f x = mapFixi G {_} {G′} f (mapFixo G f x)

-- Using this fixed point we can define a finite syntactic representation of grammars,
-- which are indexed by their corresponding (possibly) infinite grammar representation:

data DecGram (n : ℕ) : Gram n → Set₁ where
    ∅ : DecGram n ∅
    ε : DecGram n ε
    ‵_ : (c : Tok) → DecGram n (‵ c)
    _·_ : Dec A → DecGram n G → DecGram n (A · G)
    _∪_ : DecGram n G₁ → DecGram n G₂ → DecGram n (G₁ ∪ G₂)
    _∙_ : DecGram n G₁ → DecGram n G₂ → DecGram n (G₁ ∙ G₂)
    var : (i : Fin n) → DecGram n (var i)
    μ : DecGram (suc n) G → DecGram n (fixG G)

-- this needs to be made a constructor, that shouldn't cause problems but is some work
_◃_ : (∀ {Γ} {w} → ⟦ Γ ⊢ G₁ ⟧ w ↔ ⟦ Γ ⊢ G₂ ⟧ w) → DecGram n G₁ → DecGram n G₂
_◃_ = {!!}

consrn : ∀{n m} → (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
consrn f zero = zero
consrn f (suc i) = suc (f i)

conssub : (Fin n → Gram m) → Fin (suc n) → Gram (suc m)
conssub k zero = var zero
conssub k (suc i) = renameG suc (k i)

↔cong : (f : Set → Set) (map : ∀{X Y : Set} → (X → Y) → f X → f Y) → A ↔ B → f A ↔ f B
↔cong f map bi .to x = map (bi .to) x
↔cong f map bi .from x = map (bi .from) x

↔cong₂ : ∀{A₁ A₂ B₁ B₂} (f : Set → Set → Set) (map : ∀{X₁ X₂ Y₁ Y₂ : Set} → (X₁ → Y₁) → (X₂ → Y₂) → f X₁ X₂ → f Y₁ Y₂) → A₁ ↔ B₁ → A₂ ↔ B₂ → f A₁ A₂ ↔ f B₁ B₂
↔cong₂ f map bi₁ bi₂ .to x = map (bi₁ .to) (bi₂ .to) x
↔cong₂ f map bi₁ bi₂ .from x = map (bi₁ .from) (bi₂ .from) x

subrn : (G : Gram _) (f : Fin n → Fin m) → ⟦ Γ ⊢ substG G (conssub (var ∘ f)) ⟧ w ↔ ⟦ Γ ⊢ substG G (var ∘ consrn f) ⟧ w
subrn ∅ f .to ()
subrn ε f .to x = x
subrn (‵ c) f .to x = x
subrn (A · G) f .to (pl₁ , pr₁) = pl₁ , subrn G f .to pr₁
subrn (G₁ ∪ G₂) f .to (inl x) = inl (subrn G₁ f .to x)
subrn (G₁ ∪ G₂) f .to (inr x) = inr (subrn G₂ f .to x)
subrn (G₁ ∙ G₂) f .to (u , v , refl , x , y) = u , v , refl , subrn G₁ f .to x , subrn G₂ f .to y
subrn (□ □G) f .to (□ x) = □ (subrn (□G .!) f .to x)
subrn ∅ f .from ()
subrn ε f .from x = x
subrn (‵ c) f .from x = x
subrn (A · G) f .from (pl₁ , pr₁) = pl₁ , subrn G f .from pr₁
subrn (G₁ ∪ G₂) f .from (inl x) = inl (subrn G₁ f .from x)
subrn (G₁ ∪ G₂) f .from (inr x) = inr (subrn G₂ f .from x)
subrn (G₁ ∙ G₂) f .from (u , v , refl , x , y) = u , v , refl , subrn G₁ f .from x , subrn G₂ f .from y
subrn (□ □G) f .from (□ x) = □ (subrn (□G .!) f .from x)
-- special cases:
subrn (var zero) f = ↔refl
subrn (var (suc i)) f = ↔refl

renamesuc : ∀ G → ⟦ ℒ ∷ Γ ⊢ renameG suc G ⟧ w ↔ ⟦ Γ ⊢ G ⟧ w
renamesuc ε .to x = x
renamesuc (‵ c) .to x = x
renamesuc (A · G) .to (pl₁ , pr₁) = pl₁ , renamesuc G .to pr₁
renamesuc (G ∪ G₁) .to (inl x) = inl (renamesuc G .to x)
renamesuc (G ∪ G₁) .to (inr x) = inr (renamesuc G₁ .to x)
renamesuc (G ∙ G₁) .to (u , v , refl , x , y) = u , v , refl , renamesuc G .to x , renamesuc G₁ .to y
renamesuc (var i) .to x = x
renamesuc (□ □G) .to (□ x) = □ (renamesuc (□G .!) .to x)

renamesuc ε .from x = x
renamesuc (‵ c) .from x = x
renamesuc (A · G) .from (pl₁ , pr₁) = pl₁ , renamesuc G .from pr₁
renamesuc (G ∪ G₁) .from (inl x) = inl (renamesuc G .from x)
renamesuc (G ∪ G₁) .from (inr x) = inr (renamesuc G₁ .from x)
renamesuc (G ∙ G₁) .from (u , v , refl , x , y) = u , v , refl , renamesuc G .from x , renamesuc G₁ .from y
renamesuc (var i) .from x = x
renamesuc (□ □G) .from (□ x) = □ (renamesuc (□G .!) .from x)

substFixG : ∀{n m} {Γ : Vec Lang m} (G : Gram (suc n)) {G₀ : Gram (suc n)} (k : Fin n → Gram m) → ⟦ Γ ⊢ substG (fixG′ G₀ G) k ⟧ w ↔ ⟦ Γ ⊢ fixG′ (substG G₀ (conssub k)) (substG G (conssub k)) ⟧ w
substFixG ε k .to x = x
substFixG (‵ c) k .to x = x
substFixG (A · G) k .to (x , y) = x , substFixG G k .to y
substFixG (G₁ ∪ G₂) k .to (inl x) = inl (substFixG G₁ k .to x)
substFixG (G₁ ∪ G₂) k .to (inr x) = inr (substFixG G₂ k .to x)
substFixG (G₁ ∙ G₂) k .to (u , v , refl , x , y) = u , v , refl , substFixG G₁ k .to x , substFixG G₂ k . to y
substFixG (var zero) {G₀ = G₀} k .to (□ x) = □ (substFixG G₀ k .to x)
substFixG {n = suc n} (var (suc i)) {G₀} k .to x = roll′ (renameG suc (k i)) (renamesuc (k i) .from x)
substFixG (□ □G) k .to (□ x) = □ (substFixG (□G .!) k .to x)
substFixG ε k .from x = x
substFixG (‵ c) k .from x = x
substFixG (A · G) k .from (pl₁ , pr₁) = pl₁ , substFixG G k .from pr₁
substFixG (G ∪ G₁) k .from (inl x) = inl (substFixG G k .from x)
substFixG (G ∪ G₁) k .from (inr x) = inr (substFixG G₁ k .from x)
substFixG (G ∙ G₁) k .from (u , v , refl , x , y) = u , v , refl , substFixG G k .from x , substFixG G₁ k .from y
substFixG (var zero) {G₀} k .from (□ x) = □ (substFixG G₀ k .from x)
substFixG {n = suc n} (var (suc i)) {G₀} k .from x = renamesuc (k i) .to (unroll′ (renameG suc (k i)) {substG G₀ (conssub k)} x)
substFixG (□ □G) k .from (□ x) = □ (substFixG (□G .!) k .from x)

renameFixG : ∀{n m} {Γ : Vec Lang m} (G : Gram (suc n)) (f : Fin n → Fin m) → ⟦ Γ ⊢ renameG f (fixG G) ⟧ w ↔ ⟦ Γ ⊢ fixG (renameG (consrn f) G) ⟧ w
renameFixG {n = n} {m} {Γ} G f .to x = mapFix (substG G (conssub (var ∘ f))) {substG G (var ∘ consrn f)} (subrn G f .to) (substFixG {Γ = Γ} G {G} (var ∘ f) .to x)
renameFixG {n = n} {m} {Γ} G f .from x = substFixG {Γ = Γ} G {G} (var ∘ f) .from (mapFix (substG G (var ∘ consrn f)) {substG G (conssub (var ∘ f))} (subrn G f .from) x)

↔sym : A ↔ B → B ↔ A
to (↔sym bi) = from bi
from (↔sym bi) = to bi

renameDG : ∀{n m G} → (f : Fin n → Fin m) → DecGram n G → DecGram m (renameG f G)
renameDG f ∅ = ∅
renameDG f ε = ε
renameDG f (‵ c) = ‵ c
renameDG f (x · DG) = x · renameDG f DG
renameDG f (DG ∪ DG₁) = renameDG f DG ∪ renameDG f DG₁
renameDG f (DG ∙ DG₁) = renameDG f DG ∙ renameDG f DG₁
renameDG f (var i) = var (f i)
renameDG f (μ {G = G} DG) = (↔sym (renameFixG G f)) ◃ μ (renameDG (consrn f) DG)

subst : {A : Set ℓ₁} {x y : A} (P : A → Set ℓ₂) → (x ≡ y) → P x → P y
subst _ refl x = x

fixGsuc-to : (G : Gram n) {G₀ : Gram _} → ⟦ Γ ⊢ fixG′ G₀ (renameG suc G) ⟧ w → ⟦ Γ ⊢ G ⟧ w
fixGsuc-to G x = renamesuc G .to (unroll′ (renameG suc G) x)

fixGsuc-from : (G : Gram n) {G₀ : Gram _} → ⟦ Γ ⊢ G ⟧ w → ⟦ Γ ⊢ fixG′ G₀ (renameG suc G) ⟧ w
fixGsuc-from G x = roll′ (renameG suc G) (renamesuc G .from x)

variable σ : Vec (Gram m) n

substDGμ : (G : Gram _) → ⟦ Γ ⊢ fixG (substG G (lookup (var zero ∷ mapVec (renameG suc) σ))) ⟧ w ↔ ⟦ Γ ⊢ substG (fixG G) (lookup σ) ⟧ w

substDGμ-to : (G : Gram _) {G₀ : Gram _} → ⟦ Γ ⊢ fixG′ (substG G₀ (lookup (var zero ∷ mapVec (renameG suc) σ))) (substG G (lookup (var zero ∷ mapVec (renameG suc) σ))) ⟧ w → ⟦ Γ ⊢ substG (fixG′ G₀ G) (lookup σ) ⟧ w
substDGμ-to ε x = x
substDGμ-to (‵ c) x = x
substDGμ-to (A · G) (x , y) = x , substDGμ-to G y 
substDGμ-to (G ∪ G₁) (inl x) = inl (substDGμ-to G x)
substDGμ-to (G ∪ G₁) (inr x) = inr (substDGμ-to G₁ x)
substDGμ-to (G ∙ G₁) (u , v , refl , x , y) = u , v , refl , substDGμ-to G x , substDGμ-to G₁ y
substDGμ-to (var zero) {G₀} (□ x) = □ (substDGμ-to G₀ x)
substDGμ-to {σ = σ} (var (suc i)) {G₀} x = fixGsuc-to (lookup σ i) (subst (λ X → ⟦ _ ⊢ fixG′ _ X ⟧ _) (lookup-map (renameG suc) σ i) x)
substDGμ-to (□ □G) (□ x) = □ (substDGμ-to (□G .!) x)

sym : {x y : A} → x ≡ y → y ≡ x
sym refl = refl

substDGμ-from : (G : Gram _) {G₀ : Gram _} → ⟦ Γ ⊢ substG (fixG′ G₀ G) (lookup σ) ⟧ w → ⟦ Γ ⊢ fixG′ (substG G₀ (lookup (var zero ∷ mapVec (renameG suc) σ))) (substG G (lookup (var zero ∷ mapVec (renameG suc) σ))) ⟧ w
substDGμ-from ε x = x
substDGμ-from (‵ c) x = x
substDGμ-from (A · G) (x , y) = x , substDGμ-from G y 
substDGμ-from (G ∪ G₁) (inl x) = inl (substDGμ-from G x)
substDGμ-from (G ∪ G₁) (inr x) = inr (substDGμ-from G₁ x)
substDGμ-from (G ∙ G₁) (u , v , refl , x , y) = u , v , refl , substDGμ-from G x , substDGμ-from G₁ y
substDGμ-from (var zero) {G₀} (□ x) = □ (substDGμ-from G₀ x)
substDGμ-from {σ = σ} (var (suc i)) {G₀} x = subst (λ X → ⟦ _ ⊢ fixG′ _ X ⟧ _) (sym (lookup-map (renameG suc) σ i)) (fixGsuc-from (lookup σ i) x)
substDGμ-from (□ □G) (□ x) = □ (substDGμ-from (□G .!) x)

substDGμ G .to x = substDGμ-to G x
substDGμ G .from x = substDGμ-from G x

substDG : (σ : Vec (Gram m) n) → DecGram n G → ((i : Fin n) → DecGram m (lookup σ i)) → DecGram m (substG G (lookup σ))
substDG σ ∅ k = ∅
substDG σ ε k = ε
substDG σ (‵ c) k = ‵ c
substDG σ (x · G) k = x · substDG σ G k
substDG σ (G ∪ G₁) k = substDG σ G k ∪ substDG σ G₁ k
substDG σ (G ∙ G₁) k = substDG σ G k ∙ substDG σ G₁ k
substDG σ (var i) k = k i
substDG σ (μ {G = G′} G) k = substDGμ G′ ◃ μ (substDG (var zero ∷ mapVec (renameG suc) σ) G λ { zero → var zero ; (suc i) → subst (λ X → DecGram (suc _) X) (sym (lookup-map (renameG suc) σ i)) (renameDG suc (k i)) })

-- example

expr′ : DecGram n _
expr′ = μ (‵ x ∪ var zero ∙ ‵ + ∙ var zero) where open Tok

-- nullability

_⊎?_ : Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎? y = yes (inl x)
no x ⊎? yes x₁ = yes (inr x₁)
no x ⊎? no x₁ = no (λ { (inl y) → x y ; (inr y) → x₁ y })

_×?_ : Dec A → Dec B → Dec (A × B)
yes x ×? yes x₁ = yes (x , x₁)
yes x ×? no x₁ = no (λ z → x₁ (_×_.pr z))
no x ×? y = no (λ z → x (_×_.pl z))

νfix-to : ∀ {G₀} G → ν⟦ (⊥ ∷ Γν) ⊢ G ⟧ → ν⟦ Γν ⊢ fixG′ G₀ G ⟧
νfix-to ε _ = tt
νfix-to (A · G) (x , y) = x , νfix-to G y
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

νfix-from : ∀ {G₀} G → ν⟦ Γν ⊢ fixG′ G₀ G ⟧ → ν⟦ (⊥ ∷ Γν) ⊢ G ⟧ ⊎ ν⟦ (⊥ ∷ Γν) ⊢ G₀ ⟧
νfix-from ε _ = inl tt
νfix-from (A · G) (x , y) = ⊎mapl (x ,_) (νfix-from G y)
νfix-from (G ∪ G₁) (inl x) = ⊎mapl inl (νfix-from G x)
νfix-from (G ∪ G₁) (inr x) = ⊎mapl inr (νfix-from G₁ x)
νfix-from (G ∙ G₁) (pl , pr) = ⊎lift2l _,_ (νfix-from G pl) (νfix-from G₁ pr)
νfix-from {G₀ = G₀} (var zero) (□ x) = inr (⊎collapse (νfix-from G₀ x))
νfix-from (var (suc i)) x = inl x
νfix-from (□ G) (□ x) = ⊎mapl □ (νfix-from (! G) x)

νfix : ∀ G → ν⟦ (⊥ ∷ Γν) ⊢ G ⟧ ↔ ν⟦ Γν ⊢ fixG G ⟧
to (νfix G) = νfix-to G
from (νfix G) x = ⊎collapse (νfix-from G x)

ν?′ : DecGram n G → (∀ i → Dec (lookup Γν i)) → Dec ν⟦ Γν ⊢ G ⟧
ν?′ ∅ Γ = no (λ z → z)
ν?′ ε Γ = yes tt
ν?′ (‵ c) Γ = no (λ z → z)
ν?′ (x · G) Γ = x ×? ν?′ G Γ
ν?′ (G₁ ∪ G₂) Γ = ν?′ G₁ Γ ⊎? ν?′ G₂ Γ
ν?′ (G₁ ∙ G₂) Γ = ν?′ G₁ Γ ×? ν?′ G₂ Γ
ν?′ (var i) Γ = Γ i
ν?′ (μ {G = G′} G) Γ = mapDec (νfix G′) (ν?′ G (λ { zero → no λ () ; (suc i) → Γ i })) 

↔lookup : (f : A → Set) (xs : Vec A n) (i : Fin n) → lookup (mapVec f xs) i ↔ f (lookup xs i)
↔lookup f (x ∷ xs) zero = ↔refl
↔lookup f (x ∷ xs) (suc i) = ↔lookup f xs i

ν?₀ : DecGram zero G → Dec (ν ⟦ G ⟧)

ν? : DecGram n G → (∀ i → Dec (ν (lookup Γ i))) → Dec (ν ⟦ Γ ⊢ G ⟧)
ν? {G = G} {Γ = Γ′} DG Γ = mapDec (νG-correct {Γν = mapVec ν Γ′} G (↔lookup ν Γ′)) (ν?′ DG (λ i → mapDec (↔sym (↔lookup ν Γ′ i)) (Γ i)))

ν?₀ G = ν? G λ ()

-- derivative

δ⟦_⟧₀ : Gram zero → Tok → Gram zero

δ⟦_,_,_⊢_⟧ : Vec Set n → Vec (Gram m) n → Vec (Gram m) n → Gram n → Tok → Gram m
δ⟦ Γν , Γδ , σ ⊢ ∅ ⟧ _ = ∅
δ⟦ Γν , Γδ , σ ⊢ ε ⟧ _ = ∅
δ⟦ Γν , Γδ , σ ⊢ ‵ c′ ⟧ c with c′ ≟ c
... | yes _ = ε
... | no _ = ∅
δ⟦ Γν , Γδ , σ ⊢ A · G ⟧ c = A · δ⟦ Γν , Γδ , σ ⊢ G ⟧ c
δ⟦ Γν , Γδ , σ ⊢ G₁ ∪ G₂ ⟧ c = δ⟦ Γν , Γδ , σ ⊢ G₁ ⟧ c ∪ δ⟦ Γν , Γδ , σ ⊢ G₂ ⟧ c
δ⟦ Γν , Γδ , σ ⊢ G₁ ∙ G₂ ⟧ c = δ⟦ Γν , Γδ , σ ⊢ G₁ ⟧ c ∙ substG G₂ (lookup σ) ∪ (ν⟦ Γν ⊢ G₁ ⟧ · δ⟦ Γν , Γδ , σ ⊢ G₂ ⟧ c)
δ⟦ Γν , Γδ , σ ⊢ var i ⟧ c = lookup Γδ i
δ⟦ Γν , Γδ , σ ⊢ □ G ⟧ c = □ (λ { .! → δ⟦ Γν , Γδ , σ ⊢ ! G ⟧ c })

δ⟦ G ⟧₀ = δ⟦ [] , [] , [] ⊢ G ⟧

variable Γδ : Vec (Gram m) n

Γδ-correct : Vec Lang n → Vec Lang m → Tok → Vec (Gram m) n → Set
Γδ-correct Γ Γ′ c Γδ = ∀ {w} i → ⟦ Γ′ ⊢ lookup Γδ i ⟧ w ↔ δ c (lookup Γ i) w

data AllVec {A : Set ℓ} (P : A → Set) : {n : ℕ} (xs : Vec A n) → Set ℓ where
  [] : AllVec P []
  _∷_ : ∀{x} {xs : Vec A n} → P x → AllVec P xs → AllVec P (x ∷ xs)

tabulate : ((i : Fin n) → A) → Vec A n
tabulate {zero} f = []
tabulate {suc n} f = f zero ∷ tabulate {n} (f ∘ suc)

σ-correct : Vec Lang n → Vec Lang m → Vec (Gram m) n → Set
σ-correct Γ Γ′ σ = ∀ {w} i → ⟦ Γ′ ⊢ lookup σ i ⟧ w ↔ lookup Γ i w

the-σ : (Γ : Vec (Gram m) n) (Γ′ : Vec Lang m) → Vec (Gram m) n
the-σ Γ _ = Γ

the-σ-correct : (Γ : Vec (Gram m) n) (Γ′ : Vec Lang m) → σ-correct (mapVec (λ G → ⟦ Γ′ ⊢ G ⟧) Γ) Γ′ (the-σ Γ Γ′)
the-σ-correct (ℒ ∷ Γ) Γ′ zero = ↔refl
the-σ-correct (ℒ ∷ Γ) Γ′ (suc i) = the-σ-correct Γ Γ′ i

σ-corollary : (σ : Vec (Gram m) n) → σ-correct Γ Γ′ σ → (G : Gram n) → ⟦ Γ′ ⊢ substG G (lookup σ) ⟧ w ↔ ⟦ Γ ⊢ G ⟧ w
σ-corollary σ σc ε .to x = x
σ-corollary σ σc (‵ c) .to x = x
σ-corollary σ σc (A · G) .to (x , y) = x , σ-corollary σ σc  G .to y
σ-corollary σ σc (G ∪ G₁) .to (inl x) = inl (σ-corollary σ σc G .to x)
σ-corollary σ σc (G ∪ G₁) .to (inr x) = inr (σ-corollary σ σc G₁ .to x)
σ-corollary σ σc (G ∙ G₁) .to (u , v , refl , x , y) = u , v , refl , σ-corollary σ σc G .to x , σ-corollary σ σc G₁ .to y
σ-corollary σ σc (var i) .to x = σc i .to x
σ-corollary σ σc (□ □G) .to (□ x) = □ (σ-corollary σ σc (□G .!) .to x)
σ-corollary σ σc ε .from x = x
σ-corollary σ σc (‵ c) .from x = x
σ-corollary σ σc (A · G) .from (x , y) = x , σ-corollary σ σc  G .from y
σ-corollary σ σc (G ∪ G₁) .from (inl x) = inl (σ-corollary σ σc G .from x)
σ-corollary σ σc (G ∪ G₁) .from (inr x) = inr (σ-corollary σ σc G₁ .from x)
σ-corollary σ σc (G ∙ G₁) .from (u , v , refl , x , y) = u , v , refl , σ-corollary σ σc G .from x , σ-corollary σ σc G₁ .from y
σ-corollary σ σc (var i) .from x = σc i .from x
σ-corollary σ σc (□ □G) .from (□ x) = □ (σ-corollary σ σc (□G .!) .from x)

δG-sound : Γν-correct Γ Γν → Γδ-correct Γ Γ′ c Γδ → σ-correct Γ Γ′ σ → (G : Gram n) → ⟦ Γ′ ⊢ δ⟦ Γν , Γδ , σ ⊢ G ⟧ c ⟧ w → δ c ⟦ Γ ⊢ G ⟧ w
δG-sound {c = c} Γν Γδ σ (‵ c′) x with c′ ≟ c
δG-sound {c = c} Γν Γδ σ (‵ c) refl | yes refl = refl
δG-sound {c = c} Γν Γδ σ (‵ c′) () | no _
δG-sound Γν Γδ σ (A · G) (pl , pr) = pl , δG-sound Γν Γδ σ G pr
δG-sound Γν Γδ σ (G ∪ G₁) (inl x) = inl (δG-sound Γν Γδ σ G x)
δG-sound Γν Γδ σ (G ∪ G₁) (inr x) = inr (δG-sound Γν Γδ σ G₁ x)
δG-sound {σ = σ′} Γν Γδ σ (G ∙ G₁) (inl (u , v , refl , x , y)) = (_ ∷ u) , v , refl , δG-sound Γν Γδ σ G x , σ-corollary σ′ σ G₁ .to y
δG-sound Γν Γδ σ (G ∙ G₁) (inr (x , y)) = [] , (_ ∷ _) , refl , νG-sound G Γν x , δG-sound Γν Γδ σ G₁ y
δG-sound Γν Γδ σ (var i) x = to (Γδ i) x
δG-sound Γν Γδ σ (□ G) (□ x) = □ (δG-sound Γν Γδ σ (G .!) x)

δG-complete : Γν-correct Γ Γν → Γδ-correct Γ Γ′ c Γδ → σ-correct Γ Γ′ σ → (G : Gram n) → δ c ⟦ Γ ⊢ G ⟧ w → ⟦ Γ′ ⊢ (δ⟦ Γν , Γδ , σ ⊢ G ⟧ c) ⟧ w 
δG-complete {c = c} Γν Γδ σ (‵ c′) x with c′ ≟ c
δG-complete {c = c} Γν Γδ σ (‵ c) refl | yes refl = refl
δG-complete {c = .c′} Γν Γδ σ (‵ c′) refl | no ¬x = ¬x refl
δG-complete Γν Γδ σ (A · G) (pl , pr) = pl , δG-complete Γν Γδ σ G pr
δG-complete Γν Γδ σ (G ∪ G₁) (inl x) = inl (δG-complete Γν Γδ σ G x)
δG-complete Γν Γδ σ (G ∪ G₁) (inr x) = inr (δG-complete Γν Γδ σ G₁ x)
δG-complete {σ = σ′} Γν Γδ σ (G ∙ G₁) ((c ∷ u) , v , refl , x , y) = inl (u , v , refl , δG-complete Γν Γδ σ G x , σ-corollary σ′ σ G₁ .from y)
δG-complete Γν Γδ σ (G ∙ G₁) ([] , (c ∷ v) , refl , x , y) = inr (νG-complete G Γν x , δG-complete Γν Γδ σ G₁ y)
δG-complete Γν Γδ σ (var i) x = from (Γδ i) x
δG-complete Γν Γδ σ (□ G) (□ x) = □ (δG-complete Γν Γδ σ (! G) x)

δG-correct : Γν-correct Γ Γν → Γδ-correct Γ Γ′ c Γδ → σ-correct Γ Γ′ σ → (G : Gram n) → ⟦ Γ′ ⊢ (δ⟦ Γν , Γδ , σ ⊢ G ⟧ c) ⟧ w ↔ δ c ⟦ Γ ⊢ G ⟧ w
to (δG-correct Γν Γδ σ G) = δG-sound Γν Γδ σ G
from (δG-correct Γν Γδ σ G) = δG-complete Γν Γδ σ G

↔lookupG : ∀{n m Γ} (f : A → Gram m) (xs : Vec A n) (i : Fin n) → ⟦ Γ ⊢ lookup (mapVec f xs) i ⟧ w ↔ ⟦ Γ ⊢ f (lookup xs i) ⟧ w
↔lookupG f (x ∷ xs) zero = ↔refl
↔lookupG f (x ∷ xs) (suc i) = ↔lookupG f xs i

substG₀ν : ∀ {ν₁} (G : Gram _) → (ν₁ → ν⟦ Γν ⊢ G′ ⟧) → ν⟦ ν₁ ∷ Γν ⊢ G ⟧ → ν⟦ Γν ⊢ substG₀ G G′ ⟧
substG₀ν ε f x = x
substG₀ν (A · G) f (pl₁ , pr₁) = pl₁ , substG₀ν G f pr₁
substG₀ν (G ∪ G₁) f (inl x) = inl (substG₀ν G f x)
substG₀ν (G ∪ G₁) f (inr x) = inr (substG₀ν G₁ f x)
substG₀ν (G ∙ G₁) f (pl₁ , pr₁) = substG₀ν G f pl₁ , substG₀ν G₁ f pr₁
substG₀ν (var zero) f x = f x
substG₀ν (var (suc i)) f x = x
substG₀ν (□ □G) f (□ x) = □ (substG₀ν (□G .!) f x)

↔trans : A ↔ B → B ↔ C → A ↔ C
↔trans bi₁ bi₂ .to = bi₂ .to ∘ bi₁ .to
↔trans bi₁ bi₂ .from = bi₁ .from ∘ bi₂ .from

δfix : {Γ₀ : Vec Lang m} (σ : Vec (Gram m) n) {Γ′ : Vec Lang m} → let Γ = mapVec (λ G → ⟦ Γ′ ⊢ G ⟧) σ ; Γν = the-Γν σ Γ′ in {w : List Tok} (G : Gram (suc n))
  → ⟦ Γ₀ ⊢ fixG (δ⟦ ν⟦ Γν ⊢ fixG G ⟧ ∷ Γν , var zero ∷ mapVec (renameG suc) Γδ , renameG suc (substG (fixG G) (lookup σ)) ∷ mapVec (renameG suc) σ ⊢ G ⟧ c) ⟧ w
  ↔ ⟦ Γ₀ ⊢ δ⟦ Γν , Γδ , σ ⊢ fixG G ⟧ c ⟧ w

δfix-to : {Γ₀ : Vec Lang m} (Γ : Vec Lang n) {Γ′ : Vec Lang m} (_ : Γν-correct Γ Γν) {σ : Vec (Gram m) n} (_ : σ-correct Γ Γ′ σ) (G : Gram (suc n)) {G₀ : Gram (suc n)}
  → ⟦ Γ₀ ⊢ fixG′
    (δ⟦ ν⟦ Γν ⊢ fixG G₀ ⟧ ∷ Γν
      , var zero ∷ mapVec (renameG suc) Γδ
      , mapVec (renameG suc) (substG (fixG G₀) (lookup σ) ∷ σ)
      ⊢ G₀ ⟧ c)
    (δ⟦ ν⟦ Γν ⊢ fixG G₀ ⟧ ∷ Γν
      , var zero ∷ mapVec (renameG suc) Γδ
      , mapVec (renameG suc) (substG (fixG G₀) (lookup σ) ∷ σ)
      ⊢ G ⟧ c)
    ⟧ w
  → ⟦ Γ₀ ⊢ δ⟦ Γν , Γδ , σ ⊢ fixG′ G₀ G ⟧ c ⟧ w
δfix-to {c = c′} Γ Γν σ (‵ c) x with c ≟ c′
... | yes _ = x
... | no _ = x
δfix-to Γ Γν σ (A · G) (x , y) = x , δfix-to Γ Γν σ G y
δfix-to Γ Γν σ (G ∪ G₁) (inl x) = inl (δfix-to Γ Γν σ G x)
δfix-to Γ Γν σ (G ∪ G₁) (inr x) = inr (δfix-to Γ Γν σ G₁ x)
δfix-to {Γ₀ = Γ₀} Γ Γν {σ = σ′} σ (G ∙ G₁) {G₀} (inl (u , v , refl , x , y)) = inl (u , v , refl , δfix-to Γ Γν σ G x ,
  let y = unroll′ (substG G₁ (lookup (mapVec (renameG suc) (substG (fixG G₀) (lookup σ′) ∷ σ′)))) y
  in {!⊢subst {Γ = Γ₀} _ ? G₁ .from!}
  )
  -- let y = unroll′ (substG G₁ (lookup (mapVec (renameG suc) (substG (fixG G₀) (lookup σ′) ∷ σ′)))) y
  --     y = ⊢subst _
  --       (λ where
  --         zero → ↔trans (↔sym (σ-corollary σ′ σ (fixG G₀))) (↔sym {!!}) -- (renamesuc (substG (fixG G₀) (lookup σ′))))
  --         (suc i) → {!!}
  --           -- subst (λ X → lookup Γ i _ ↔ ⟦ _ ∷ _ ⊢ X ⟧ _)
  --           --  (sym (lookup-map (renameG suc) σ′ i))
  --           --  (↔sym (↔trans (renamesuc (lookup σ′ i))
  --           --    (σ i)))
  --       )
  --       G₁ .from y
  --     y = roll′ {Γ = Γ} G₁ y
  -- in {! ⊢subst (lookup σ′) (λ i → ↔sym (σ i)) (fixG′ G₀ G₁) .to y !})
δfix-to Γ Γν σ (G ∙ G₁) {G₀} (inr (x , y)) = inr (
  (let x = νG-sound G (λ { zero → νG-correct {Γ = Γ} (fixG G₀) Γν ; (suc i) → Γν i }) x
       x = roll′ G x  
   in νG-complete (fixG′ G₀ G) Γν x)
  , δfix-to Γ Γν σ G₁ y)
δfix-to Γ Γν σ (var zero) {G₀} (□ x) = □ (δfix-to Γ Γν σ G₀ x)
δfix-to {Γδ = Γδ} Γ Γν σ (var (suc i)) x = fixGsuc-to (lookup Γδ i) (subst (λ X → ⟦ _ ⊢ fixG′ _ X ⟧ _) (lookup-map (renameG suc) Γδ i) x)
δfix-to Γ Γν σ (□ □G) (□ x) = □ (δfix-to Γ Γν σ (□G .!) x)

δfix-from : (Γ : Vec Lang n) {Γ′ : Vec Lang m} (Γνc : Γν-correct Γ Γν) (σc : σ-correct Γ Γ′ σ) (G : Gram (suc n)) {G₀ : Gram (suc n)}
  → ⟦ Γ′ ⊢ δ⟦ Γν , Γδ , σ ⊢ fixG′ G₀ G ⟧ c ⟧ w
  → ⟦ Γ′ ⊢ fixG′
      (δ⟦ ν⟦ Γν ⊢ fixG G₀ ⟧ ∷ Γν
        , var zero ∷ mapVec (renameG suc) Γδ
        , mapVec (renameG suc) (substG (fixG G₀) (lookup σ) ∷ σ)
        ⊢ G₀ ⟧ c)
      (δ⟦ ν⟦ Γν ⊢ fixG G₀ ⟧ ∷ Γν
        , var zero ∷ mapVec (renameG suc) Γδ
        , mapVec (renameG suc) (substG (fixG G₀) (lookup σ) ∷ σ)
        ⊢ G ⟧ c)
    ⟧ w
δfix-from {c = c′} Γ Γν σ (‵ c) x with c ≟ c′
... | yes _ = x
... | no _ = x
δfix-from Γ Γν σ (A · G) (x , y) = x , δfix-from Γ Γν σ G y
δfix-from Γ Γν σ (G ∪ G₁) (inl x) = inl (δfix-from Γ Γν σ G x)
δfix-from Γ Γν σ (G ∪ G₁) (inr x) = inr (δfix-from Γ Γν σ G₁ x)
δfix-from {σ = σ′} Γ {Γ′} Γν σ (G ∙ G₁) {G₀} (inl (u , v , refl , x , y)) = inl (u , v , refl , δfix-from Γ Γν σ G x ,
  roll′
   (substG G₁
    (lookup
     (mapVec (renameG suc) (substG (fixG G₀) (lookup σ′) ∷ σ′))))
   (⊢subst
     (lookup (mapVec (renameG suc) (substG (fixG G₀) (lookup σ′) ∷ σ′)))
       (λ where
         zero → ↔sym (↔trans (renamesuc (substG (fixG G₀) (lookup σ′)))
           (σ-corollary {Γ = Γ} σ′ σ (fixG G₀)))
         (suc i) → subst (λ X → lookup Γ i _ ↔ ⟦ _ ∷ _ ⊢ X ⟧ _) (sym (lookup-map (renameG suc) σ′ i))
           (↔sym (↔trans (renamesuc (lookup σ′ i)) (σ i))))
       G₁ .to (unroll′ G₁ (⊢subst (lookup σ′) (λ i → ↔sym (σ i)) (fixG′ G₀ G₁) .from y))))
δfix-from {n = n} Γ Γν σ (G ∙ G₁) {G₀} (inr (x , y)) = inr (νG-complete G (λ { zero → νG-correct (fixG G₀) Γν ; (suc i) → Γν i }) (unroll′ {Γ = Γ} G {G₀} (νG-sound {n = n} (fixG′ G₀ G) Γν x)) , δfix-from Γ Γν σ G₁ y)
δfix-from Γ Γν σ (var zero) {G₀} (□ x) = □ (δfix-from Γ Γν σ G₀ x)
δfix-from {Γδ = Γδ} Γ Γν σ (var (suc i)) x = subst (λ X → ⟦ _ ⊢ fixG′ _ X ⟧ _) (sym (lookup-map (renameG suc) Γδ i)) (fixGsuc-from (lookup Γδ i) x)
δfix-from Γ Γν σ (□ □G) (□ x) = □ (δfix-from Γ Γν σ (□G .!) x)

δfix Γ {Γ′} G .to x = δfix-to {Γν = the-Γν Γ Γ′} (mapVec (λ G → ⟦ Γ′ ⊢ G ⟧) Γ) (the-Γν-correct Γ) {σ = Γ} (the-σ-correct Γ Γ′) G x
-- δfix Γ {Γ′} G .from x = δfix-from (mapVec (λ G → ⟦ Γ′ ⊢ G ⟧) Γ) (the-Γν-correct Γ) (the-σ-correct Γ Γ′) G x

δ?₀ : DecGram zero G → (c : Tok) → DecGram zero (δ⟦ G ⟧₀ c)

δ? : (σ : Vec (Gram m) n) → let Γν = the-Γν σ Γ′ in (∀ i → Dec (lookup Γν i)) → (∀ i → DecGram m (lookup Γδ i)) → (∀ i → DecGram m (lookup σ i)) → DecGram n G → (c : Tok) → DecGram m (δ⟦ Γν , Γδ , σ ⊢ G ⟧ c)
δ? σ Γν? Γδ? σ? ∅ c = ∅
δ? σ Γν? Γδ? σ? ε c = ∅
δ? σ Γν? Γδ? σ? (‵ c′) c with c′ ≟ c
... | yes _ = ε
... | no _ = ∅
δ? σ Γν? Γδ? σ? (x · G) c = x · δ? σ Γν? Γδ? σ? G c
δ? σ Γν? Γδ? σ? (G₁ ∪ G₂) c = δ? σ Γν? Γδ? σ? G₁ c ∪ δ? σ Γν? Γδ? σ? G₂ c
δ? {G = G′} σ Γν? Γδ? σ? (G₁ ∙ G₂) c = δ? σ Γν? Γδ? σ? G₁ c ∙ substDG σ G₂ σ? ∪ (ν?′ G₁ Γν? · δ? σ Γν? Γδ? σ? G₂ c)
δ? σ Γν? Γδ? σ? (var i) c = Γδ? i
δ? {m = m} {Γ′ = Γ′} {Γδ = Γδ′} {G = G′} σ Γν? Γδ? σ? (μ {G = G″} G) c =
  (λ {HERE} → {!δfix {Γ₀ = HERE} σ G″!}) ◃ μ (
    δ? {Γ′ = δ c ⟦ mapVec (λ G → ⟦ Γ′ ⊢ G ⟧) σ ⊢ G′ ⟧ ∷ Γ′}
       {Γδ = var zero ∷ mapVec (renameG suc) Γδ′}
       (mapVec (renameG suc) (substG G′ (lookup σ) ∷ σ))
       (λ { zero → {!ν? (μ G)!} ; (suc i) → {!!} })
       {!!}
       {!!}
       -- (λ { zero → ν?′ (μ G) Γν? ; (suc i) → Γν? i })
       -- (λ { zero → var zero ; (suc i) → (↔sym (↔lookupG (renameG suc) Γδ′ i)) ◃ renameDG suc (Γδ? i) })
       -- (λ { zero → renameDG {n = m} {G = substG (fixG G″) (lookup σ)} suc (substDG σ (μ G) σ?) ; (suc i) → subst (DecGram _) (sym (lookup-map (renameG suc) σ i)) (renameDG suc (σ? i))})
       G
       c)

δ?₀ G c = δ? [] (λ ()) (λ ()) (λ ()) G c

parse : DecGram zero G → (w : List Tok) → Dec (⟦ G ⟧ w)
parse G [] = ν?₀ G
parse {G = G′} G (c ∷ w) = mapDec (δG-correct (λ ()) (λ ()) (λ ()) G′) (parse (δ?₀ G c) w)
