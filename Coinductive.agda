{-# OPTIONS --guardedness --safe #-}

open import Agda.Primitive using (Level)

variable
  ℓ : Level
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
        ‵_ : Tok → Gram n
        _·_ : Set → Gram n → Gram n
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

renameG : ∀{n m} → (Fin n → Fin m) → Gram n → Gram m
renameG f ∅ = ∅
renameG f ε = ε
renameG f (‵ c) = ‵ c
renameG f (A · G) = A · renameG f G
renameG f (G₁ ∪ G₂) = renameG f G₁ ∪ renameG f G₂
renameG f (G₁ ∙ G₂) = renameG f G₁ ∙ renameG f G₂
renameG f (var i) = var (f i)
renameG f (□ G) = □ λ { .! → renameG f (! G) }

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

⟦_⊢_⟧ : (Γ : Vec Lang n) → Gram n → Lang

data □⟦_⊢_⟧ (Γ : Vec Lang n) (□G : □Gram n) (w : List Tok) : Set where
  □ : ⟦ Γ ⊢ ! □G ⟧ w → □⟦ Γ ⊢ □G ⟧ w

-- lookupEl : {xs : List A} → El xs → A
-- lookupEl {xs = []} ()
-- lookupEl {xs = x ∷ _} here = x
-- lookupEl {xs = _ ∷ xs} (there i) = lookupEl i

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

x+x+x : ⟦ Γ ⊢ expr ⟧ (let open T in x ∷ + ∷ x ∷ + ∷ x ∷ [])
x+x+x = inr (_ , _ , refl , □ (inl refl) , _ , _ , refl , refl , □ (inr (_ , _ , refl , □ (inl refl) , _ , _ , refl , refl , □ (inl refl))))


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

data ⊤ : Set where
  tt : ⊤

-- data All {A : Set ℓ} (f : A → Set) : List A → Set ℓ where
--   [] : All f []
--   _∷_ : ∀{x xs} → f x → All f xs → All f (x ∷ xs)

-- lookupAll : All f Γ → 

variable Γν : Vec Set n

ν⟦_⊢_⟧ : (Γν : Vec Set n) → Gram n → Set

data ν□G (□G : □Gram n) (Γν : Vec Set n) : Set where
  □ : ν⟦ Γν ⊢ ! □G ⟧ → ν□G □G Γν

-- lookupAll : ∀{f x} → All f Γ → El Γ x → f x
-- lookupAll = {!!}

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

_∘_ : (B -> C) -> (A -> B) -> A -> C
(f ∘ g) x = f (g x)

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

-- mapFix : ∀ G {G′} → (∀{Γ w} → ⟦ Γ ⊢ G ⟧ w → ⟦ Γ ⊢ G′ ⟧ w) → ⟦ Γ ⊢ fixG G ⟧ w → ⟦ Γ ⊢ fixG G′ ⟧ w

map×r : (B → C) → A × B → A × C
map×r f (x , y) = x , f y

-- test : (G : Gram _) → A → ⟦ Γ ⊢ fixG G ⟧ w → ⟦ Γ ⊢ fixG (A · G) ⟧ w
-- test {A = A} G a x = mapFix₀ (A · G) (test G a) (a , x)

-- mapFix ε f x = {!f x!}
-- mapFix (‵ x₁) f x = {!!}
-- mapFix (x₁ · G) f x = {!!}
-- mapFix (G ∪ G₁) f x = {!!}
-- mapFix (G ∙ G₁) f x = {!!}
-- mapFix (var x₁) f x = {!!}
-- mapFix (□ x₁) f x = {!!}

-- Is fixG really a fixed point? Yes:

unroll : ∀ G → ⟦ Γ ⊢ fixG G ⟧ w → ⟦ (⟦ Γ ⊢ fixG G ⟧ ∷ Γ) ⊢ G ⟧ w

unroll′ : ∀{G₀} G → ⟦ Γ ⊢ fixG′ G₀ G ⟧ w → ⟦ (⟦ Γ ⊢ fixG G₀ ⟧ ∷ Γ) ⊢ G ⟧ w
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

-- this needs to be made a constructor
_◃_ : (∀ Γ w → ⟦ Γ ⊢ G₁ ⟧ w ↔ ⟦ Γ ⊢ G₂ ⟧ w) → DecGram n G₁ → DecGram n G₂
_◃_ = {!!}

consrn : ∀{n m} → (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
consrn f zero = zero
consrn f (suc i) = suc (f i)

renameFixG : ∀{n m} {Γ : Vec Lang m} (G : Gram (suc n)) (f : Fin n → Fin m) → ⟦ Γ ⊢ renameG f (fixG G) ⟧ w ↔ ⟦ Γ ⊢ fixG (renameG (consrn f) G) ⟧ w
renameFixG = {!!}
-- to (renameFixG ε f) x = x
-- to (renameFixG (‵ x₁) f) x = x
-- to (renameFixG (x₁ · G) f) (pl , pr) = pl , {!to (renameFixG G f) pr!}
-- to (renameFixG (G ∪ G₁) f) x = {!!}
-- to (renameFixG (G ∙ G₁) f) x = {!!}
-- to (renameFixG (var x₁) f) x = {!!}
-- to (renameFixG (□ G) f) (□ x) = □ {!to (renameFixG (G .!) ?) x!}
-- from (renameFixG G f) = {!!}

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
renameDG f (μ {G = G} DG) = (λ _ _ → ↔sym (renameFixG G f)) ◃ μ (renameDG (consrn f) DG)

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

mapVec : (A → B) → Vec A n → Vec B n
mapVec f [] = []
mapVec f (x ∷ xs) = f x ∷ mapVec f xs

↔lookup : (f : A → Set) (xs : Vec A n) (i : Fin n) → lookup (mapVec f xs) i ↔ f (lookup xs i)
↔lookup f (x ∷ xs) zero = ↔refl
↔lookup f (x ∷ xs) (suc i) = ↔lookup f xs i

ν?₀ : DecGram zero G → Dec (ν ⟦ G ⟧)

ν? : DecGram n G → (∀ i → Dec (ν (lookup Γ i))) → Dec (ν ⟦ Γ ⊢ G ⟧)
ν? {G = G} {Γ = Γ′} DG Γ = mapDec (νG-correct {Γν = mapVec ν Γ′} G (↔lookup ν Γ′)) (ν?′ DG (λ i → mapDec (↔sym (↔lookup ν Γ′ i)) (Γ i)))

ν?₀ G = ν? G λ ()

-- derivative

δ⟦_⟧₀ : Gram zero → Tok → Gram zero

δ⟦_,_⊢_⟧ : Vec Set n → Vec (Gram n) n → Gram n → Tok → Gram n
δ⟦ Γν , Γδ ⊢ ∅ ⟧ _ = ∅
δ⟦ Γν , Γδ ⊢ ε ⟧ _ = ∅
δ⟦ Γν , Γδ ⊢ ‵ c′ ⟧ c with c′ ≟ c
... | yes _ = ε
... | no _ = ∅
δ⟦ Γν , Γδ ⊢ A · G ⟧ c = A · δ⟦ Γν , Γδ ⊢ G ⟧ c
δ⟦ Γν , Γδ ⊢ G₁ ∪ G₂ ⟧ c = δ⟦ Γν , Γδ ⊢ G₁ ⟧ c ∪ δ⟦ Γν , Γδ ⊢ G₂ ⟧ c
δ⟦ Γν , Γδ ⊢ G₁ ∙ G₂ ⟧ c = δ⟦ Γν , Γδ ⊢ G₁ ⟧ c ∙ G₂ ∪ (ν⟦ Γν ⊢ G₁ ⟧ · δ⟦ Γν , Γδ ⊢ G₂ ⟧ c)
δ⟦ Γν , Γδ ⊢ var i ⟧ c = lookup Γδ i
δ⟦ Γν , Γδ ⊢ □ G ⟧ c = □ (λ { .! → δ⟦ Γν , Γδ ⊢ ! G ⟧ c })

δ⟦ G ⟧₀ = δ⟦ [] , [] ⊢ G ⟧

variable Γδ : Vec (Gram n) n

Γδ-correct : Vec Lang n → Tok → Vec (Gram n) n → Set
Γδ-correct Γ c Γδ = ∀ {w} i → ⟦ Γ ⊢ lookup Γδ i ⟧ w ↔ δ c (lookup Γ i) w

δG-sound : Γν-correct Γ Γν → Γδ-correct Γ c Γδ → (G : Gram n) → ⟦ Γ ⊢ (δ⟦ Γν , Γδ ⊢ G ⟧ c) ⟧ w → δ c ⟦ Γ ⊢ G ⟧ w
δG-sound {c = c} Γν Γδ (‵ c′) x with c′ ≟ c
δG-sound {c = c} Γν Γδ (‵ c) refl | yes refl = refl
δG-sound {c = c} Γν Γδ (‵ c′) () | no _
δG-sound Γν Γδ (A · G) (pl , pr) = pl , δG-sound Γν Γδ G pr
δG-sound Γν Γδ (G ∪ G₁) (inl x) = inl (δG-sound Γν Γδ G x)
δG-sound Γν Γδ (G ∪ G₁) (inr x) = inr (δG-sound Γν Γδ G₁ x)
δG-sound Γν Γδ (G ∙ G₁) (inl (u , v , refl , x , y)) = (_ ∷ u) , v , refl , δG-sound Γν Γδ G x , y
δG-sound Γν Γδ (G ∙ G₁) (inr (x , y)) = [] , (_ ∷ _) , refl , νG-sound G Γν x , δG-sound Γν Γδ G₁ y
δG-sound Γν Γδ (var i) x = to (Γδ i) x
δG-sound Γν Γδ (□ G) (□ x) = □ (δG-sound Γν Γδ (G .!) x)

δG-complete : Γν-correct Γ Γν → Γδ-correct Γ c Γδ → (G : Gram n) → δ c ⟦ Γ ⊢ G ⟧ w → ⟦ Γ ⊢ (δ⟦ Γν , Γδ ⊢ G ⟧ c) ⟧ w 
δG-complete {c = c} Γν Γδ (‵ c′) x with c′ ≟ c
δG-complete {c = c} Γν Γδ (‵ c) refl | yes refl = refl
δG-complete {c = .c′} Γν Γδ (‵ c′) refl | no ¬x = ¬x refl
δG-complete Γν Γδ (A · G) (pl , pr) = pl , δG-complete Γν Γδ G pr
δG-complete Γν Γδ (G ∪ G₁) (inl x) = inl (δG-complete Γν Γδ G x)
δG-complete Γν Γδ (G ∪ G₁) (inr x) = inr (δG-complete Γν Γδ G₁ x)
δG-complete Γν Γδ (G ∙ G₁) ((c ∷ u) , v , refl , x , y) = inl (u , v , refl , δG-complete Γν Γδ G x , y)
δG-complete Γν Γδ (G ∙ G₁) ([] , (c ∷ v) , refl , x , y) = inr (νG-complete G Γν x , δG-complete Γν Γδ G₁ y)
δG-complete Γν Γδ (var i) x = from (Γδ i) x
δG-complete Γν Γδ (□ G) (□ x) = □ (δG-complete Γν Γδ (! G) x)

↔lookupG : ∀{n m Γ} (f : A → Gram m) (xs : Vec A n) (i : Fin n) → ⟦ Γ ⊢ lookup (mapVec f xs) i ⟧ w ↔ ⟦ Γ ⊢ f (lookup xs i) ⟧ w
↔lookupG f (x ∷ xs) zero = ↔refl
↔lookupG f (x ∷ xs) (suc i) = ↔lookupG f xs i

-- inside : ⟦ Γ ⊢ fixG (A · G) ⟧ w → ⟦ Γ ⊢ fixG G ⟧ w
-- inside {G = G} (_ , y) = mapFixo G _×_.pr y
-- 
-- outside₁ : {G′ : Gram _} (G : Gram _) → (∀{Γ w} → ⟦ Γ ⊢ G ⟧ w → ⟦ Γ ⊢ G′ ⟧ w) → ⟦ Γ ⊢ δ⟦ Γν , Γδ ⊢ G ⟧ c ⟧ w → ⟦ Γ ⊢ δ⟦ Γν , Γδ ⊢ G′ ⟧ c ⟧ w
-- outside₁ = {!!}
-- -- outside₁ {c = c} (‵ c′) f x with c′ ≟ c
-- -- ... | yes _ = {!!}
-- -- ... | no _ = {!!}
-- -- outside₁ (x₁ · G) f x = {!!}
-- -- outside₁ (G ∪ G₁) f x = {!!}
-- -- outside₁ (G ∙ G₁) f x = {!!}
-- -- outside₁ (var x₁) f x = {!!}
-- -- outside₁ (□ x₁) f x = {!!}
-- 
-- outside₂ : ⟦ Γ ⊢ fixG′ G (A · G) ⟧ w → ⟦ Γ ⊢ fixG (A · G) ⟧ w
-- outside₂ {G = G} (x , y) = mapFixo {w = _} (_ · G) (_,_ x) (x , y)

δfix-to : {G₀ : Gram _} (G : Gram _)
  → ⟦ Γ ⊢ fixG
      (δ⟦ (ν⟦ Γν ⊢ fixG G₀ ⟧ ∷ Γν)
        , (var zero ∷ mapVec (renameG suc) Γδ)
        ⊢ G ⟧ c)
    ⟧ w
  → ⟦ Γ ⊢ δ⟦ Γν , Γδ ⊢ fixG G ⟧ c ⟧ w
δfix-to {c = c} (‵ c′)  with c′ ≟ c
... | yes _ = λ x → x
... | no _ = λ ()
δfix-to {Γ = Γ} {Γν = Γν} {Γδ = Γδ} {c = c} {w = w} {G₀ = G₀} (A · G) (x , y) =
  {!mapFix _ _×_.pr y!}
δfix-to = {!!}
--    outside₁ {G′ = fixG (A · G)} (fixG G) (outside₂ {G = G} ∘ x ,_) (δfix-to {_} {Γ} {Γν} {Γδ} {c} {w} {G₀} G
--       (inside {_} {Γ} {_} {δ⟦ ν⟦ Γν ⊢ fixG G₀ ⟧ ∷ Γν , var zero ∷ mapVec (renameG suc) Γδ ⊢ G ⟧ c} {w} (x , y)))

-- outside {_} {Γ} {_} {δ⟦ ν⟦ Γν ⊢ fixG G₀ ⟧ ∷ Γν , var zero ∷ mapVec (renameG suc) Γδ ⊢ G ⟧ c} {w} {Γν} {Γδ} {c}

-- mapFix₀ : ∀{G′} (G : Gram _) → (∀{Γ w} → ⟦ Γ ⊢ G ⟧ w → ⟦ Γ ⊢ G′ ⟧ w) → ⟦ Γ ⊢ fixG′ G G ⟧ w → ⟦ Γ ⊢ fixG′ G′ G ⟧ w

--   x ,  mapFix₀ _ (x ,_) (δfix-to G (mapFix₀ (A · δ⟦ ν⟦ Γν ⊢ fixG G₀ ⟧ ∷ Γν , var zero ∷ mapVec (renameG suc) Γδ ⊢ G ⟧ c) {!!} {!y!}))

-- δfix-to (G₁ ∪ G₂) (inl x) = inl (δfix-to G₁ x)
-- δfix-to (G₁ ∪ G₂) (inr x) = inr (δfix-to G₂ x)
-- δfix-to (G₁ ∙ G₂) (inl (u , v , refl , x , y)) = inl (u , v , refl , δfix-to G₁ x , {!y!})
-- δfix-to (G₁ ∙ G₂) (inr x) = {!!}
-- δfix-to (var i) x = {!!}
-- δfix-to (□ G) x = {!!}

-- δfix-to : {G₀ : Gram _} (G : Gram _)
--   → ⟦ Γ ⊢ fixG′
--       (δ⟦ (ν⟦ Γν ⊢ fixG G₀ ⟧ ∷ Γν)
--         , (var zero ∷ mapVec (renameG suc) Γδ)
--         ⊢ G₀ ⟧ c)
--       (δ⟦ (ν⟦ Γν ⊢ fixG G₀ ⟧ ∷ Γν)
--         , (var zero ∷ mapVec (renameG suc) Γδ)
--         ⊢ G ⟧ c)
--     ⟧ w
--   → ⟦ Γ ⊢ δ⟦ Γν , Γδ ⊢ fixG′ G₀ G ⟧ c ⟧ w
-- δfix-to {c = c} (‵ c′)  with c′ ≟ c
-- ... | yes _ = λ x → x
-- ... | no _ = λ ()
-- δfix-to (A · G) (x , y) = x , δfix-to G y
-- δfix-to (G₁ ∪ G₂) (inl x) = inl (δfix-to G₁ x)
-- δfix-to (G₁ ∪ G₂) (inr x) = inr (δfix-to G₂ x)
-- δfix-to (G₁ ∙ G₂) (inl (u , v , refl , x , y)) = inl (u , v , refl , δfix-to G₁ x , {!y!})
-- δfix-to (G₁ ∙ G₂) (inr x) = {!!}
-- δfix-to (var i) x = {!!}
-- δfix-to (□ G) x = {!!}

δfix-from : (G : Gram _)
  → ⟦ Γ ⊢ δ⟦ Γν , Γδ ⊢ fixG G ⟧ c ⟧ w
  → ⟦ Γ ⊢ fixG
      (δ⟦ (ν⟦ Γν ⊢ fixG G ⟧ ∷ Γν)
        , (var zero ∷ mapVec (renameG suc) Γδ)
        ⊢ G ⟧ c)
    ⟧ w
δfix-from = {!!}
-- δfix-from {c = c} (‵ c′) x with c′ ≟ c
-- ... | yes _ = x
-- ... | no _ = x
-- δfix-from (A · G) (x , y) = x , {!δfix-from G ?!}
-- δfix-from (G₁ ∪ G₂) x = {!!}
-- δfix-from (G₁ ∙ G₂) x = {!!}
-- δfix-from (var i) x = {!!}
-- δfix-from (□ G) x = {!!}

δfix-bi : ⟦ Γ ⊢ fixG (δ⟦ (ν⟦ Γν ⊢ fixG G ⟧ ∷ Γν) , (var zero ∷ mapVec (renameG suc) Γδ) ⊢ G ⟧ c) ⟧ w ↔ ⟦ Γ ⊢ δ⟦ Γν , Γδ ⊢ fixG G ⟧ c ⟧ w
to (δfix-bi {Γ = Γ} {Γν = Γν} {G = G} {Γδ = Γδ} {c = c} {w = w}) x = δfix-to {Γ = Γ} {Γν = Γν} {Γδ = Γδ} {c = c} {w = w} {G₀ = G} G x
from (δfix-bi {G = G}) x = δfix-from G x

δ?₀ : DecGram zero G → (c : Tok) → DecGram zero (δ⟦ G ⟧₀ c)

δ? : (∀ i → Dec (lookup Γν i)) → (∀ i → DecGram n (lookup Γδ i)) → DecGram n G → (c : Tok) → DecGram n (δ⟦ Γν , Γδ ⊢ G ⟧ c)
δ? Γν Γδ ∅ c = ∅
δ? Γν Γδ ε c = ∅
δ? Γν Γδ (‵ c′) c with c′ ≟ c
... | yes _ = ε
... | no _ = ∅
δ? Γν Γδ (x · G) c = x · δ? Γν Γδ G c
δ? Γν Γδ (G₁ ∪ G₂) c = δ? Γν Γδ G₁ c ∪ δ? Γν Γδ G₂ c
δ? Γν Γδ (G₁ ∙ G₂) c = δ? Γν Γδ G₁ c ∙ G₂ ∪ (ν?′ G₁ Γν · δ? Γν Γδ G₂ c)
δ? Γν Γδ (var i) c = Γδ i
δ? {Γν = Γν′} {Γδ = Γδ′} {G = G′} Γν Γδ (μ {G = G″} G) c = (λ _ _ → record { to = δfix-to {G₀ = G″} G″ ; from = δfix-from G″ }) ◃ μ (δ? {Γν = (ν⟦ Γν′ ⊢ G′ ⟧) ∷ Γν′} {Γδ = var zero ∷ mapVec (renameG suc) Γδ′} (λ { zero → ν?′ (μ G) Γν ; (suc i) → Γν i }) (λ { zero → var zero ; (suc i) → (λ _ _ → ↔sym (↔lookupG (renameG suc) Γδ′ i)) ◃ renameDG suc (Γδ i) }) G c)

δ?₀ G c = δ? (λ ()) (λ ()) G c

