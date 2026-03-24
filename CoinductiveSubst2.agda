{-# OPTIONS --guardedness -WnoPatternShadowsConstructor #-}

open import Level using (Level ; _⊔_)
open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Relation.Binary.PropositionalEquality hiding (subst-subst)
open ≡-Reasoning

variable
  ℓ ℓ₁ ℓ₂ : Level
  A B C : Set ℓ

data ⊥ : Set where

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
        a : Tok
        b : Tok
        -- c : Tok

    _≟_ : (c c′ : Tok) → Dec (c ≡ c′) 
    x ≟ x = yes refl
    x ≟ + = no (λ ())
    + ≟ x = no (λ ())
    + ≟ + = yes refl
    x ≟ a = no (λ ())
    x ≟ b = no (λ ())
--    x ≟ c = no (λ ())
    + ≟ a = no (λ ())
    + ≟ b = no (λ ())
 --   + ≟ c = no (λ ())
    a ≟ x = no (λ ())
    a ≟ + = no (λ ())
    a ≟ a = yes refl
    a ≟ b = no (λ ())
  --  a ≟ c = no (λ ())
    b ≟ x = no (λ ())
    b ≟ + = no (λ ())
    b ≟ a = no (λ ())
    b ≟ b = yes refl
   -- b ≟ c = no (λ ())
   -- c ≟ x = no (λ ())
   -- c ≟ + = no (λ ())
   -- c ≟ a = no (λ ())
   -- c ≟ b = no (λ ())
   -- c ≟ c = yes refl

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

-- mutual
--     data Gram : Set₁ where
--         ∅ : Gram
--         ε : Gram
--         ‵_ : (c : Tok) → Gram
--         _·_ : (A : Set) → (G : Gram) → Gram
--         _∪_ : (G₁ G₂ : Gram) → Gram
--         _∙_ : (G₁ G₂ : Gram) → Gram
--         ▹ : (∞G : ∞Gram) → Gram
-- 
--     record ∞Gram : Set₁ where
--         coinductive
--         field ! : Gram

infix 23 ‵_
infixr 22 _∙_
infixr 21 _∪_

-- open ∞Gram using (!)

_∘_ : (B -> C) -> (A -> B) -> A -> C
(f ∘ g) x = f (g x)

variable
    Γ Γ′ Γ₁ Γ₂ : Vec Lang n
--    G G′ G₁ G₂ : Gram
    u v w : List Tok
--    ∞G : ∞Gram
    ℒ : Lang

-- module _ where
--     open ∞Gram
--     open T
-- 
--     left-right : Gram
--     left-right = let left-right = ▹ λ { .! → left-right } in
--         left-right ∙ left-right
-- 
--     expr : Gram
--     expr = let open T; expr = ▹ λ { .! → expr } in
--         ‵ x ∪ expr ∙ ‵ + ∙ expr
-- 
--     repeat : ℕ → Gram → Gram
--     repeat zero G = ε
--     repeat (suc k) G = G ∙ repeat k G
-- 
--     -- this supports even context-sensitive languages
--     aᵏbᵏcᵏ : Gram
--     aᵏbᵏcᵏ = go zero
--       where
--         go : ℕ → Gram
--         go k = repeat k (‵ a) ∙ repeat k (‵ b) ∙ repeat k (‵ c) ∪ ▹ λ { .! → go (suc k) } 
      
variable c : Tok

-- ⟦_⟧ : Gram → Lang
-- 
-- data ▹⟦_⟧ (∞G : ∞Gram) (w : List Tok) : Set where
--   ▹ : ⟦ ∞G .! ⟧ w → ▹⟦ ∞G ⟧ w
-- 
-- ⟦ ∅ ⟧ _ = ⊥
-- ⟦ ε ⟧ w = w ≡ []
-- ⟦ ‵ c ⟧ w = w ≡ c ∷ []
-- ⟦ A · G ⟧ w = A × ⟦ G ⟧ w
-- ⟦ G₁ ∪ G₂ ⟧ w = ⟦ G₁ ⟧ w ⊎ ⟦ G₂ ⟧ w
-- ⟦ G₁ ∙ G₂ ⟧ w = ∃ λ u → ∃ λ v → (w ≡ u ++ v) × ⟦ G₁ ⟧ u × ⟦ G₂ ⟧ v
-- ⟦ ▹ ∞G ⟧ w = ▹⟦ ∞G ⟧ w

mapVec : (A → B) → Vec A n → Vec B n
mapVec f [] = []
mapVec f (x ∷ xs) = f x ∷ mapVec f xs

record _↔_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
open _↔_

-- ⊢subst : (k : Fin n → Gram m) (foo : ∀ {w} i → lookup Γ′ i w ↔ ⟦ Γ ⊢ k i ⟧ w) (G : Gram n) → ⟦ Γ′ ⊢ G ⟧ w ↔ ⟦ Γ ⊢ substG G k ⟧ w
-- ⊢subst k f ε .to x = x
-- ⊢subst k f (‵ c) .to x = x
-- ⊢subst k f (A · G) .to (x , y) = x , ⊢subst k f G .to y
-- ⊢subst k f (G ∪ G₁) .to (inl x) = inl (⊢subst k f G .to x)
-- ⊢subst k f (G ∪ G₁) .to (inr x) = inr (⊢subst k f G₁ .to x)
-- ⊢subst k f (G ∙ G₁) .to (u , v , refl , x , y) = u , v , refl , ⊢subst k f G .to x , ⊢subst k f G₁ .to y
-- ⊢subst k f (var i) .to x = f i .to x
-- ⊢subst k f (▹ ∞G) .to (▹ x) = ▹ (⊢subst k f (∞G .!) .to x)
-- ⊢subst k f ε .from x = x
-- ⊢subst k f (‵ c) .from x = x
-- ⊢subst k f (A · G) .from (pl₁ , pr₁) = pl₁ , ⊢subst k f G .from pr₁
-- ⊢subst k f (G ∪ G₁) .from (inl x) = inl (⊢subst k f G .from x)
-- ⊢subst k f (G ∪ G₁) .from (inr x) = inr (⊢subst k f G₁ .from x)
-- ⊢subst k f (G ∙ G₁) .from (u , v , refl , x , y) = u , v , refl , ⊢subst k f G .from x , ⊢subst k f G₁ .from y
-- ⊢subst k f (var i) .from x = f i .from x
-- ⊢subst k f (▹ ∞G) .from (▹ x) = ▹ (⊢subst k f (∞G .!) .from x)
-- 
-- ⊢subst₀ : (G : Gram _) → ⟦ ⟦ Γ ⊢ G′ ⟧ ∷ Γ ⊢ G ⟧ w → ⟦ Γ ⊢ substG₀ G G′ ⟧ w
-- ⊢subst₀ ε x = x
-- ⊢subst₀ (‵ c) x = x
-- ⊢subst₀ {G′ = G′} (A · G) (pl , pr) = pl , ⊢subst₀ G pr
-- ⊢subst₀ (G ∪ G₁) (inl x) = inl (⊢subst₀ G x)
-- ⊢subst₀ (G ∪ G₁) (inr x) = inr (⊢subst₀ G₁ x)
-- ⊢subst₀ (G ∙ G₁) (u , v , refl , x , y) = u , v , refl , ⊢subst₀ G x , ⊢subst₀ G₁ y
-- ⊢subst₀ (var zero) x = x
-- ⊢subst₀ (var (suc i)) x = x
-- ⊢subst₀ (▹ ∞G) (▹ x) = ▹ (⊢subst₀ (∞G .!) x)
-- 
-- ⊢subst₀′ : (G : Gram _) → ⟦ Γ ⊢ substG₀ G G′ ⟧ w → ⟦ ⟦ Γ ⊢ G′ ⟧ ∷ Γ ⊢ G ⟧ w
-- ⊢subst₀′ ε x = x
-- ⊢subst₀′ (‵ c) x = x
-- ⊢subst₀′ {G′ = G′} (A · G) (pl , pr) = pl , ⊢subst₀′ G pr
-- ⊢subst₀′ (G ∪ G₁) (inl x) = inl (⊢subst₀′ G x)
-- ⊢subst₀′ (G ∪ G₁) (inr x) = inr (⊢subst₀′ G₁ x)
-- ⊢subst₀′ (G ∙ G₁) (u , v , refl , x , y) = u , v , refl , ⊢subst₀′ G x , ⊢subst₀′ G₁ y
-- ⊢subst₀′ (var zero) x = x
-- ⊢subst₀′ (var (suc i)) x = x
-- ⊢subst₀′ (▹ ∞G) (▹ x) = ▹ (⊢subst₀′ (∞G .!) x)
-- 
-- --    expr : Gram n
-- --    expr = let open T; expr = ▹ λ { .! → expr } in
-- --        ‵ x ∪ expr ∙ ‵ + ∙ expr
-- 
-- -- data Expr : Set where
-- --   x : Expr
-- --   _+_ : Expr → Expr → ExprG

-- x+x+x : ⟦ expr ⟧ (let open T in x ∷ + ∷ x ∷ + ∷ x ∷ [])
-- x+x+x = inr (_ , _ , refl , ▹ (inl refl) ,
--              _ , _ , refl , refl
--                           , ▹ (inr (_ , _ , refl , ▹ (inl refl) ,
--                                     _ , _ , refl , refl
--                                                  , ▹ (inl refl))))


mapDec : (A ↔ B) → Dec A → Dec B
mapDec bi (yes x) = yes (to bi x)
mapDec bi (no ¬x) = no (λ y → ¬x (from bi y))

data Bool : Set where
  false : Bool
  true : Bool

data ⊤ : Set where
  tt : ⊤

-- ν⟦_⟧ : Gram → Set
-- 
-- data ν∞G (∞G : ∞Gram) : Set where
--   ▹ : ν⟦ ∞G .! ⟧ → ν∞G ∞G
-- 
-- ν⟦ ∅ ⟧ = ⊥
-- ν⟦ ε ⟧ = ⊤
-- ν⟦ ‵ c ⟧ = ⊥
-- ν⟦ A · G ⟧ = A × ν⟦ G ⟧
-- ν⟦ G₁ ∪ G₂ ⟧ = ν⟦ G₁ ⟧ ⊎ ν⟦ G₂ ⟧
-- ν⟦ G₁ ∙ G₂ ⟧ = ν⟦ G₁ ⟧ × ν⟦ G₂ ⟧
-- ν⟦ ▹ ∞G ⟧ = ν∞G ∞G

↔refl : A ↔ A
to ↔refl x = x
from ↔refl x = x

-- Γν-correct : Vec Lang n → Vec Set n → Set
-- Γν-correct Γ Γν = ∀ i → lookup Γν i ↔ ν (lookup Γ i)
-- 
-- lookup-map : (f : A → B) (v : Vec A n) (i : Fin n) → lookup (mapVec f v) i ≡ f (lookup v i)
-- lookup-map f (x ∷ v) zero = refl
-- lookup-map f (x ∷ v) (suc i) = lookup-map f v i
-- 
-- the-Γν : Vec (Gram m) n → Vec Lang m → Vec Set n
-- the-Γν Γ Γ′ = mapVec (λ G → ν ⟦ Γ′ ⊢ G ⟧) Γ
-- 
-- the-Γν-correct : (Γ : Vec (Gram m) n) → Γν-correct (mapVec (λ G → ⟦ Γ′ ⊢ G ⟧) Γ) (the-Γν Γ Γ′)
-- the-Γν-correct (G ∷ Γ) zero = ↔refl
-- the-Γν-correct (G ∷ Γ) (suc i) = the-Γν-correct Γ i

-- νG-sound : (G : Gram) → ν⟦ G ⟧ → ν ⟦ G ⟧
-- νG-sound ε x = refl
-- νG-sound (A · G) (x , y) = x , νG-sound G y
-- νG-sound (G₁ ∪ G₂) (inl x) = inl (νG-sound G₁ x)
-- νG-sound (G₁ ∪ G₂) (inr y) = inr (νG-sound G₂ y)
-- νG-sound (G₁ ∙ G₂) (pl , pr) = [] , [] , refl , νG-sound G₁ pl , νG-sound G₂ pr
-- νG-sound (▹ ∞G) (▹ x) = ▹ (νG-sound (! ∞G) x)
-- 
-- νG-complete : (G : Gram) → ν ⟦ G ⟧ → ν⟦ G ⟧
-- νG-complete ε x = tt
-- νG-complete (A · G) (x , y) = x , νG-complete G y
-- νG-complete (G ∪ G₁) (inl x) = inl (νG-complete G x)
-- νG-complete (G ∪ G₁) (inr x) = inr (νG-complete G₁ x)
-- νG-complete (G ∙ G₁) ([] , [] , refl , pl , pr) = νG-complete G pl , νG-complete G₁ pr
-- νG-complete (▹ ∞G) (▹ x) = ▹ (νG-complete (! ∞G) x)
-- 
-- νG-correct : (G : Gram) → ν⟦ G ⟧ ↔ ν ⟦ G ⟧
-- to (νG-correct G) = νG-sound G
-- from (νG-correct G) = νG-complete G

const : A → B → A
const x _ = x

-- fixG : Gram (suc n) → Gram n
-- 
-- fixG′ : Gram (suc n) → Gram (suc n) → Gram n
-- fixG′ G₀ ∅ = ∅
-- fixG′ G₀ ε = ε
-- fixG′ G₀ (‵ c) = ‵ c
-- fixG′ G₀ (A · G) = A · fixG′ G₀ G
-- fixG′ G₀ (G₁ ∪ G₂) = fixG′ G₀ G₁ ∪ fixG′ G₀ G₂
-- fixG′ G₀ (G₁ ∙ G₂) = fixG′ G₀ G₁ ∙ fixG′ G₀ G₂
-- fixG′ G₀ (var zero) = ▹ (λ { .! → fixG G₀ }) -- this is the special case
-- fixG′ G₀ (var (suc i)) = var i
-- fixG′ G₀ (▹ G) = ▹ (λ { .! → fixG′ G₀ (! G) })
-- 
-- fixG {n = n} G = fixG′ G G
-- 
-- -- Is fixG really a fixed point? Yes:
-- 
-- unroll : ∀ G → ⟦ Γ ⊢ fixG G ⟧ w → ⟦ (⟦ Γ ⊢ fixG G ⟧ ∷ Γ) ⊢ G ⟧ w
-- 
-- unroll′ : ∀ G {G₀} → ⟦ Γ ⊢ fixG′ G₀ G ⟧ w → ⟦ (⟦ Γ ⊢ fixG G₀ ⟧ ∷ Γ) ⊢ G ⟧ w
-- unroll′ ε x = x
-- unroll′ (‵ x₁) x = x
-- unroll′ (A · G) (x , y) = x , unroll′ G y
-- unroll′ (G₁ ∪ G₂) (inl x) = inl (unroll′ G₁ x)
-- unroll′ (G₁ ∪ G₂) (inr x) = inr (unroll′ G₂ x)
-- unroll′ (G₁ ∙ G₂) (u , v , refl , x , y) = u , v , refl , unroll′ G₁ x , unroll′ G₂ y
-- unroll′ (var zero) (▹ x) = x
-- unroll′ (var (suc i)) x = x
-- unroll′ (▹ G) (▹ x) = ▹ (unroll′ (! G) x)
-- 
-- unroll G = unroll′ G
-- 
-- roll : ∀ G → ⟦ (⟦ Γ ⊢ fixG G ⟧ ∷ Γ) ⊢ G ⟧ w → ⟦ Γ ⊢ fixG G ⟧ w 
-- 
-- roll′ : ∀{G₀} G → ⟦ (⟦ Γ ⊢ fixG G₀ ⟧ ∷ Γ) ⊢ G ⟧ w → ⟦ Γ ⊢ fixG′ G₀ G ⟧ w 
-- roll′ ε x = x
-- roll′ (‵ x₁) x = x
-- roll′ (A · G) (x , y) = x , roll′ G y
-- roll′ (G₁ ∪ G₂) (inl x) = inl (roll′ G₁ x)
-- roll′ (G₁ ∪ G₂) (inr x) = inr (roll′ G₂ x)
-- roll′ (G₁ ∙ G₂) (u , v , refl , x , y) = u , v , refl , roll′ G₁ x , roll′ G₂ y
-- roll′ (var zero) x = ▹ x
-- roll′ (var (suc i)) x = x
-- roll′ (▹ G) (▹ x) = ▹ (roll′ (! G) x) 
-- 
-- roll G = roll′ G
-- 
-- mapFix : ∀ G {G′} → (∀{Γ w} → ⟦ Γ ⊢ G ⟧ w → ⟦ Γ ⊢ G′ ⟧ w) → ⟦ Γ ⊢ fixG G ⟧ w → ⟦ Γ ⊢ fixG G′ ⟧ w
-- 
-- mapFixi : ∀ G {G₀ G′} → (∀{ℒ w} → ⟦ ℒ ∷ Γ ⊢ G ⟧ w → ⟦ ℒ ∷ Γ ⊢ G′ ⟧ w) → ⟦ Γ ⊢ fixG′ G₀ G ⟧ w → ⟦ Γ ⊢ fixG′ G₀ G′ ⟧ w
-- mapFixi G {G₀} {G′} f x = roll′ G′ (f (unroll′ G x))
-- 
-- mapFixo : ∀{G₀ G₀′} (G : Gram _) → (∀{Γ w} → ⟦ Γ ⊢ G₀ ⟧ w → ⟦ Γ ⊢ G₀′ ⟧ w) → ⟦ Γ ⊢ fixG′ G₀ G ⟧ w → ⟦ Γ ⊢ fixG′ G₀′ G ⟧ w
-- mapFixo ε f x = x
-- mapFixo (‵ x₁) f x = x
-- mapFixo (_ · G) f (x , y) = x , mapFixo G f y
-- mapFixo (G ∪ G₁) f (inl x) = inl (mapFixo G f x)
-- mapFixo (G ∪ G₁) f (inr x) = inr (mapFixo G₁ f x)
-- mapFixo (G ∙ G₁) f (u , v , refl , x , y) = u , v , refl , mapFixo G f x , mapFixo G₁ f y
-- mapFixo {G₀ = G₀} {G₀′} (var zero) f (▹ x) = ▹ (mapFix G₀ {G₀′} f x)
-- mapFixo (var (suc i)) f x = x
-- mapFixo (▹ G) f (▹ x) = ▹ (mapFixo (! G) f x)
-- 
-- mapFix G {G′} f x = mapFixi G {_} {G′} f (mapFixo G f x)
-- 
-- -- Using this fixed point we can define a finite syntactic representation of grammars,
-- -- which are indexed by their corresponding (possibly) infinite grammar representation:

data DecGram (n : ℕ) : Set₁ where
    ∅ : DecGram n
    ε : DecGram n
    ‵_ : (c : Tok) → DecGram n
    _·_ : Dec A → DecGram n → DecGram n
    _∪_ : DecGram n → DecGram n → DecGram n
    _∙_ : DecGram n → DecGram n → DecGram n
    var : (i : Fin n) → DecGram n
    μ : DecGram (suc n) → DecGram n

setOf : Dec A → Set
setOf {A = A} _ = A

cons : A → (Fin n → A) → (Fin (suc n) → A)
cons x f zero = x
cons _ f (suc i) = f i

nil : Fin zero → A
nil ()

renameD : (Fin n → Fin m) → DecGram n → DecGram m
renameD f ∅ = ∅
renameD f ε = ε
renameD f (‵ c) = ‵ c
renameD f (x · G) = x · renameD f G
renameD f (G ∪ G₁) = renameD f G ∪ renameD f G₁
renameD f (G ∙ G₁) = renameD f G ∙ renameD f G₁
renameD f (var i) = var (f i)
renameD f (μ G) = μ (renameD (cons zero (suc ∘ f)) G)

substD : DecGram n → (Fin n → DecGram m) → DecGram m
substD ∅ k = ∅
substD ε k = ε
substD (‵ c) k = ‵ c
substD (x · G₁) k = x · substD G₁ k
substD (G₁ ∪ G₃) k = substD G₁ k ∪ substD G₃ k
substD (G₁ ∙ G₃) k = substD G₁ k ∙ substD G₃ k
substD (var i) k = k i
substD (μ G₁) k = μ (substD G₁ (cons (var zero) (renameD suc ∘ k)))

_⊢_ : (Fin n → DecGram m) → DecGram n → DecGram m
Γ ⊢ ∅ = ∅
Γ ⊢ ε = ε
Γ ⊢ (‵ c) = ‵ c
Γ ⊢ (x · G₁) = x · (Γ ⊢ G₁)
Γ ⊢ (G₁ ∪ G₃) = (Γ ⊢ G₁)  ∪ (Γ ⊢ G₃)
Γ ⊢ (G₁ ∙ G₃) = (Γ ⊢ G₁) ∙ (Γ ⊢ G₃)
Γ ⊢ (var i) = Γ i
Γ ⊢ (μ G₁) = μ (cons (var zero) (renameD suc ∘ Γ) ⊢ G₁)

postulate funext : {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g

f∘cons : ∀ {f : A → B} {x xs} (i : Fin (suc n)) → f (cons x xs i) ≡ cons (f x) (f ∘ xs) i
f∘cons zero = refl
f∘cons (suc i) = refl

rename≡⊢ : {f : Fin n → Fin m} {G : DecGram n} → renameD f G ≡ (var ∘ f) ⊢ G
rename≡⊢ {G = ∅} = refl
rename≡⊢ {G = ε} = refl
rename≡⊢ {G = ‵ c} = refl
rename≡⊢ {G = x · G} = cong (x ·_) rename≡⊢
rename≡⊢ {G = G ∪ G₁} = cong₂ _∪_ rename≡⊢ rename≡⊢
rename≡⊢ {G = G ∙ G₁} = cong₂ _∙_ rename≡⊢ rename≡⊢
rename≡⊢ {G = var i} = refl
rename≡⊢ {G = μ G} = cong μ (trans rename≡⊢ (cong (_⊢ G) (funext (f∘cons {f = var}))))

-- D⟦_⟧ : DecGram zero → Gram
-- D⟦ ∅ ⟧ = ∅
-- D⟦ ε ⟧ = ε
-- D⟦ ‵ c ⟧ = ‵ c
-- D⟦ x · G ⟧ = setOf x · D⟦ G ⟧
-- D⟦ G ∪ G₁ ⟧ = D⟦ G ⟧ ∪ D⟦ G₁ ⟧
-- D⟦ G ∙ G₁ ⟧ = D⟦ G ⟧ ∙ D⟦ G₁ ⟧
-- D⟦ μ G ⟧ = ▹ λ { .! → D⟦ substD G (λ { zero → μ G ; (suc i) → var i }) ⟧ }

-- _+_ : ℕ → ℕ → ℕ
-- zero + x = x
-- (suc x) + y = suc (x + y)
-- 
-- _+++_ : Vec A n → Vec A m → Vec A (n + m)
-- [] +++ xs = xs
-- (x ∷ xs) +++ ys = x ∷ (xs +++ ys)
-- 
-- tabulate : (Fin n → A) → Vec A n
-- tabulate {zero} f = []
-- tabulate {suc n} f = f zero ∷ tabulate {n} λ i → f (suc i)

⟦_⊢_⟧ : Vec Lang n → DecGram n → Lang

data ▹⟦_⊢_⟧ (Γ : Vec Lang n) (G : DecGram n) (w : List Tok) : Set where
  ▹ : ⟦ Γ ⊢ G ⟧ w → ▹⟦ Γ ⊢ G ⟧ w

⟦ Γ ⊢ ∅ ⟧ = λ _ → ⊥
⟦ Γ ⊢ ε ⟧ = λ w → w ≡ []
⟦ Γ ⊢ ‵ c ⟧ = λ w → w ≡ (c ∷ [])
⟦ Γ ⊢ x · G ⟧ w = setOf x × ⟦ Γ ⊢ G ⟧ w
⟦ Γ ⊢ G ∪ G₁ ⟧ w = ⟦ Γ ⊢ G ⟧ w ⊎ ⟦ Γ ⊢ G₁ ⟧ w
⟦ Γ ⊢ G ∙ G₁ ⟧ w = ∃ λ u → ∃ λ v → (w ≡ u ++ v) × ⟦ Γ ⊢ G ⟧ u × ⟦ Γ ⊢ G₁ ⟧ v
⟦ Γ ⊢ μ G ⟧ = ▹⟦ ⟦ Γ ⊢ μ G ⟧ ∷ Γ ⊢ G ⟧

-- _⊎?_ : Dec A → Dec B → Dec (A ⊎ B)
-- yes x ⊎? y = yes (inl x)
-- no x ⊎? yes x₁ = yes (inr x₁)
-- no x ⊎? no x₁ = no (λ { (inl y) → x y ; (inr y) → x₁ y })
-- 
-- _×?_ : Dec A → Dec B → Dec (A × B)
-- yes x ×? yes x₁ = yes (x , x₁)
-- yes x ×? no x₁ = no (λ z → x₁ (_×_.pr z))
-- no x ×? y = no (λ z → x (_×_.pl z))
-- 
-- rename-rename : ∀{n n′ n″} {f : Fin n′ → Fin n″} {g : Fin n → Fin n′} (G : DecGram n) → renameD f (renameD g G) ≡ renameD (f ∘ g) G
-- rename-rename ∅ = refl
-- rename-rename ε = refl
-- rename-rename (‵ c) = refl
-- rename-rename (x · G) = cong (x ·_) (rename-rename G)
-- rename-rename (G ∪ G₁) = cong₂ _∪_ (rename-rename G) (rename-rename G₁)
-- rename-rename (G ∙ G₁) = cong₂ _∙_ (rename-rename G) (rename-rename G₁)
-- rename-rename (var i) = refl
-- rename-rename (μ G) = cong μ (trans (rename-rename G) (cong (λ X → renameD X G) (funext (f∘cons {f = cons _ _}))))
-- 
-- rename-subst : ∀ {n₁ n₂ n₃} (G : DecGram n₁) {f : Fin n₂ → Fin n₃} {k : Fin n₁ → DecGram n₂}
--                → renameD f (substD G k) ≡ substD G (renameD f ∘ k)
-- rename-subst ∅ = refl
-- rename-subst ε = refl
-- rename-subst (‵ c) = refl
-- rename-subst (x · G) = cong (x ·_) (rename-subst G)
-- rename-subst (G ∪ G₁) = cong₂ _∪_ (rename-subst G) (rename-subst G₁)
-- rename-subst (G ∙ G₁) = cong₂ _∙_ (rename-subst G) (rename-subst G₁)
-- rename-subst (var i) = refl
-- rename-subst (μ G) {f = f} {k = k} = cong μ (trans (rename-subst G) (cong (substD G) (funext (λ i → trans (f∘cons {f = renameD _} i) (cong (λ X → cons (var zero) X i) (funext λ i → trans (rename-rename (k i)) (sym (rename-rename (k i)))))))))
-- -- (trans (cong (substD G) (funext λ where
-- --   zero → refl
-- --   (suc i) → trans (rename-rename {f = suc} {g = f} (k i)) (sym (rename-rename {f = cons zero (suc ∘ f)} {g = suc} (k i)))
-- --    )) (rename-subst G))
-- 
-- subst-rename-G : ∀ {n′} {k : Fin m → DecGram n′} {f : Fin n → Fin m} (G : DecGram n) → substD (renameD f G) k ≡ substD G (k ∘ f)
-- subst-rename-G ∅ = refl
-- subst-rename-G ε = refl
-- subst-rename-G (‵ c) = refl
-- subst-rename-G (x · G) = cong (x ·_) (subst-rename-G G)
-- subst-rename-G (G ∪ G₁) = cong₂ _∪_ (subst-rename-G G) (subst-rename-G G₁)
-- subst-rename-G (G ∙ G₁) = cong₂ _∙_ (subst-rename-G G) (subst-rename-G G₁)
-- subst-rename-G (var i) = refl
-- subst-rename-G (μ G) = cong μ (trans (subst-rename-G G) (cong (substD G) (funext λ where
--   zero → refl
--   (suc i) → refl
--    )))
-- 
-- subst-subst : ∀ {n m₁ m₂} (G : DecGram n) (k₁ : Fin n → DecGram m₁) (k₂ : Fin m₁ → DecGram m₂)
--             → substD (substD G (λ i → k₁ i)) (λ i → k₂ i) ≡ substD G (λ i → substD (k₁ i) (λ i → k₂ i))
-- subst-subst ∅ k₁ k₂ = refl
-- subst-subst ε k₁ k₂ = refl
-- subst-subst (‵ c) k₁ k₂ = refl
-- subst-subst (x · G) k₁ k₂ = cong (x ·_) (subst-subst G k₁ k₂)
-- subst-subst (G ∪ G₁) k₁ k₂ = cong₂ _∪_ (subst-subst G k₁ k₂) (subst-subst G₁ k₁ k₂)
-- subst-subst (G ∙ G₁) k₁ k₂ = cong₂ _∙_ (subst-subst G k₁ k₂) (subst-subst G₁ k₁ k₂)
-- subst-subst (var i) k₁ k₂ = refl
-- subst-subst (μ G) k₁ k₂ = cong μ (trans (subst-subst G (cons (var zero) (renameD suc ∘ k₁)) (cons (var zero) (renameD suc ∘ k₂))) (cong (substD G) (funext (λ where
--   zero → refl
--   (suc i) → trans (subst-rename-G (k₁ i)) (sym (rename-subst (k₁ i)))
--     ))))
-- 
-- -- νDμ-to : {k : Vec (DecGram zero) n} (G : DecGram (suc n))
-- --          (x : ν ⟦ substD G (lookup (∅ ∷ k)) ⟧) →
-- --          ν ⟦ substD (μ G) (lookup k) ⟧
-- -- νDμ-to G x = ▹ {!!}
-- -- -- νDμ-to ε x = ▹ refl
-- -- -- νDμ-to (x₁ · G) (x , y) = {!!}
-- -- -- νDμ-to (G ∪ G₁) x = {!!}
-- -- -- νDμ-to (G ∙ G₁) x = {!!}
-- -- -- νDμ-to (var i) x = {!!}
-- -- -- νDμ-to (μ G) x = {!!}
-- 
-- ↔trans : A ↔ B → B ↔ C → A ↔ C
-- ↔trans bi₁ bi₂ .to = bi₂ .to ∘ bi₁ .to
-- ↔trans bi₁ bi₂ .from = bi₁ .from ∘ bi₂ .from
-- 
-- ≡→↔ : {G₁ G₂ : DecGram zero} → G₁ ≡ G₂ → ⟦ G₁ ⟧ w ↔ ⟦ G₂ ⟧ w 
-- ≡→↔ refl = ↔refl
-- 
-- cons-var : (i : Fin (suc n)) → cons (var zero) (renameD suc ∘ var) i ≡ var i
-- cons-var zero = refl
-- cons-var (suc i) = refl
-- 
-- subst-var : (G : DecGram n) → substD G var ≡ G
-- subst-var ∅ = refl
-- subst-var ε = refl
-- subst-var (‵ c) = refl
-- subst-var (x · G) = cong (x ·_) (subst-var G)
-- subst-var (G ∪ G₁) = cong₂ _∪_ (subst-var G) (subst-var G₁)
-- subst-var (G ∙ G₁) = cong₂ _∙_ (subst-var G) (subst-var G₁)
-- subst-var (var i) = refl
-- subst-var (μ G) = cong μ
--   (begin
--   substD G (cons (var zero) (renameD suc ∘ var))
--   ≡⟨ cong (substD G) (funext cons-var) ⟩
--   substD G var
--   ≡⟨ subst-var G ⟩
--   G
--   ∎)
-- 
-- roll : (k : Fin n → DecGram zero) (G : DecGram (suc n))
--      → ⟦ substD (μ G) k ⟧ w ↔ ⟦ substD G (cons (substD (μ G) k) k) ⟧ w
-- roll {w = w} k G = ↔trans (record { to = λ { (▹ x) → x } ; from = ▹ })
--   (≡→↔ {G₁ = substD (substD G (cons (var zero) (λ z → renameD suc (k z))))
--               (cons (μ (substD G (cons (var zero) (λ z → renameD suc (k z)))))
--                nil)} {G₂ = substD G
--                                (cons (μ (substD G (cons (var zero) (λ z → renameD suc (k z))))) k)}
--     (trans (subst-subst G (cons (var zero) _) _) (cong (substD G) (funext (λ where
--       zero → refl
--       (suc i) → trans (subst-rename-G (k i)) (trans (cong (substD (k i)) (funext (λ ()))) (subst-var (k i)))
--         )))))
-- 
-- νDμ-to : ∀ G {G₀} →
--          ν ⟦ substD G (cons ∅ nil) ⟧ → ν ⟦ substD G (cons (μ G₀) nil) ⟧
-- νDμ-to ε x = refl
-- νDμ-to (x₁ · G) (x , y) = x , νDμ-to G y
-- νDμ-to (G ∪ G₁) (inl x) = inl (νDμ-to G x)
-- νDμ-to (G ∪ G₁) (inr x) = inr (νDμ-to G₁ x)
-- νDμ-to (G ∙ G₁) ([] , [] , refl , x , y) = [] , [] , refl , νDμ-to G x , νDμ-to G₁ y
-- νDμ-to (var zero) ()
-- νDμ-to (var (suc ()))
-- νDμ-to (μ G) (▹ x) = ▹
--   let x = subst (λ G → ν ⟦ G ⟧)
--             (begin
--                substD (substD G (cons (var zero) (renameD suc ∘ cons ∅ nil))) (cons (μ (substD G (cons (var zero) (renameD suc ∘ cons ∅ nil)))) nil)
--             ≡⟨ subst-subst G _ _ ⟩
--                substD G
--                 (λ z →
--                    substD (cons (var zero) (renameD suc ∘ cons ∅ nil) z)
--                    (cons (μ (substD G (cons (var zero) (renameD suc ∘ cons ∅ nil))))
--                     nil))
--             ≡⟨ {!!} ⟩
--                substD G (cons (μ (substD G (cons (var zero) (cons ∅ nil)))) (cons ∅ nil))
--             ∎)
--             x
--   in {!!}
-- --   let x = subst (λ G → ⟦ G ⟧ []) (subst-subst G _ _) x
-- --       x = subst (λ k → ν ⟦ substD G k ⟧) (funext λ where
-- --         zero → cong μ {!!}
-- --         (suc i) → subst-rename-G (cons ∅ nil i)
-- --          ) x
-- --   in {!!}
-- 
-- νDμ : {G : DecGram (suc zero)} →
--       ν ⟦ substD G (cons ∅ nil) ⟧ ↔
--       ν ⟦ substD G (cons (μ G) nil) ⟧
-- to (νDμ {G = G}) = {!νDμ-to G!}
-- from (νDμ {G = G}) = {!!}
-- 
-- -- νD : (k : Vec (DecGram zero) n) (Γ : ∀ i → Dec (ν ⟦ lookup k i ⟧)) (G : DecGram n) → Dec (ν ⟦ substD G (lookup k) ⟧)
-- -- νD k Γ ∅ = no (λ z → z)
-- -- νD k Γ ε = yes refl
-- -- νD k Γ (‵ c) = no (λ ())
-- -- νD k Γ (x · G) = x ×? νD k Γ G
-- -- νD k Γ (G ∪ G₁) = νD k Γ G ⊎? νD k Γ G₁
-- -- νD k Γ (G ∙ G₁) = mapDec (record { to = λ (x , y) → [] , [] , refl , x , y ; from = λ where ([] , [] , refl , x , y) → x , y })
-- --                        (νD k Γ G ×? νD k Γ G₁)
-- -- νD k Γ (var i) = Γ i
-- -- νD k Γ (μ G) = mapDec (νDμ {Γ = Γ} {G = G}) (νD (∅ ∷ k) (λ { zero → no λ () ; (suc i) → Γ i }) G)
-- -- 
-- -- -- -- this needs to be made a constructor, that shouldn't cause problems but is some work
-- -- -- _◃_ : (∀ {Γ} {w} → ⟦ Γ ⊢ G₁ ⟧ w ↔ ⟦ Γ ⊢ G₂ ⟧ w) → DecGram n G₁ → DecGram n G₂
-- -- -- _◃_ = {!!}
-- -- -- 
-- -- -- consrn : ∀{n m} → (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
-- -- -- consrn f zero = zero
-- -- -- consrn f (suc i) = suc (f i)
-- -- -- 
-- -- -- conssub : (Fin n → Gram m) → Fin (suc n) → Gram (suc m)
-- -- -- conssub k zero = var zero
-- -- -- conssub k (suc i) = renameG suc (k i)
-- -- -- 
-- -- -- ↔cong : (f : Set → Set) (map : ∀{X Y : Set} → (X → Y) → f X → f Y) → A ↔ B → f A ↔ f B
-- -- -- ↔cong f map bi .to x = map (bi .to) x
-- -- -- ↔cong f map bi .from x = map (bi .from) x
-- -- -- 
-- -- -- ↔cong₂ : ∀{A₁ A₂ B₁ B₂} (f : Set → Set → Set) (map : ∀{X₁ X₂ Y₁ Y₂ : Set} → (X₁ → Y₁) → (X₂ → Y₂) → f X₁ X₂ → f Y₁ Y₂) → A₁ ↔ B₁ → A₂ ↔ B₂ → f A₁ A₂ ↔ f B₁ B₂
-- -- -- ↔cong₂ f map bi₁ bi₂ .to x = map (bi₁ .to) (bi₂ .to) x
-- -- -- ↔cong₂ f map bi₁ bi₂ .from x = map (bi₁ .from) (bi₂ .from) x
-- -- -- 
-- -- -- subrn : (G : Gram _) (f : Fin n → Fin m) → ⟦ Γ ⊢ substG G (conssub (var ∘ f)) ⟧ w ↔ ⟦ Γ ⊢ substG G (var ∘ consrn f) ⟧ w
-- -- -- subrn ∅ f .to ()
-- -- -- subrn ε f .to x = x
-- -- -- subrn (‵ c) f .to x = x
-- -- -- subrn (A · G) f .to (pl₁ , pr₁) = pl₁ , subrn G f .to pr₁
-- -- -- subrn (G₁ ∪ G₂) f .to (inl x) = inl (subrn G₁ f .to x)
-- -- -- subrn (G₁ ∪ G₂) f .to (inr x) = inr (subrn G₂ f .to x)
-- -- -- subrn (G₁ ∙ G₂) f .to (u , v , refl , x , y) = u , v , refl , subrn G₁ f .to x , subrn G₂ f .to y
-- -- -- subrn (▹ ∞G) f .to (▹ x) = ▹ (subrn (∞G .!) f .to x)
-- -- -- subrn ∅ f .from ()
-- -- -- subrn ε f .from x = x
-- -- -- subrn (‵ c) f .from x = x
-- -- -- subrn (A · G) f .from (pl₁ , pr₁) = pl₁ , subrn G f .from pr₁
-- -- -- subrn (G₁ ∪ G₂) f .from (inl x) = inl (subrn G₁ f .from x)
-- -- -- subrn (G₁ ∪ G₂) f .from (inr x) = inr (subrn G₂ f .from x)
-- -- -- subrn (G₁ ∙ G₂) f .from (u , v , refl , x , y) = u , v , refl , subrn G₁ f .from x , subrn G₂ f .from y
-- -- -- subrn (▹ ∞G) f .from (▹ x) = ▹ (subrn (∞G .!) f .from x)
-- -- -- -- special cases:
-- -- -- subrn (var zero) f = ↔refl
-- -- -- subrn (var (suc i)) f = ↔refl
-- -- -- 
-- -- -- renamesuc : ∀ G → ⟦ ℒ ∷ Γ ⊢ renameG suc G ⟧ w ↔ ⟦ Γ ⊢ G ⟧ w
-- -- -- renamesuc ε .to x = x
-- -- -- renamesuc (‵ c) .to x = x
-- -- -- renamesuc (A · G) .to (pl₁ , pr₁) = pl₁ , renamesuc G .to pr₁
-- -- -- renamesuc (G ∪ G₁) .to (inl x) = inl (renamesuc G .to x)
-- -- -- renamesuc (G ∪ G₁) .to (inr x) = inr (renamesuc G₁ .to x)
-- -- -- renamesuc (G ∙ G₁) .to (u , v , refl , x , y) = u , v , refl , renamesuc G .to x , renamesuc G₁ .to y
-- -- -- renamesuc (var i) .to x = x
-- -- -- renamesuc (▹ ∞G) .to (▹ x) = ▹ (renamesuc (∞G .!) .to x)
-- -- -- 
-- -- -- renamesuc ε .from x = x
-- -- -- renamesuc (‵ c) .from x = x
-- -- -- renamesuc (A · G) .from (pl₁ , pr₁) = pl₁ , renamesuc G .from pr₁
-- -- -- renamesuc (G ∪ G₁) .from (inl x) = inl (renamesuc G .from x)
-- -- -- renamesuc (G ∪ G₁) .from (inr x) = inr (renamesuc G₁ .from x)
-- -- -- renamesuc (G ∙ G₁) .from (u , v , refl , x , y) = u , v , refl , renamesuc G .from x , renamesuc G₁ .from y
-- -- -- renamesuc (var i) .from x = x
-- -- -- renamesuc (▹ ∞G) .from (▹ x) = ▹ (renamesuc (∞G .!) .from x)
-- -- -- 
-- -- -- substFixG : ∀{n m} {Γ : Vec Lang m} (G : Gram (suc n)) {G₀ : Gram (suc n)} (k : Fin n → Gram m) → ⟦ Γ ⊢ substG (fixG′ G₀ G) k ⟧ w ↔ ⟦ Γ ⊢ fixG′ (substG G₀ (conssub k)) (substG G (conssub k)) ⟧ w
-- -- -- substFixG ε k .to x = x
-- -- -- substFixG (‵ c) k .to x = x
-- -- -- substFixG (A · G) k .to (x , y) = x , substFixG G k .to y
-- -- -- substFixG (G₁ ∪ G₂) k .to (inl x) = inl (substFixG G₁ k .to x)
-- -- -- substFixG (G₁ ∪ G₂) k .to (inr x) = inr (substFixG G₂ k .to x)
-- -- -- substFixG (G₁ ∙ G₂) k .to (u , v , refl , x , y) = u , v , refl , substFixG G₁ k .to x , substFixG G₂ k . to y
-- -- -- substFixG (var zero) {G₀ = G₀} k .to (▹ x) = ▹ (substFixG G₀ k .to x)
-- -- -- substFixG {n = suc n} (var (suc i)) {G₀} k .to x = roll′ (renameG suc (k i)) (renamesuc (k i) .from x)
-- -- -- substFixG (▹ ∞G) k .to (▹ x) = ▹ (substFixG (∞G .!) k .to x)
-- -- -- substFixG ε k .from x = x
-- -- -- substFixG (‵ c) k .from x = x
-- -- -- substFixG (A · G) k .from (pl₁ , pr₁) = pl₁ , substFixG G k .from pr₁
-- -- -- substFixG (G ∪ G₁) k .from (inl x) = inl (substFixG G k .from x)
-- -- -- substFixG (G ∪ G₁) k .from (inr x) = inr (substFixG G₁ k .from x)
-- -- -- substFixG (G ∙ G₁) k .from (u , v , refl , x , y) = u , v , refl , substFixG G k .from x , substFixG G₁ k .from y
-- -- -- substFixG (var zero) {G₀} k .from (▹ x) = ▹ (substFixG G₀ k .from x)
-- -- -- substFixG {n = suc n} (var (suc i)) {G₀} k .from x = renamesuc (k i) .to (unroll′ (renameG suc (k i)) {substG G₀ (conssub k)} x)
-- -- -- substFixG (▹ ∞G) k .from (▹ x) = ▹ (substFixG (∞G .!) k .from x)
-- -- -- 
-- -- -- renameFixG : ∀{n m} {Γ : Vec Lang m} (G : Gram (suc n)) (f : Fin n → Fin m) → ⟦ Γ ⊢ renameG f (fixG G) ⟧ w ↔ ⟦ Γ ⊢ fixG (renameG (consrn f) G) ⟧ w
-- -- -- renameFixG {n = n} {m} {Γ} G f .to x = mapFix (substG G (conssub (var ∘ f))) {substG G (var ∘ consrn f)} (subrn G f .to) (substFixG {Γ = Γ} G {G} (var ∘ f) .to x)
-- -- -- renameFixG {n = n} {m} {Γ} G f .from x = substFixG {Γ = Γ} G {G} (var ∘ f) .from (mapFix (substG G (var ∘ consrn f)) {substG G (conssub (var ∘ f))} (subrn G f .from) x)
-- -- -- 
-- -- -- ↔sym : A ↔ B → B ↔ A
-- -- -- to (↔sym bi) = from bi
-- -- -- from (↔sym bi) = to bi
-- -- -- 
-- -- -- renameD : ∀{n m G} → (f : Fin n → Fin m) → DecGram n G → DecGram m (renameG f G)
-- -- -- renameD f ∅ = ∅
-- -- -- renameD f ε = ε
-- -- -- renameD f (‵ c) = ‵ c
-- -- -- renameD f (x · D) = x · renameD f D
-- -- -- renameD f (D ∪ D₁) = renameD f D ∪ renameD f D₁
-- -- -- renameD f (D ∙ D₁) = renameD f D ∙ renameD f D₁
-- -- -- renameD f (var i) = var (f i)
-- -- -- renameD f (μ {G = G} D) = (↔sym (renameFixG G f)) ◃ μ (renameD (consrn f) D)
-- -- -- 
-- -- -- 
-- -- -- fixGsuc-to : (G : Gram n) {G₀ : Gram _} → ⟦ Γ ⊢ fixG′ G₀ (renameG suc G) ⟧ w → ⟦ Γ ⊢ G ⟧ w
-- -- -- fixGsuc-to G x = renamesuc G .to (unroll′ (renameG suc G) x)
-- -- -- 
-- -- -- fixGsuc-from : (G : Gram n) {G₀ : Gram _} → ⟦ Γ ⊢ G ⟧ w → ⟦ Γ ⊢ fixG′ G₀ (renameG suc G) ⟧ w
-- -- -- fixGsuc-from G x = roll′ (renameG suc G) (renamesuc G .from x)
-- -- -- 
-- -- -- variable σ : Vec (Gram m) n
-- -- -- 
-- -- -- substDμ : (G : Gram _) → ⟦ Γ ⊢ fixG (substG G (lookup (var zero ∷ mapVec (renameG suc) σ))) ⟧ w ↔ ⟦ Γ ⊢ substG (fixG G) (lookup σ) ⟧ w
-- -- -- 
-- -- -- substDμ-to : (G : Gram _) {G₀ : Gram _} → ⟦ Γ ⊢ fixG′ (substG G₀ (lookup (var zero ∷ mapVec (renameG suc) σ))) (substG G (lookup (var zero ∷ mapVec (renameG suc) σ))) ⟧ w → ⟦ Γ ⊢ substG (fixG′ G₀ G) (lookup σ) ⟧ w
-- -- -- substDμ-to ε x = x
-- -- -- substDμ-to (‵ c) x = x
-- -- -- substDμ-to (A · G) (x , y) = x , substDμ-to G y 
-- -- -- substDμ-to (G ∪ G₁) (inl x) = inl (substDμ-to G x)
-- -- -- substDμ-to (G ∪ G₁) (inr x) = inr (substDμ-to G₁ x)
-- -- -- substDμ-to (G ∙ G₁) (u , v , refl , x , y) = u , v , refl , substDμ-to G x , substDμ-to G₁ y
-- -- -- substDμ-to (var zero) {G₀} (▹ x) = ▹ (substDμ-to G₀ x)
-- -- -- substDμ-to {σ = σ} (var (suc i)) {G₀} x = fixGsuc-to (lookup σ i) (subst (λ X → ⟦ _ ⊢ fixG′ _ X ⟧ _) (lookup-map (renameG suc) σ i) x)
-- -- -- substDμ-to (▹ ∞G) (▹ x) = ▹ (substDμ-to (∞G .!) x)
-- -- -- 
-- -- -- 
-- -- -- substDμ-from : (G : Gram _) {G₀ : Gram _} → ⟦ Γ ⊢ substG (fixG′ G₀ G) (lookup σ) ⟧ w → ⟦ Γ ⊢ fixG′ (substG G₀ (lookup (var zero ∷ mapVec (renameG suc) σ))) (substG G (lookup (var zero ∷ mapVec (renameG suc) σ))) ⟧ w
-- -- -- substDμ-from ε x = x
-- -- -- substDμ-from (‵ c) x = x
-- -- -- substDμ-from (A · G) (x , y) = x , substDμ-from G y 
-- -- -- substDμ-from (G ∪ G₁) (inl x) = inl (substDμ-from G x)
-- -- -- substDμ-from (G ∪ G₁) (inr x) = inr (substDμ-from G₁ x)
-- -- -- substDμ-from (G ∙ G₁) (u , v , refl , x , y) = u , v , refl , substDμ-from G x , substDμ-from G₁ y
-- -- -- substDμ-from (var zero) {G₀} (▹ x) = ▹ (substDμ-from G₀ x)
-- -- -- substDμ-from {σ = σ} (var (suc i)) {G₀} x = subst (λ X → ⟦ _ ⊢ fixG′ _ X ⟧ _) (sym (lookup-map (renameG suc) σ i)) (fixGsuc-from (lookup σ i) x)
-- -- -- substDμ-from (▹ ∞G) (▹ x) = ▹ (substDμ-from (∞G .!) x)
-- -- -- 
-- -- -- substDμ G .to x = substDμ-to G x
-- -- -- substDμ G .from x = substDμ-from G x
-- -- -- 
-- -- -- substD : (σ : Vec (Gram m) n) → DecGram n G → ((i : Fin n) → DecGram m (lookup σ i)) → DecGram m (substG G (lookup σ))
-- -- -- substD σ ∅ k = ∅
-- -- -- substD σ ε k = ε
-- -- -- substD σ (‵ c) k = ‵ c
-- -- -- substD σ (x · G) k = x · substD σ G k
-- -- -- substD σ (G ∪ G₁) k = substD σ G k ∪ substD σ G₁ k
-- -- -- substD σ (G ∙ G₁) k = substD σ G k ∙ substD σ G₁ k
-- -- -- substD σ (var i) k = k i
-- -- -- substD σ (μ {G = G′} G) k = substDμ G′ ◃ μ (substD (var zero ∷ mapVec (renameG suc) σ) G λ { zero → var zero ; (suc i) → subst (λ X → DecGram (suc _) X) (sym (lookup-map (renameG suc) σ i)) (renameD suc (k i)) })
-- -- -- 
-- -- -- -- example
-- -- -- 
-- -- -- expr′ : DecGram n _
-- -- -- expr′ = μ (‵ x ∪ var zero ∙ ‵ + ∙ var zero) where open Tok
-- -- -- 
-- -- -- -- nullability
-- -- --
-- -- -- 
-- -- -- ν? : (D : DecGram n) → Dec (ν⟦ D⟦ substD D (λ i → ∅) ⟧ ⟧)
-- -- -- ν? ∅ = no λ ()
-- -- -- ν? ε = yes tt
-- -- -- ν? (‵ c) = no λ ()
-- -- -- ν? (x · D) = x ×? (ν? D)
-- -- -- ν? (D ∪ D₁) = ν? D ⊎? ν? D₁
-- -- -- ν? (D ∙ D₁) = ν? D ×? ν? D₁
-- -- -- ν? (var i) = no λ ()
-- -- -- ν? (μ D) = mapDec (record { to = λ x → ▹ {!!} ; from = λ where (▹ x) → {!!} }) (ν? D)
-- -- -- 
-- -- -- 
-- -- -- νfix-to : ∀ {G₀} G → ν⟦ (⊥ ∷ Γν) ⊢ G ⟧ → ν⟦ Γν ⊢ fixG′ G₀ G ⟧
-- -- -- νfix-to ε _ = tt
-- -- -- νfix-to (A · G) (x , y) = x , νfix-to G y
-- -- -- νfix-to (G₁ ∪ G₂) (inl x) = inl (νfix-to G₁ x)
-- -- -- νfix-to (G₁ ∪ G₂) (inr x) = inr (νfix-to G₂ x)
-- -- -- νfix-to (G₁ ∙ G₂) (pl , pr) = νfix-to G₁ pl , νfix-to G₂ pr
-- -- -- νfix-to (var (suc i)) x = x
-- -- -- νfix-to (▹ G) (▹ x) = ▹ (νfix-to (! G) x)
-- -- -- 
-- -- -- ⊎mapl : ∀{C} → (A → C) → A ⊎ B → C ⊎ B
-- -- -- ⊎mapl f (inl x) = inl (f x)
-- -- -- ⊎mapl f (inr x) = inr x
-- -- -- 
-- -- -- ⊎lift2l : ∀{C D} → (A → B → C) → A ⊎ D → B ⊎ D → C ⊎ D
-- -- -- ⊎lift2l f (inl x) (inl x₁) = inl (f x x₁)
-- -- -- ⊎lift2l f (inl x) (inr x₁) = inr x₁
-- -- -- ⊎lift2l f (inr x) y = inr x
-- -- -- 
-- -- -- ⊎collapse : A ⊎ A → A
-- -- -- ⊎collapse (inl x) = x
-- -- -- ⊎collapse (inr x) = x
-- -- -- 
-- -- -- νfix-from : ∀ {G₀} G → ν⟦ Γν ⊢ fixG′ G₀ G ⟧ → ν⟦ (⊥ ∷ Γν) ⊢ G ⟧ ⊎ ν⟦ (⊥ ∷ Γν) ⊢ G₀ ⟧
-- -- -- νfix-from ε _ = inl tt
-- -- -- νfix-from (A · G) (x , y) = ⊎mapl (x ,_) (νfix-from G y)
-- -- -- νfix-from (G ∪ G₁) (inl x) = ⊎mapl inl (νfix-from G x)
-- -- -- νfix-from (G ∪ G₁) (inr x) = ⊎mapl inr (νfix-from G₁ x)
-- -- -- νfix-from (G ∙ G₁) (pl , pr) = ⊎lift2l _,_ (νfix-from G pl) (νfix-from G₁ pr)
-- -- -- νfix-from {G₀ = G₀} (var zero) (▹ x) = inr (⊎collapse (νfix-from G₀ x))
-- -- -- νfix-from (var (suc i)) x = inl x
-- -- -- νfix-from (▹ G) (▹ x) = ⊎mapl ▹ (νfix-from (! G) x)
-- -- -- 
-- -- -- νfix : ∀ G → ν⟦ (⊥ ∷ Γν) ⊢ G ⟧ ↔ ν⟦ Γν ⊢ fixG G ⟧
-- -- -- to (νfix G) = νfix-to G
-- -- -- from (νfix G) x = ⊎collapse (νfix-from G x)
-- -- -- 
-- -- -- ν?′ : DecGram n G → (∀ i → Dec (lookup Γν i)) → Dec ν⟦ Γν ⊢ G ⟧
-- -- -- ν?′ ∅ Γ = no (λ z → z)
-- -- -- ν?′ ε Γ = yes tt
-- -- -- ν?′ (‵ c) Γ = no (λ z → z)
-- -- -- ν?′ (x · G) Γ = x ×? ν?′ G Γ
-- -- -- ν?′ (G₁ ∪ G₂) Γ = ν?′ G₁ Γ ⊎? ν?′ G₂ Γ
-- -- -- ν?′ (G₁ ∙ G₂) Γ = ν?′ G₁ Γ ×? ν?′ G₂ Γ
-- -- -- ν?′ (var i) Γ = Γ i
-- -- -- ν?′ (μ {G = G′} G) Γ = mapDec (νfix G′) (ν?′ G (λ { zero → no λ () ; (suc i) → Γ i })) 
-- -- -- 
-- -- -- ↔lookup : (f : A → Set) (xs : Vec A n) (i : Fin n) → lookup (mapVec f xs) i ↔ f (lookup xs i)
-- -- -- ↔lookup f (x ∷ xs) zero = ↔refl
-- -- -- ↔lookup f (x ∷ xs) (suc i) = ↔lookup f xs i
-- -- -- 
-- -- -- ν?₀ : DecGram zero G → Dec (ν ⟦ G ⟧)
-- -- -- 
-- -- -- ν? : DecGram n G → (∀ i → Dec (ν (lookup Γ i))) → Dec (ν ⟦ Γ ⊢ G ⟧)
-- -- -- ν? {G = G} {Γ = Γ′} D Γ = mapDec (νG-correct {Γν = mapVec ν Γ′} G (↔lookup ν Γ′)) (ν?′ D (λ i → mapDec (↔sym (↔lookup ν Γ′ i)) (Γ i)))
-- -- -- 
-- -- -- ν?₀ G = ν? G λ ()
-- -- -- 
-- -- -- -- derivative
-- -- -- 
-- -- -- δ⟦_⟧₀ : Gram zero → Tok → Gram zero
-- -- -- 
-- -- -- δ⟦_,_,_⊢_⟧ : Vec Set n → Vec (Gram m) n → Vec (Gram m) n → Gram n → Tok → Gram m
-- -- -- δ⟦ Γν , Γδ , σ ⊢ ∅ ⟧ _ = ∅
-- -- -- δ⟦ Γν , Γδ , σ ⊢ ε ⟧ _ = ∅
-- -- -- δ⟦ Γν , Γδ , σ ⊢ ‵ c′ ⟧ c with c′ ≟ c
-- -- -- ... | yes _ = ε
-- -- -- ... | no _ = ∅
-- -- -- δ⟦ Γν , Γδ , σ ⊢ A · G ⟧ c = A · δ⟦ Γν , Γδ , σ ⊢ G ⟧ c
-- -- -- δ⟦ Γν , Γδ , σ ⊢ G₁ ∪ G₂ ⟧ c = δ⟦ Γν , Γδ , σ ⊢ G₁ ⟧ c ∪ δ⟦ Γν , Γδ , σ ⊢ G₂ ⟧ c
-- -- -- δ⟦ Γν , Γδ , σ ⊢ G₁ ∙ G₂ ⟧ c = δ⟦ Γν , Γδ , σ ⊢ G₁ ⟧ c ∙ substG G₂ (lookup σ) ∪ (ν⟦ Γν ⊢ G₁ ⟧ · δ⟦ Γν , Γδ , σ ⊢ G₂ ⟧ c)
-- -- -- δ⟦ Γν , Γδ , σ ⊢ var i ⟧ c = lookup Γδ i
-- -- -- δ⟦ Γν , Γδ , σ ⊢ ▹ G ⟧ c = ▹ (λ { .! → δ⟦ Γν , Γδ , σ ⊢ ! G ⟧ c })
-- -- -- 
-- -- -- δ⟦ G ⟧₀ = δ⟦ [] , [] , [] ⊢ G ⟧
-- -- -- 
-- -- -- variable Γδ : Vec (Gram m) n
-- -- -- 
-- -- -- Γδ-correct : Vec Lang n → Vec Lang m → Tok → Vec (Gram m) n → Set
-- -- -- Γδ-correct Γ Γ′ c Γδ = ∀ {w} i → ⟦ Γ′ ⊢ lookup Γδ i ⟧ w ↔ δ c (lookup Γ i) w
-- -- -- 
-- -- -- data AllVec {A : Set ℓ} (P : A → Set) : {n : ℕ} (xs : Vec A n) → Set ℓ where
-- -- --   [] : AllVec P []
-- -- --   _∷_ : ∀{x} {xs : Vec A n} → P x → AllVec P xs → AllVec P (x ∷ xs)
-- -- -- 
-- -- -- tabulate : ((i : Fin n) → A) → Vec A n
-- -- -- tabulate {zero} f = []
-- -- -- tabulate {suc n} f = f zero ∷ tabulate {n} (f ∘ suc)
-- -- -- 
-- -- -- σ-correct : Vec Lang n → Vec Lang m → Vec (Gram m) n → Set
-- -- -- σ-correct Γ Γ′ σ = ∀ {w} i → ⟦ Γ′ ⊢ lookup σ i ⟧ w ↔ lookup Γ i w
-- -- -- 
-- -- -- the-σ : (Γ : Vec (Gram m) n) (Γ′ : Vec Lang m) → Vec (Gram m) n
-- -- -- the-σ Γ _ = Γ
-- -- -- 
-- -- -- the-σ-correct : (Γ : Vec (Gram m) n) (Γ′ : Vec Lang m) → σ-correct (mapVec (λ G → ⟦ Γ′ ⊢ G ⟧) Γ) Γ′ (the-σ Γ Γ′)
-- -- -- the-σ-correct (ℒ ∷ Γ) Γ′ zero = ↔refl
-- -- -- the-σ-correct (ℒ ∷ Γ) Γ′ (suc i) = the-σ-correct Γ Γ′ i
-- -- -- 
-- -- -- σ-corollary : (σ : Vec (Gram m) n) → σ-correct Γ Γ′ σ → (G : Gram n) → ⟦ Γ′ ⊢ substG G (lookup σ) ⟧ w ↔ ⟦ Γ ⊢ G ⟧ w
-- -- -- σ-corollary σ σc ε .to x = x
-- -- -- σ-corollary σ σc (‵ c) .to x = x
-- -- -- σ-corollary σ σc (A · G) .to (x , y) = x , σ-corollary σ σc  G .to y
-- -- -- σ-corollary σ σc (G ∪ G₁) .to (inl x) = inl (σ-corollary σ σc G .to x)
-- -- -- σ-corollary σ σc (G ∪ G₁) .to (inr x) = inr (σ-corollary σ σc G₁ .to x)
-- -- -- σ-corollary σ σc (G ∙ G₁) .to (u , v , refl , x , y) = u , v , refl , σ-corollary σ σc G .to x , σ-corollary σ σc G₁ .to y
-- -- -- σ-corollary σ σc (var i) .to x = σc i .to x
-- -- -- σ-corollary σ σc (▹ ∞G) .to (▹ x) = ▹ (σ-corollary σ σc (∞G .!) .to x)
-- -- -- σ-corollary σ σc ε .from x = x
-- -- -- σ-corollary σ σc (‵ c) .from x = x
-- -- -- σ-corollary σ σc (A · G) .from (x , y) = x , σ-corollary σ σc  G .from y
-- -- -- σ-corollary σ σc (G ∪ G₁) .from (inl x) = inl (σ-corollary σ σc G .from x)
-- -- -- σ-corollary σ σc (G ∪ G₁) .from (inr x) = inr (σ-corollary σ σc G₁ .from x)
-- -- -- σ-corollary σ σc (G ∙ G₁) .from (u , v , refl , x , y) = u , v , refl , σ-corollary σ σc G .from x , σ-corollary σ σc G₁ .from y
-- -- -- σ-corollary σ σc (var i) .from x = σc i .from x
-- -- -- σ-corollary σ σc (▹ ∞G) .from (▹ x) = ▹ (σ-corollary σ σc (∞G .!) .from x)
-- -- -- 
-- -- -- δG-sound : Γν-correct Γ Γν → Γδ-correct Γ Γ′ c Γδ → σ-correct Γ Γ′ σ → (G : Gram n) → ⟦ Γ′ ⊢ δ⟦ Γν , Γδ , σ ⊢ G ⟧ c ⟧ w → δ c ⟦ Γ ⊢ G ⟧ w
-- -- -- δG-sound {c = c} Γν Γδ σ (‵ c′) x with c′ ≟ c
-- -- -- δG-sound {c = c} Γν Γδ σ (‵ c) refl | yes refl = refl
-- -- -- δG-sound {c = c} Γν Γδ σ (‵ c′) () | no _
-- -- -- δG-sound Γν Γδ σ (A · G) (pl , pr) = pl , δG-sound Γν Γδ σ G pr
-- -- -- δG-sound Γν Γδ σ (G ∪ G₁) (inl x) = inl (δG-sound Γν Γδ σ G x)
-- -- -- δG-sound Γν Γδ σ (G ∪ G₁) (inr x) = inr (δG-sound Γν Γδ σ G₁ x)
-- -- -- δG-sound {σ = σ′} Γν Γδ σ (G ∙ G₁) (inl (u , v , refl , x , y)) = (_ ∷ u) , v , refl , δG-sound Γν Γδ σ G x , σ-corollary σ′ σ G₁ .to y
-- -- -- δG-sound Γν Γδ σ (G ∙ G₁) (inr (x , y)) = [] , (_ ∷ _) , refl , νG-sound G Γν x , δG-sound Γν Γδ σ G₁ y
-- -- -- δG-sound Γν Γδ σ (var i) x = to (Γδ i) x
-- -- -- δG-sound Γν Γδ σ (▹ G) (▹ x) = ▹ (δG-sound Γν Γδ σ (G .!) x)
-- -- -- 
-- -- -- δG-complete : Γν-correct Γ Γν → Γδ-correct Γ Γ′ c Γδ → σ-correct Γ Γ′ σ → (G : Gram n) → δ c ⟦ Γ ⊢ G ⟧ w → ⟦ Γ′ ⊢ (δ⟦ Γν , Γδ , σ ⊢ G ⟧ c) ⟧ w 
-- -- -- δG-complete {c = c} Γν Γδ σ (‵ c′) x with c′ ≟ c
-- -- -- δG-complete {c = c} Γν Γδ σ (‵ c) refl | yes refl = refl
-- -- -- δG-complete {c = .c′} Γν Γδ σ (‵ c′) refl | no ¬x = ¬x refl
-- -- -- δG-complete Γν Γδ σ (A · G) (pl , pr) = pl , δG-complete Γν Γδ σ G pr
-- -- -- δG-complete Γν Γδ σ (G ∪ G₁) (inl x) = inl (δG-complete Γν Γδ σ G x)
-- -- -- δG-complete Γν Γδ σ (G ∪ G₁) (inr x) = inr (δG-complete Γν Γδ σ G₁ x)
-- -- -- δG-complete {σ = σ′} Γν Γδ σ (G ∙ G₁) ((c ∷ u) , v , refl , x , y) = inl (u , v , refl , δG-complete Γν Γδ σ G x , σ-corollary σ′ σ G₁ .from y)
-- -- -- δG-complete Γν Γδ σ (G ∙ G₁) ([] , (c ∷ v) , refl , x , y) = inr (νG-complete G Γν x , δG-complete Γν Γδ σ G₁ y)
-- -- -- δG-complete Γν Γδ σ (var i) x = from (Γδ i) x
-- -- -- δG-complete Γν Γδ σ (▹ G) (▹ x) = ▹ (δG-complete Γν Γδ σ (! G) x)
-- -- -- 
-- -- -- δG-correct : Γν-correct Γ Γν → Γδ-correct Γ Γ′ c Γδ → σ-correct Γ Γ′ σ → (G : Gram n) → ⟦ Γ′ ⊢ (δ⟦ Γν , Γδ , σ ⊢ G ⟧ c) ⟧ w ↔ δ c ⟦ Γ ⊢ G ⟧ w
-- -- -- to (δG-correct Γν Γδ σ G) = δG-sound Γν Γδ σ G
-- -- -- from (δG-correct Γν Γδ σ G) = δG-complete Γν Γδ σ G
-- -- -- 
-- -- -- ↔lookupG : ∀{n m Γ} (f : A → Gram m) (xs : Vec A n) (i : Fin n) → ⟦ Γ ⊢ lookup (mapVec f xs) i ⟧ w ↔ ⟦ Γ ⊢ f (lookup xs i) ⟧ w
-- -- -- ↔lookupG f (x ∷ xs) zero = ↔refl
-- -- -- ↔lookupG f (x ∷ xs) (suc i) = ↔lookupG f xs i
-- -- -- 
-- -- -- substG₀ν : ∀ {ν₁} (G : Gram _) → (ν₁ → ν⟦ Γν ⊢ G′ ⟧) → ν⟦ ν₁ ∷ Γν ⊢ G ⟧ → ν⟦ Γν ⊢ substG₀ G G′ ⟧
-- -- -- substG₀ν ε f x = x
-- -- -- substG₀ν (A · G) f (pl₁ , pr₁) = pl₁ , substG₀ν G f pr₁
-- -- -- substG₀ν (G ∪ G₁) f (inl x) = inl (substG₀ν G f x)
-- -- -- substG₀ν (G ∪ G₁) f (inr x) = inr (substG₀ν G₁ f x)
-- -- -- substG₀ν (G ∙ G₁) f (pl₁ , pr₁) = substG₀ν G f pl₁ , substG₀ν G₁ f pr₁
-- -- -- substG₀ν (var zero) f x = f x
-- -- -- substG₀ν (var (suc i)) f x = x
-- -- -- substG₀ν (▹ ∞G) f (▹ x) = ▹ (substG₀ν (∞G .!) f x)
-- -- -- 
-- -- -- 
-- -- -- -- δfix : (σ : Vec (Gram m) n) → {w : List Tok} (G : Gram (suc n))
-- -- -- --   → {Γ′ : Vec Lang m} → let Γ = mapVec ⟦ Γ′ ⊢_⟧ σ ; Γν = the-Γν σ Γ′
-- -- -- --   in {Γ₀ : Vec Lang m}
-- -- -- --   → ⟦ Γ₀ ⊢ fixG (δ⟦ ν⟦ Γν ⊢ fixG G ⟧ ∷ Γν , var zero ∷ mapVec (renameG suc) Γδ , renameG suc (substG (fixG G) (lookup σ)) ∷ mapVec (renameG suc) σ ⊢ G ⟧ c) ⟧ w
-- -- -- --   ↔ ⟦ Γ₀ ⊢ δ⟦ Γν , Γδ , σ ⊢ fixG G ⟧ c ⟧ w
-- -- -- -- 
-- -- -- -- δfix-to : (σ : Vec (Gram m) n) → (_ : ⊤) (_ : ⊤) (G : Gram (suc n)) {G₀ : Gram (suc n)}
-- -- -- --   → {Γ′ : Vec Lang m} → let Γ = mapVec (λ G → ⟦ Γ′ ⊢ G ⟧) σ ; Γν = the-Γν σ Γ′ in
-- -- -- --   {Γ₀ : Vec Lang m} →
-- -- -- --   ⟦ Γ₀ ⊢ fixG′
-- -- -- --     (δ⟦ ν⟦ Γν ⊢ fixG G₀ ⟧ ∷ Γν
-- -- -- --       , var zero ∷ mapVec (renameG suc) Γδ
-- -- -- --       , mapVec (renameG suc) (substG (fixG G₀) (lookup σ) ∷ σ)
-- -- -- --       ⊢ G₀ ⟧ c)
-- -- -- --     (δ⟦ ν⟦ Γν ⊢ fixG G₀ ⟧ ∷ Γν
-- -- -- --       , var zero ∷ mapVec (renameG suc) Γδ
-- -- -- --       , mapVec (renameG suc) (substG (fixG G₀) (lookup σ) ∷ σ)
-- -- -- --       ⊢ G ⟧ c)
-- -- -- --     ⟧ w
-- -- -- --   → ⟦ Γ₀ ⊢ δ⟦ Γν , Γδ , σ ⊢ fixG′ G₀ G ⟧ c ⟧ w
-- -- -- -- δfix-to {c = c′} Γ Γν σ (‵ c) x with c ≟ c′
-- -- -- -- ... | yes _ = x
-- -- -- -- ... | no _ = x
-- -- -- -- δfix-to Γ Γν σ (A · G) (x , y) = x , δfix-to Γ Γν σ G y
-- -- -- -- δfix-to Γ Γν σ (G ∪ G₁) (inl x) = inl (δfix-to Γ Γν σ G x)
-- -- -- -- δfix-to Γ Γν σ (G ∪ G₁) (inr x) = inr (δfix-to Γ Γν σ G₁ x)
-- -- -- -- δfix-to σ′ Γν σ (G ∙ G₁) {G₀} {Γ₀ = Γ₀} (inl (u , v , refl , x , y)) = inl (u , v , refl , δfix-to σ′ Γν σ G x ,
-- -- -- --   ⊢subst {Γ′ = mapVec ⟦ Γ₀ ⊢_⟧ σ′} {Γ = Γ₀} (lookup σ′) (λ i → ↔sym (the-σ-correct σ′ Γ₀ i)) (fixG′ G₀ G₁) .to
-- -- -- --   let y = unroll′ (substG G₁ (lookup (mapVec (renameG suc) (substG (fixG G₀) (lookup σ′) ∷ σ′)))) y
-- -- -- --       y = (⊢subst (lookup
-- -- -- --           (renameG suc (substG (fixG G₀) (lookup σ′)) ∷
-- -- -- --            mapVec (renameG suc) σ′))
-- -- -- --              (λ where
-- -- -- --                zero → ↔trans (⊢subst (lookup σ′) (λ G → ↔sym (the-σ-correct σ′ Γ₀ G)) (fixG G₀)) (↔sym (renamesuc (substG (fixG G₀) (lookup σ′))))
-- -- -- --                (suc i) → subst (λ X → lookup ((mapVec ⟦ Γ₀ ⊢_⟧) σ′) i _ ↔ ⟦ _ ∷ Γ₀ ⊢ X ⟧ _)
-- -- -- --                           (sym (lookup-map (renameG suc) σ′ i))
-- -- -- --                           (↔sym (↔trans (renamesuc (lookup σ′ i))
-- -- -- --                                 (the-σ-correct σ′ Γ₀ i))))
-- -- -- --              G₁ .from y)
-- -- -- --    in roll′ G₁ y 
-- -- -- --   )
-- -- -- -- δfix-to Γ Γν σ (G ∙ G₁) {G₀} {Γ₀} (inr (x , y)) = inr (
-- -- -- --   (let x = νG-sound G (λ { zero → νG-correct {Γ = mapVec (λ G → ⟦ Γ₀ ⊢ G ⟧) Γ} (fixG G₀) (the-Γν-correct Γ) ; (suc i) → the-Γν-correct Γ i }) x
-- -- -- --        x = roll′ G x  
-- -- -- --    in νG-complete (fixG′ G₀ G) (the-Γν-correct Γ) x)
-- -- -- --   , δfix-to Γ Γν σ G₁ y)
-- -- -- -- δfix-to Γ Γν σ (var zero) {G₀} (▹ x) = ▹ (δfix-to Γ Γν σ G₀ x)
-- -- -- -- δfix-to {Γδ = Γδ} Γ Γν σ (var (suc i)) x = fixGsuc-to (lookup Γδ i) (subst (λ X → ⟦ _ ⊢ fixG′ _ X ⟧ _) (lookup-map (renameG suc) Γδ i) x)
-- -- -- -- δfix-to Γ Γν σ (▹ ∞G) (▹ x) = ▹ (δfix-to Γ Γν σ (∞G .!) x)
-- -- -- -- 
-- -- -- -- δfix-from : (Γ : Vec Lang n) {Γ′ : Vec Lang m} (Γνc : Γν-correct Γ Γν) (σc : σ-correct Γ Γ′ σ) (G : Gram (suc n)) {G₀ : Gram (suc n)}
-- -- -- --   → ⟦ Γ′ ⊢ δ⟦ Γν , Γδ , σ ⊢ fixG′ G₀ G ⟧ c ⟧ w
-- -- -- --   → ⟦ Γ′ ⊢ fixG′
-- -- -- --       (δ⟦ ν⟦ Γν ⊢ fixG G₀ ⟧ ∷ Γν
-- -- -- --         , var zero ∷ mapVec (renameG suc) Γδ
-- -- -- --         , mapVec (renameG suc) (substG (fixG G₀) (lookup σ) ∷ σ)
-- -- -- --         ⊢ G₀ ⟧ c)
-- -- -- --       (δ⟦ ν⟦ Γν ⊢ fixG G₀ ⟧ ∷ Γν
-- -- -- --         , var zero ∷ mapVec (renameG suc) Γδ
-- -- -- --         , mapVec (renameG suc) (substG (fixG G₀) (lookup σ) ∷ σ)
-- -- -- --         ⊢ G ⟧ c)
-- -- -- --     ⟧ w
-- -- -- -- δfix-from {c = c′} Γ Γν σ (‵ c) x with c ≟ c′
-- -- -- -- ... | yes _ = x
-- -- -- -- ... | no _ = x
-- -- -- -- δfix-from Γ Γν σ (A · G) (x , y) = x , δfix-from Γ Γν σ G y
-- -- -- -- δfix-from Γ Γν σ (G ∪ G₁) (inl x) = inl (δfix-from Γ Γν σ G x)
-- -- -- -- δfix-from Γ Γν σ (G ∪ G₁) (inr x) = inr (δfix-from Γ Γν σ G₁ x)
-- -- -- -- δfix-from {σ = σ′} Γ {Γ′} Γν σ (G ∙ G₁) {G₀} (inl (u , v , refl , x , y)) = inl (u , v , refl , δfix-from Γ Γν σ G x ,
-- -- -- --   roll′
-- -- -- --    (substG G₁
-- -- -- --     (lookup
-- -- -- --      (mapVec (renameG suc) (substG (fixG G₀) (lookup σ′) ∷ σ′))))
-- -- -- --    (⊢subst
-- -- -- --      (lookup (mapVec (renameG suc) (substG (fixG G₀) (lookup σ′) ∷ σ′)))
-- -- -- --        (λ where
-- -- -- --          zero → ↔sym (↔trans (renamesuc (substG (fixG G₀) (lookup σ′)))
-- -- -- --            (σ-corollary {Γ = Γ} σ′ σ (fixG G₀)))
-- -- -- --          (suc i) → subst (λ X → lookup Γ i _ ↔ ⟦ _ ∷ _ ⊢ X ⟧ _) (sym (lookup-map (renameG suc) σ′ i))
-- -- -- --            (↔sym (↔trans (renamesuc (lookup σ′ i)) (σ i))))
-- -- -- --        G₁ .to (unroll′ G₁ (⊢subst (lookup σ′) (λ i → ↔sym (σ i)) (fixG′ G₀ G₁) .from y))))
-- -- -- -- δfix-from {n = n} Γ Γν σ (G ∙ G₁) {G₀} (inr (x , y)) = inr (νG-complete G (λ { zero → νG-correct (fixG G₀) Γν ; (suc i) → Γν i }) (unroll′ {Γ = Γ} G {G₀} (νG-sound {n = n} (fixG′ G₀ G) Γν x)) , δfix-from Γ Γν σ G₁ y)
-- -- -- -- δfix-from Γ Γν σ (var zero) {G₀} (▹ x) = ▹ (δfix-from Γ Γν σ G₀ x)
-- -- -- -- δfix-from {Γδ = Γδ} Γ Γν σ (var (suc i)) x = subst (λ X → ⟦ _ ⊢ fixG′ _ X ⟧ _) (sym (lookup-map (renameG suc) Γδ i)) (fixGsuc-from (lookup Γδ i) x)
-- -- -- -- δfix-from Γ Γν σ (▹ ∞G) (▹ x) = ▹ (δfix-from Γ Γν σ (∞G .!) x)
-- -- -- -- 
-- -- -- -- δfix Γ G {Γ′ = Γ′} {Γ₀ = Γ₀} .to x = δfix-to Γ tt tt G {Γ₀ = Γ₀} x
-- -- -- -- -- δfix Γ {Γ′} G .from x = δfix-from (mapVec (λ G → ⟦ Γ′ ⊢ G ⟧) Γ) (the-Γν-correct Γ) (the-σ-correct Γ Γ′) G x
-- -- -- 
-- -- -- δfix : ∀ (σ : Vec (Gram m) n)
-- -- --           (Γδ : Vec (Gram m) n)
-- -- --           (Γ′ : Vec Lang m)
-- -- --           (G : Gram (suc n))
-- -- --           (Γ₀ : Vec Lang m) →
-- -- --        ⟦ Γ₀ ⊢
-- -- --        fixG
-- -- --        (δ⟦
-- -- --         the-Γν (mapVec (renameG suc) (substG (fixG G) (lookup σ) ∷ σ))
-- -- --         (δ c ⟦ mapVec ⟦ Γ′ ⊢_⟧ σ ⊢ fixG G ⟧ ∷ Γ′)
-- -- --         , var zero ∷ mapVec (renameG suc) Γδ ,
-- -- --         mapVec (renameG suc) (substG (fixG G) (lookup σ) ∷ σ) ⊢ G ⟧
-- -- --         c)
-- -- --        ⟧
-- -- --        w
-- -- --        ↔ ⟦ Γ₀ ⊢ δ⟦ the-Γν σ Γ′ , Γδ , σ ⊢ fixG G ⟧ c ⟧ w
-- -- -- 
-- -- -- δfix-to : (σ : Vec (Gram m) n)
-- -- --           (Γδ : Vec (Gram m) n)
-- -- --           (Γ′ : Vec Lang m)
-- -- --           (G : Gram (suc n))
-- -- --           (G₀ : Gram (suc n))
-- -- --           (Γ₀ : Vec Lang m) →
-- -- --           ⟦ Γ₀ ⊢
-- -- --           fixG′
-- -- --           (δ⟦
-- -- --            the-Γν (mapVec (renameG suc) (substG (fixG G₀) (lookup σ) ∷ σ))
-- -- --            (δ c ⟦ mapVec (⟦_⊢_⟧ Γ′) σ ⊢ fixG G₀ ⟧ ∷ Γ′)
-- -- --            , var zero ∷ mapVec (renameG suc) Γδ ,
-- -- --            mapVec (renameG suc) (substG (fixG G₀) (lookup σ) ∷ σ) ⊢ G₀ ⟧
-- -- --            c)
-- -- --           (δ⟦
-- -- --            the-Γν (mapVec (renameG suc) (substG (fixG G₀) (lookup σ) ∷ σ))
-- -- --            (δ c ⟦ mapVec (⟦_⊢_⟧ Γ′) σ ⊢ fixG G₀ ⟧ ∷ Γ′)
-- -- --            , var zero ∷ mapVec (renameG suc) Γδ ,
-- -- --            mapVec (renameG suc) (substG (fixG G₀) (lookup σ) ∷ σ) ⊢ G ⟧
-- -- --            c)
-- -- --           ⟧
-- -- --           w →
-- -- --           ⟦ Γ₀ ⊢ δ⟦ the-Γν σ Γ′ , Γδ , σ ⊢ fixG′ G₀ G ⟧ c ⟧ w
-- -- -- δfix-to {c = c′} σ Γδ Γ′ (‵ c) G₀ Γ₀ x with c ≟ c′
-- -- -- ... | yes _ = x
-- -- -- ... | no _ = x
-- -- -- δfix-to σ Γδ Γ′ (A · G) G₀ Γ₀ (x , y) = x , δfix-to σ Γδ Γ′ G G₀ Γ₀ y
-- -- -- δfix-to σ Γδ Γ′ (G ∪ G₁) G₀ Γ₀ (inl x) = inl (δfix-to σ Γδ Γ′ G G₀ Γ₀ x)
-- -- -- δfix-to σ Γδ Γ′ (G ∪ G₁) G₀ Γ₀ (inr x) = inr (δfix-to σ Γδ Γ′ G₁ G₀ Γ₀ x)
-- -- -- δfix-to σ Γδ Γ′ (G ∙ G₁) G₀ Γ₀ (inl (u , v , refl , x , y)) = inl (u , v , refl , δfix-to σ Γδ Γ′ G G₀ Γ₀ x ,
-- -- --   ⊢subst {Γ′ = mapVec ⟦ Γ₀ ⊢_⟧ σ} (lookup σ) (λ i → ↔sym (the-σ-correct σ Γ₀ i)) (fixG′ G₀ G₁) .to
-- -- --     let y = (unroll′ (substG G₁ (lookup (renameG suc (substG (fixG G₀) (lookup σ)) ∷ mapVec (renameG suc) σ))) y )
-- -- --         y = (⊢subst (lookup (renameG suc (substG (fixG G₀) (lookup σ)) ∷ mapVec (renameG suc) σ))
-- -- --             (λ { zero → ↔sym (↔trans (renamesuc (substG (fixG G₀) (lookup σ))) (↔sym (⊢subst (lookup σ) (λ i → subst (λ X → X _ ↔ ⟦ Γ₀ ⊢ lookup σ i ⟧ _) (sym (lookup-map ⟦ Γ₀ ⊢_⟧ σ i)) ↔refl) (fixG G₀))))
-- -- --                ; (suc i) → subst (λ X → lookup (mapVec ⟦ Γ₀ ⊢_⟧ σ) i _ ↔ ⟦ _ ∷ Γ₀ ⊢ X ⟧ _) (sym (lookup-map (renameG suc) σ i)) (↔trans (subst (λ X → X _ ↔ ⟦ Γ₀ ⊢ lookup σ i ⟧ _) (sym (lookup-map ⟦ Γ₀ ⊢_⟧ σ i)) ↔refl) (↔sym (renamesuc (lookup σ i))))
-- -- --                })
-- -- --             G₁ .from y)
-- -- --     in roll′ G₁ y 
-- -- --   )
-- -- -- δfix-to σ Γδ Γ′ (G ∙ G₁) G₀ Γ₀ (inr (x , y)) = inr (
-- -- --   {!x!}
-- -- --   , δfix-to σ Γδ Γ′ G₁ G₀ Γ₀ y)
-- -- -- δfix-to σ Γδ Γ′ (var zero) G₀ Γ₀ (▹ x) = ▹ (δfix-to σ Γδ Γ′ G₀ G₀ Γ₀ x)
-- -- -- δfix-to σ Γδ Γ′ (var (suc i)) G₀ Γ₀ x =
-- -- --   {!!}
-- -- -- δfix-to σ Γδ Γ′ (▹ ∞G) G₀ Γ₀ (▹ x) = ▹ (δfix-to σ Γδ Γ′ (∞G .!) G₀ Γ₀ x)
-- -- -- 
-- -- -- to (δfix σ Γδ Γ′ G Γ₀) = δfix-to σ Γδ Γ′ G G Γ₀
-- -- -- from (δfix σ Γδ Γ′ G Γ₀) = {!!}
-- -- -- 
-- -- -- δ?₀ : DecGram zero G → (c : Tok) → DecGram zero (δ⟦ G ⟧₀ c)
-- -- -- 
-- -- -- δ? : (σ : Vec (Gram m) n) → let Γν = the-Γν σ Γ′ in (∀ i → Dec (lookup Γν i)) → (∀ i → DecGram m (lookup Γδ i)) → (∀ i → DecGram m (lookup σ i)) → DecGram n G → (c : Tok) → DecGram m (δ⟦ Γν , Γδ , σ ⊢ G ⟧ c)
-- -- -- δ? σ Γν? Γδ? σ? ∅ c = ∅
-- -- -- δ? σ Γν? Γδ? σ? ε c = ∅
-- -- -- δ? σ Γν? Γδ? σ? (‵ c′) c with c′ ≟ c
-- -- -- ... | yes _ = ε
-- -- -- ... | no _ = ∅
-- -- -- δ? σ Γν? Γδ? σ? (x · G) c = x · δ? σ Γν? Γδ? σ? G c
-- -- -- δ? σ Γν? Γδ? σ? (G₁ ∪ G₂) c = δ? σ Γν? Γδ? σ? G₁ c ∪ δ? σ Γν? Γδ? σ? G₂ c
-- -- -- δ? {G = G′} σ Γν? Γδ? σ? (G₁ ∙ G₂) c = δ? σ Γν? Γδ? σ? G₁ c ∙ substD σ G₂ σ? ∪ (ν?′ G₁ Γν? · δ? σ Γν? Γδ? σ? G₂ c)
-- -- -- δ? σ Γν? Γδ? σ? (var i) c = Γδ? i
-- -- -- δ? {m = m} {Γ′ = Γ′} {Γδ = Γδ′} {G = G′} σ Γν? Γδ? σ? (μ {G = G″} G) c =
-- -- --   (λ {Γ₀} → δfix σ Γδ′ Γ′ G″ Γ₀) ◃ μ (
-- -- --     δ? {Γ′ = δ c ⟦ mapVec ⟦ Γ′ ⊢_⟧ σ ⊢ G′ ⟧ ∷ Γ′}
-- -- --        {Γδ = var zero ∷ mapVec (renameG suc) Γδ′}
-- -- --        (mapVec (renameG suc) (substG G′ (lookup σ) ∷ σ))
-- -- --        (λ { zero → mapDec (↔trans (⊢subst {Γ′ = mapVec ⟦ Γ′ ⊢_⟧ σ} (lookup σ) (λ i → ↔sym (the-σ-correct σ Γ′ i)) (fixG G″)) (↔sym (renamesuc (substG (fixG G″) (lookup σ))))) (ν? (μ G) λ i → mapDec (the-Γν-correct σ i) (Γν? i)) ; (suc i) → mapDec (subst (λ X → lookup (the-Γν σ Γ′) i ↔ X) (sym (lookup-map _ (mapVec (renameG suc) σ) i)) (subst (λ X → lookup (the-Γν σ Γ′) i ↔ ⟦ _ ∷ Γ′ ⊢ X ⟧ []) (sym (lookup-map _ σ i)) (↔sym (↔trans (renamesuc (lookup σ i)) (↔trans (the-σ-correct σ Γ′ i) (↔sym (the-Γν-correct {Γ′ = Γ′} σ i))))))) (Γν? i) })
-- -- --        (λ { zero → var zero ; (suc i) → subst (DecGram (suc m)) (sym (lookup-map _ Γδ′ i)) (renameD suc (Γδ? i)) })
-- -- --        (λ { zero → renameD suc (substD σ (μ G) σ?) ; (suc i) → subst (DecGram (suc m)) (sym (lookup-map _ σ i)) (renameD suc (σ? i)) })
-- -- --        G
-- -- --        c)
-- -- -- 
-- -- -- δ?₀ G c = δ? {Γ′ = []} [] (λ ()) (λ ()) (λ ()) G c
-- -- -- 
-- -- -- parse : DecGram zero G → (w : List Tok) → Dec (⟦ G ⟧ w)
-- -- -- parse G [] = ν?₀ G
-- -- -- parse {G = G′} G (c ∷ w) = mapDec (δG-correct (λ ()) (λ ()) (λ ()) G′) (parse (δ?₀ G c) w)
-- -- -- 
-- -- -- 
-- -- 
-- 
