{-# OPTIONS --guardedness #-}
{-# OPTIONS --allow-unsolved-metas  #-}

module Gram where

open import Agda.Primitive using (Level ; _⊔_)
open import Prelude
open import Lang
open T using (Tok ; _≟_)
open _↔_

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

_⇔_ : (_ _ : Gram n) → Set₁
G₁ ⇔ G₂ = ∀{Γ w} → ⟦ Γ ⊢ G₁ ⟧ w ↔ ⟦ Γ ⊢ G₂ ⟧ w

tsbus : (Γ : Vec Lang m) → (Fin n → Gram m) → Vec Lang n
tsbus {n = zero} Γ f = []
tsbus {n = suc n} Γ f = ⟦ Γ ⊢ f zero ⟧ ∷ tsbus Γ (f ∘ suc)

x+x+x : ⟦ Γ ⊢ expr ⟧ (let open T in x ∷ + ∷ x ∷ + ∷ x ∷ [])
x+x+x = inr (_ , _ , refl , □ (inl refl) , _ , _ , refl , refl , □ (inr (_ , _ , refl , □ (inl refl) , _ , _ , refl , refl , □ (inl refl))))

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

-- -- our variables are only ever used in this way, so let's enshrine that:
-- data Grams : ℕ → Set₁ where
--   [] : Grams zero
--   _∷_ : (G : Gram (suc n)) → (Gs : Grams n) → Grams (suc n)
-- 
-- ⟦_⟧s : Grams n → Vec Lang n
-- ⟦ [] ⟧s = []
-- ⟦ G ∷ Gs ⟧s = ⟦ ⟦ Gs ⟧s ⊢ fixG G ⟧ ∷ ⟦ Gs ⟧s
-- 
-- variable Gs Gs′ : Grams n
-- 
-- fin→nat : Fin n → ℕ
-- fin→nat zero = zero
-- fin→nat (suc i) = suc (fin→nat i)
-- 
-- _+_ : Fin n → ℕ → ℕ
-- zero + x = x
-- suc x + y = suc (x + y)
-- 
-- -- always subtracts at least one
-- _-_ : (n : ℕ) → Fin n → ℕ
-- (suc n) - zero = n
-- (suc n) - suc i = n - i
-- 
-- -- m = n - i
-- lookupGrams : (i : Fin n) → (Gs : Grams n) → Gram (suc (n - i)) × Grams (n - i)
-- lookupGrams zero (G ∷ Gs) = G , Gs
-- lookupGrams (suc i) (G ∷ Gs) = lookupGrams i Gs
-- 
-- lookupGrams′ : (i : Fin n) → (Gs : Grams n) → Gram n
-- lookupGrams′ zero (G ∷ Gs) = renameG suc (fixG G)
-- lookupGrams′ (suc i) (G ∷ Gs) = renameG suc (lookupGrams′ i Gs)
-- 
-- variable i : Fin n
-- 
-- lookup⟦⟧s : ∀ {Gs : Grams n} (i : Fin n) {G′ : Gram (suc (n - i))} {Gs′ : Grams (n - i)} → lookupGrams i Gs ≡ G′ , Gs′ → lookup ⟦ Gs ⟧s i ≡ ⟦ ⟦ Gs′ ⟧s ⊢ fixG G′ ⟧
-- lookup⟦⟧s {Gs = _ ∷ _} (zero)  refl = refl
-- lookup⟦⟧s {Gs = _ ∷ _} (suc i) = lookup⟦⟧s i
-- 
-- ν⟦_⊢_⟧ : (Gs : Grams n) → Gram n → Set
-- 
-- data ν□G (□G : □Gram n) (Gs : Grams n) : Set where
--   □ : ν⟦ Gs ⊢ ! □G ⟧ → ν□G □G Gs
-- 
-- ν⟦ Gs ⊢ ∅ ⟧ = ⊥
-- ν⟦ Gs ⊢ ε ⟧ = ⊤
-- ν⟦ Gs ⊢ ‵ c ⟧ = ⊥
-- ν⟦ Gs ⊢ A · G ⟧ = A × ν⟦ Gs ⊢ G ⟧
-- ν⟦ Gs ⊢ G₁ ∪ G₂ ⟧ = ν⟦ Gs ⊢ G₁ ⟧ ⊎ ν⟦ Gs ⊢ G₂ ⟧
-- ν⟦ Gs ⊢ G₁ ∙ G₂ ⟧ = ν⟦ Gs ⊢ G₁ ⟧ × ν⟦ Gs ⊢ G₂ ⟧
-- ν⟦ Gs ⊢ var i ⟧ with lookupGrams i Gs
-- ... | G , Gs′ = ν ⟦ ⟦ Gs′ ⟧s ⊢ fixG G ⟧
-- ν⟦ Gs ⊢ □ □G ⟧ = ν□G □G Gs
-- 
-- data Singleton {a} {A : Set a} (x : A) : Set a where
--   _with≡_ : (y : A) → x ≡ y → Singleton x
-- 
-- inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
-- inspect x = x with≡ refl
-- 
-- νG-to : (G : Gram n) → ν⟦ Gs ⊢ G ⟧ → ν ⟦ ⟦ Gs ⟧s ⊢ G ⟧
-- νG-to ε x = refl
-- νG-to (A · G) (x , y) = x , νG-to G y
-- νG-to (G ∪ G₁) (inl x) = inl (νG-to G x)
-- νG-to (G ∪ G₁) (inr x) = inr (νG-to G₁ x)
-- νG-to (G ∙ G₁) (x , y) = [] , [] , refl , νG-to G x , νG-to G₁ y
-- νG-to {Gs = Gs} (var i) x with inspect (lookupGrams i Gs)
-- ... | G′ , Gs′ with≡ refl = subst (λ X → X []) (sym (lookup⟦⟧s i refl)) x
-- νG-to (□ □G) (□ x) = □ (νG-to (□G .!) x)
-- 
-- νG-from : (G : Gram n) → ν ⟦ ⟦ Gs ⟧s ⊢ G ⟧ → ν⟦ Gs ⊢ G ⟧
-- νG-from ε x = tt
-- νG-from (A · G) (x , y) = x , νG-from G y
-- νG-from (G ∪ G₁) (inl x) = inl (νG-from G x)
-- νG-from (G ∪ G₁) (inr x) = inr (νG-from G₁ x)
-- νG-from (G ∙ G₁) ([] , [] , refl , x , y) = νG-from G x , νG-from G₁ y
-- νG-from {Gs = Gs} (var i) x with inspect (lookupGrams i Gs)
-- ... | G′ , Gs′ with≡ refl = subst (λ X → X []) (lookup⟦⟧s i refl) x
-- νG-from (□ □G) (□ x) = □ (νG-from (□G .!) x)
-- 
-- νG-correct : ν⟦ Gs ⊢ G ⟧ ↔ ν ⟦ ⟦ Gs ⟧s ⊢ G ⟧
-- νG-correct {G = G} .to = νG-to G
-- νG-correct {G = G} .from = νG-from G
-- 
-- -- δ⟦_,_,_⊢_⟧ : Vec Set n → Vec (Gram m) n → Vec (Gram m) n → Gram n → Tok → Gram m
-- δG_[_⊢_] : Tok → Grams n → Gram n → Gram n 
-- 
-- -- data δ□G (c : Tok) (□G : □Gram n) (Gs : Grams n) : Set where
-- --   □ : δ c [ Gs ⊢ □G .! ] → δ□G □G Gs
-- 
-- wkG : (i : Fin n) → Gram (n - i) → Gram n
-- wkG zero G = renameG suc G
-- wkG (suc i) G = renameG suc (wkG i G)
-- 
-- δG c [ Gs ⊢ ∅ ] = ∅
-- δG c [ Gs ⊢ ε ] = ∅
-- δG c [ Gs ⊢ ‵ c′ ] with c ≟ c′
-- ... | yes _ = ε
-- ... | no _ = ∅
-- δG c [ Gs ⊢ A · G ] = A · (δG c [ Gs ⊢ G ])
-- δG c [ Gs ⊢ G ∪ G₁ ] = δG c [ Gs ⊢ G ] ∪ δG c [ Gs ⊢ G₁ ]
-- δG c [ Gs ⊢ G ∙ G₁ ] = δG c [ Gs ⊢ G ] ∙ {!substG G₁ (λ i → lookupGrams′ i Gs)!} ∪ (ν⟦ Gs ⊢ G ⟧ · δG c [ Gs ⊢ G₁ ])
-- δG c [ Gs ⊢ var i ] = var i
-- δG c [ Gs ⊢ □ □G ] = □ λ { .! → δG c [ Gs ⊢ □G .! ] }
-- 
-- δG-to : {Γ : Vec Lang n} (G : Gram n) {Gs : Grams n} → ⟦ Γ ⊢ δG c [ Gs ⊢ G ] ⟧ w → δ c ⟦ ⟦ Gs ⟧s ⊢ G ⟧ w
-- δG-to {c = c} (‵ c′) x with c ≟ c′
-- δG-to {c = c} (‵ c′) refl | yes refl = refl
-- δG-to {c = c} (‵ c′) () | no _
-- δG-to (A · G) (x , y) = {!!}
-- δG-to (G ∪ G₁) (inl x) = {!!}
-- δG-to (G ∪ G₁) (inr x) = {!!}
-- δG-to (G ∙ G₁) (inl (u , v , refl , x , y)) = {!!}
-- δG-to (G ∙ G₁) (inr (x , y)) = {!!}
-- δG-to (var i) x = {!!}
-- δG-to (□ □G) x = {!!}
-- 
-- postulate δG-correct : ⟦ {!!} ⊢ δG c [ Gs ⊢ G ] ⟧ w ↔ δ c ⟦ ⟦ Gs ⟧s ⊢ G ⟧ w

Γν-correct : Vec Lang n → Vec Set n → Set
Γν-correct Γ Γν = ∀ i → lookup Γν i ↔ ν (lookup Γ i)

-- the-Γν : Vec (Gram m) n → Vec Lang m → Vec Set n
-- the-Γν Γ Γ′ = mapVec (λ G → ν ⟦ Γ′ ⊢ G ⟧) Γ
-- 
-- the-Γν-correct : (Γ : Vec (Gram m) n) → Γν-correct (mapVec (λ G → ⟦ Γ′ ⊢ G ⟧) Γ) (the-Γν Γ Γ′)
-- the-Γν-correct (G ∷ Γ) zero = ↔refl
-- the-Γν-correct (G ∷ Γ) (suc i) = the-Γν-correct Γ i

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

conssub : (Fin n → Gram m) → Fin (suc n) → Gram (suc m)
conssub k zero = var zero
conssub k (suc i) = renameG suc (k i)

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

⊢rename-to : (G : Gram n) {f : Fin n → Fin m} →
             ⟦ Γ ⊢ renameG f G ⟧ w → ⟦ emaner f Γ ⊢ G ⟧ w
⊢rename-to ε x = x
⊢rename-to (‵ c) x = x
⊢rename-to (A · G) (x , y) = x , ⊢rename-to G y
⊢rename-to (G ∪ G₁) (inl x) = inl (⊢rename-to G x)
⊢rename-to (G ∪ G₁) (inr x) = inr (⊢rename-to G₁ x)
⊢rename-to (G ∙ G₁) (u , v , refl , x , y) = u , v , refl , ⊢rename-to G x , ⊢rename-to G₁ y
⊢rename-to {Γ = Γ} (var i) x = subst (λ X → X) (cong (λ f → f _) (lookup-f Γ i)) x
⊢rename-to (□ □G) (□ x) = □ (⊢rename-to (□G .!) x)

⊢rename-from : (G : Gram n) {f : Fin n → Fin m} →
               ⟦ emaner f Γ ⊢ G ⟧ w → ⟦ Γ ⊢ renameG f G ⟧ w
⊢rename-from ε x = x
⊢rename-from (‵ c) x = x
⊢rename-from (A · G) (x , y) = x , ⊢rename-from G y
⊢rename-from (G ∪ G₁) (inl x) = inl (⊢rename-from G x)
⊢rename-from (G ∪ G₁) (inr x) = inr (⊢rename-from G₁ x)
⊢rename-from (G ∙ G₁) (u , v , refl , x , y) = u , v , refl , ⊢rename-from G x , ⊢rename-from G₁ y
⊢rename-from {Γ = Γ} (var i) x = subst (λ X → X) (cong (λ f → f _) (sym (lookup-f Γ i))) x
⊢rename-from (□ □G) (□ x) = □ (⊢rename-from (□G .!) x)

⊢rename : ∀ G {f : Fin n → Fin m} → ⟦ Γ ⊢ renameG f G ⟧ w ↔ ⟦ emaner f Γ ⊢ G ⟧ w 
to (⊢rename G) = ⊢rename-to G
from (⊢rename G) = ⊢rename-from G

↔trans : (A ↔ B) → (B ↔ C) → (A ↔ C)
to (↔trans bi₁ bi₂) x = to bi₂ (to bi₁ x)
from (↔trans bi₁ bi₂) x = from bi₁ (from bi₂ x)

⇔rename : ∀ {f : Fin n → Fin m} → G ⇔ G′ → renameG f G ⇔ renameG f G′
⇔rename {G = G} {G′ = G′} bi = ↔trans (⊢rename G) (↔trans bi (↔sym (⊢rename G′)))

fixGsuc-to : (G : Gram n) {G₀ : Gram _} → ⟦ Γ ⊢ fixG′ G₀ (renameG suc G) ⟧ w → ⟦ Γ ⊢ G ⟧ w
fixGsuc-to G x = renamesuc G .to (unroll′ (renameG suc G) x)

fixGsuc-from : (G : Gram n) {G₀ : Gram _} → ⟦ Γ ⊢ G ⟧ w → ⟦ Γ ⊢ fixG′ G₀ (renameG suc G) ⟧ w
fixGsuc-from G x = roll′ (renameG suc G) (renamesuc G .from x)

postulate
    ⊢subst-to : (G : Gram n) {k : Fin n → Gram m} →
                ⟦ Γ ⊢ substG G k ⟧ w → ⟦ tsbus Γ k ⊢ G ⟧ w
--    ⊢subst-to ε x = x
--    ⊢subst-to (‵ c) x = x
--    ⊢subst-to (A · G) (x , y) = x , ⊢subst-to G y
--    ⊢subst-to (G ∪ G₁) (inl x) = inl (⊢subst-to G x)
--    ⊢subst-to (G ∪ G₁) (inr x) = inr (⊢subst-to G₁ x)
--    ⊢subst-to (G ∙ G₁) (u , v , refl , x , y) = u , v , refl , ⊢subst-to G x , ⊢subst-to G₁ y
--    ⊢subst-to {Γ = Γ} (var i) x = {!!}
--    ⊢subst-to (□ □G) (□ x) = □ (⊢subst-to (□G .!) x)

    ⊢subst-from : (G : Gram n) {k : Fin n → Gram m} →
                ⟦ tsbus Γ k ⊢ G ⟧ w → ⟦ Γ ⊢ substG G k ⟧ w
--    ⊢subst-from ε x = x
--    ⊢subst-from (‵ c) x = x
--    ⊢subst-from (A · G) (x , y) = x , ⊢subst-from G y
--    ⊢subst-from (G ∪ G₁) (inl x) = inl (⊢subst-from G x)
--    ⊢subst-from (G ∪ G₁) (inr x) = inr (⊢subst-from G₁ x)
--    ⊢subst-from (G ∙ G₁) (u , v , refl , x , y) = u , v , refl , ⊢subst-from G x , ⊢subst-from G₁ y
--    ⊢subst-from {Γ = Γ} (var i) x = {!!}
--    ⊢subst-from (□ □G) (□ x) = □ (⊢subst-from (□G .!) x)

⊢subst : ∀ G {k : Fin n → Gram m} → ⟦ Γ ⊢ substG G k ⟧ w ↔ ⟦ tsbus Γ k ⊢ G ⟧ w 
to (⊢subst G) = ⊢subst-to G
from (⊢subst G) = ⊢subst-from G

⇔subst : ∀ {k : Fin n → Gram m} → G ⇔ G′ → substG G k ⇔ substG G′ k
⇔subst {G = G} {G′ = G′} bi = ↔trans (⊢subst G) (↔trans bi (↔sym (⊢subst G′)))

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

νfix-to : ∀ {G₀} G → ν⟦ (⊥ ∷ Γν) ⊢ G ⟧ → ν⟦ Γν ⊢ fixG′ G₀ G ⟧
νfix-to ε _ = tt
νfix-to (A · G) (x , y) = x , νfix-to G y
νfix-to (G₁ ∪ G₂) (inl x) = inl (νfix-to G₁ x)
νfix-to (G₁ ∪ G₂) (inr x) = inr (νfix-to G₂ x)
νfix-to (G₁ ∙ G₂) (pl , pr) = νfix-to G₁ pl , νfix-to G₂ pr
νfix-to (var (suc i)) x = x
νfix-to (□ G) (□ x) = □ (νfix-to (! G) x)

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

-- derivative

δ⟦_⟧₀ : Gram zero → Tok → Gram zero

--           for ν       var to replace    fix to replace
--           vvvvvvvv    vvvvvv           vvvvvvvvv
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
δ⟦ Γν , Γδ , σ ⊢ □ G ⟧ c = □ (λ { .! → δ⟦ Γν , Γδ , σ ⊢ G .! ⟧ c })

δ⟦ G ⟧₀ = δ⟦ [] , [] , [] ⊢ G ⟧

variable Γδ : Vec (Gram m) n

Γδ-correct : Vec Lang n → Vec Lang m → Tok → Vec (Gram m) n → Set
Γδ-correct Γ Γ′ c Γδ = ∀ {w} i → ⟦ Γ′ ⊢ lookup Γδ i ⟧ w ↔ δ c (lookup Γ i) w

σ-correct : Vec Lang n → Vec Lang m → Vec (Gram m) n → Set
σ-correct Γ Γ′ σ = ∀ {w} i → ⟦ Γ′ ⊢ lookup σ i ⟧ w ↔ lookup Γ i w

the-σ-correct : (σ : Vec (Gram m) n) (Γ′ : Vec Lang m) → σ-correct (mapVec (λ G → ⟦ Γ′ ⊢ G ⟧) σ) Γ′ σ
the-σ-correct (_ ∷ _) Γ′ zero = ↔refl
the-σ-correct (_ ∷ σ) Γ′ (suc i) = the-σ-correct σ Γ′ i

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

δG-sound′ : (G : Gram zero) → ⟦ δ⟦ [] , [] , [] ⊢ G ⟧ c ⟧ w → δ c ⟦ G ⟧ w
δG-sound′ {c = c′} (‵ c) x with c ≟ c′
δG-sound′ {c = c′} (‵ c) refl | yes refl = refl
δG-sound′ {c = c′} (‵ c) () | no _
δG-sound′ (A · G) (x , y) = x , δG-sound′ G y
δG-sound′ (G ∪ G₁) (inl x) = inl (δG-sound′ G x)
δG-sound′ (G ∪ G₁) (inr x) = inr (δG-sound′ G₁ x)
δG-sound′ {c = c} (G ∙ G₁) (inl (u , v , refl , x , y)) = (c ∷ u) , v , refl , δG-sound′ G x , σ-corollary [] (λ ()) G₁ .to y
δG-sound′ (G ∙ G₁) (inr (x , y)) = [] , _ , refl , νG-sound G (λ ()) x , δG-sound′ G₁ y
δG-sound′ (□ □G) (□ x) = □ (δG-sound′ (□G .!) x)

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
δG-complete Γν Γδ σ (□ G) (□ x) = □ (δG-complete Γν Γδ σ (G .!) x)

δG-correct : Γν-correct Γ Γν → Γδ-correct Γ Γ′ c Γδ → σ-correct Γ Γ′ σ → (G : Gram n) → ⟦ Γ′ ⊢ (δ⟦ Γν , Γδ , σ ⊢ G ⟧ c) ⟧ w ↔ δ c ⟦ Γ ⊢ G ⟧ w
to (δG-correct Γν Γδ σ G) = δG-sound Γν Γδ σ G
from (δG-correct Γν Γδ σ G) = δG-complete Γν Γδ σ G

νunroll-to : {G₀ : Gram (suc n)} (G : Gram (suc n)) →
             ν⟦ Γν ⊢ fixG′ G₀ G ⟧ → ν⟦ ν⟦ Γν ⊢ fixG G₀ ⟧ ∷ Γν ⊢ G ⟧
νunroll-to ε x = tt
νunroll-to (A · G) (x , y) = x , νunroll-to G y
νunroll-to (G ∪ G₁) (inl x) = inl (νunroll-to G x)
νunroll-to (G ∪ G₁) (inr x) = inr (νunroll-to G₁ x)
νunroll-to (G ∙ G₁) (x , y) = νunroll-to G x , νunroll-to G₁ y
νunroll-to (var zero) (□ x) = x
νunroll-to (var (suc i)) x = x
νunroll-to (□ □G) (□ x) = □ (νunroll-to (□G .!) x)

νunroll-from : {G₀ : Gram (suc n)} (G : Gram (suc n)) →
               ν⟦ ν⟦ Γν ⊢ fixG G₀ ⟧ ∷ Γν ⊢ G ⟧ → ν⟦ Γν ⊢ fixG′ G₀ G ⟧
νunroll-from ε x = tt
νunroll-from (A · G) (x , y) = x , νunroll-from G y
νunroll-from (G ∪ G₁) (inl x) = inl (νunroll-from G x)
νunroll-from (G ∪ G₁) (inr x) = inr (νunroll-from G₁ x)
νunroll-from (G ∙ G₁) (x , y) = νunroll-from G x , νunroll-from G₁ y
νunroll-from (var zero) x = □ x
νunroll-from (var (suc i)) x = x
νunroll-from (□ □G) (□ x) = □ (νunroll-from (□G .!) x)

νunroll : {G₀ : Gram (suc n)} (G : Gram (suc n)) → ν⟦ Γν ⊢ fixG′ G₀ G ⟧ ↔ ν⟦ ν⟦ Γν ⊢ fixG G₀ ⟧ ∷ Γν ⊢ G ⟧ 
νunroll G .to = νunroll-to G
νunroll G .from = νunroll-from G

fix-suc-to : ∀ (G : Gram n) {G₀ : Gram (suc n)} {Γ : Vec Lang n}
               {w} →
             ⟦ Γ ⊢ G ⟧ w → ⟦ Γ ⊢ fixG′ G₀ (renameG suc G) ⟧ w
fix-suc-to ε x = x
fix-suc-to (‵ c) x = x
fix-suc-to (A · G) (x , y) = x , fix-suc-to G y
fix-suc-to (G ∪ G₁) (inl x) = inl (fix-suc-to G x)
fix-suc-to (G ∪ G₁) (inr x) = inr (fix-suc-to G₁ x)
fix-suc-to (G ∙ G₁) (u , v , refl , x , y) = u , v , refl , fix-suc-to G x , fix-suc-to G₁ y
fix-suc-to (var i) x = x
fix-suc-to (□ □G) (□ x) = □ (fix-suc-to (□G .!) x)

fix-suc-from : ∀ (G : Gram n) {G₀ : Gram (suc n)} {Γ : Vec Lang n}
                 {w} →
               ⟦ Γ ⊢ fixG′ G₀ (renameG suc G) ⟧ w → ⟦ Γ ⊢ G ⟧ w
fix-suc-from ε x = x
fix-suc-from (‵ c) x = x
fix-suc-from (A · G) (x , y) = x , fix-suc-from G y
fix-suc-from (G ∪ G₁) (inl x) = inl (fix-suc-from G x)
fix-suc-from (G ∪ G₁) (inr x) = inr (fix-suc-from G₁ x)
fix-suc-from (G ∙ G₁) (u , v , refl , x , y) = u , v , refl , fix-suc-from G x , fix-suc-from G₁ y
fix-suc-from (var i) x = x
fix-suc-from (□ □G) (□ x) = □ (fix-suc-from (□G .!) x)

fix-suc : ∀ (G : Gram n) {G₀ : Gram (suc n)} → G ⇔ fixG′ G₀ (renameG suc G)
to (fix-suc G) = fix-suc-to G
from (fix-suc G) = fix-suc-from G

subst-lookup-map-to : ∀ {n′} {f : Fin m → Fin n′}
                        (σ : Vec (Gram m) n) (G : Gram n) {Γ : Vec Lang n′} {w}
                        (x : ⟦ Γ ⊢ substG G (lookup (mapVec (renameG f) σ)) ⟧ w) →
                      ⟦ Γ ⊢ renameG f (substG G (lookup σ)) ⟧ w
subst-lookup-map-to σ ε x = x
subst-lookup-map-to σ (‵ c) x = x
subst-lookup-map-to σ (A · G) (x , y) = x , subst-lookup-map-to σ G y
subst-lookup-map-to σ (G ∪ G₁) (inl x) = inl (subst-lookup-map-to σ G x)
subst-lookup-map-to σ (G ∪ G₁) (inr x) = inr (subst-lookup-map-to σ G₁ x)
subst-lookup-map-to σ (G ∙ G₁) (u , v , refl , x , y) = u , v , refl , subst-lookup-map-to σ G x , subst-lookup-map-to σ G₁ y
subst-lookup-map-to {f = f} σ (var i) {Γ = Γ} {w = w} x = subst (λ X → ⟦ Γ ⊢ X ⟧ w) (lookup-map (renameG f) σ i) x
subst-lookup-map-to σ (□ □G) (□ x) = □ (subst-lookup-map-to σ (□G .!) x)

subst-lookup-map-from : ∀ {n′} {f : Fin m → Fin n′}
                          (v : Vec (Gram m) n) (G : Gram n) {Γ : Vec Lang n′} {w} →
                        ⟦ Γ ⊢ renameG f (substG G (lookup v)) ⟧ w →
                        ⟦ Γ ⊢ substG G (lookup (mapVec (renameG f) v)) ⟧ w
subst-lookup-map-from σ ε x = x
subst-lookup-map-from σ (‵ c) x = x
subst-lookup-map-from σ (A · G) (x , y) = x , subst-lookup-map-from σ G y
subst-lookup-map-from σ (G ∪ G₁) (inl x) = inl (subst-lookup-map-from σ G x)
subst-lookup-map-from σ (G ∪ G₁) (inr x) = inr (subst-lookup-map-from σ G₁ x)
subst-lookup-map-from σ (G ∙ G₁) (u , v , refl , x , y) = u , v , refl , subst-lookup-map-from σ G x , subst-lookup-map-from σ G₁ y
subst-lookup-map-from (x₁ ∷ σ) (var zero) x = x
subst-lookup-map-from (x₁ ∷ σ) (var (suc i)) x = subst-lookup-map-from σ (var i) x
subst-lookup-map-from σ (□ □G) (□ x) = □ (subst-lookup-map-from σ (□G .!) x)

subst-lookup-map : ∀ {n′} {f : Fin m → Fin n′} (v : Vec (Gram m) n) → (G : Gram n) → substG G (lookup (mapVec (renameG f) v)) ⇔ renameG f (substG G (lookup v))
to (subst-lookup-map v G) = subst-lookup-map-to v G
from (subst-lookup-map v G) = subst-lookup-map-from v G

subst-lookup-fix-to : ∀ {G₀ : Gram (suc n)}
                     (G : Gram (suc n)) →
                     ⟦ Γ ⊢ substG (fixG′ G₀ G) (lookup σ) ⟧ v →
                   ⟦ Γ ⊢ substG G (lookup (substG (fixG G₀) (lookup σ) ∷ σ)) ⟧ v
subst-lookup-fix-to ε x = x
subst-lookup-fix-to (‵ c) x = x
subst-lookup-fix-to (A · G) (x , y) = x , subst-lookup-fix-to G y
subst-lookup-fix-to (G ∪ G₁) (inl x) = inl (subst-lookup-fix-to G x)
subst-lookup-fix-to (G ∪ G₁) (inr x) = inr (subst-lookup-fix-to G₁ x)
subst-lookup-fix-to (G ∙ G₁) (u , v , refl , x , y) = u , v , refl , subst-lookup-fix-to G x , subst-lookup-fix-to G₁ y
subst-lookup-fix-to (var zero) (□ x) = x
subst-lookup-fix-to (var (suc i)) x = x
subst-lookup-fix-to (□ □G) (□ x) = □ (subst-lookup-fix-to (□G .!) x)

subst-lookup-fix-from : ∀ {G₀ : Gram (suc n)} (G : Gram (suc n))
                          {Γ : Vec Lang m} {w} →
                        ⟦ Γ ⊢ substG G (lookup (substG (fixG G₀) (lookup σ) ∷ σ)) ⟧ w →
                        ⟦ Γ ⊢ substG (fixG′ G₀ G) (lookup σ) ⟧ w
subst-lookup-fix-from ε x = x
subst-lookup-fix-from (‵ c) x = x
subst-lookup-fix-from (A · G) (x , y) = x , subst-lookup-fix-from G y
subst-lookup-fix-from (G ∪ G₁) (inl x) = inl (subst-lookup-fix-from G x)
subst-lookup-fix-from (G ∪ G₁) (inr x) = inr (subst-lookup-fix-from G₁ x)
subst-lookup-fix-from (G ∙ G₁) (u , v , refl , x , y) = u , v , refl , subst-lookup-fix-from G x , subst-lookup-fix-from G₁ y
subst-lookup-fix-from (var zero) x = □ x
subst-lookup-fix-from (var (suc i)) x = x
subst-lookup-fix-from (□ □G) (□ x) = □ (subst-lookup-fix-from (□G .!) x)

subst-lookup-fix : ∀ {G₀ : Gram (suc n)}
                     (G : Gram (suc n)) →
                     substG (fixG′ G₀ G) (lookup σ)
                   ⇔ substG G (lookup (substG (fixG G₀) (lookup σ) ∷ σ))
to (subst-lookup-fix G) = subst-lookup-fix-to G
from (subst-lookup-fix G) = subst-lookup-fix-from G

mapfix : ∀ {G G′ G₀} → (∀ {Γ w} → ⟦ Γ ⊢ G ⟧ w → ⟦ Γ ⊢ G′ ⟧ w) → ⟦ Γ ⊢ fixG′ G₀ G ⟧ w → ⟦ Γ ⊢ fixG′ G₀ G′ ⟧ w
mapfix {G = G} {G′} {G₀} f x = roll′ G′ (f (unroll′ G x))

δunroll-to : ∀ {c} {w} {G₀ : Gram (suc n)} (G : Gram (suc n))
               {Γν : Vec Set n} {Γδ : Vec (Gram m) n}
           → ⟦ Γ ⊢ δ⟦ Γν , Γδ , σ ⊢ fixG′ G₀ G ⟧ c ⟧ w
           → ⟦ Γ ⊢
             fixG′
             (δ⟦ ν⟦ Γν ⊢ fixG G₀ ⟧ ∷ Γν
               , var zero ∷ mapVec (renameG suc) Γδ
               , renameG suc (substG (fixG G₀) (lookup σ)) ∷ mapVec (renameG suc) σ
               ⊢ G₀
               ⟧ c)
             (δ⟦ ν⟦ Γν ⊢ fixG G₀ ⟧ ∷ Γν
               , var zero ∷ mapVec (renameG suc) Γδ
               , renameG suc (substG (fixG G₀) (lookup σ)) ∷ mapVec (renameG suc) σ
               ⊢ G ⟧ c)
             ⟧
             w
δunroll-to {c = c} (‵ c′) x with c′ ≟ c
... | yes _ = x
... | no _ = x
δunroll-to (A · G) (x , y) = x , δunroll-to G y
δunroll-to (G ∪ G₁) (inl x) = inl (δunroll-to G x)
δunroll-to (G ∪ G₁) (inr x) = inr (δunroll-to G₁ x)
δunroll-to {Γ = Γ} {σ = σ} {c = c} {w = w} {G₀ = G₀} (G ∙ G₁) {Γν = Γν} {Γδ = Γδ} (inl (u , v , refl , x , y)) = inl (u , v , refl , δunroll-to G x ,
  mapfix {_} {Γ} {v}
    {renameG suc (substG G₁ (lookup (substG (fixG G₀) (lookup σ) ∷ σ)))}
    {(substG G₁
      (lookup
       (renameG suc (substG (fixG G₀) (lookup σ)) ∷
        mapVec (renameG suc) σ)))}
    {δ⟦ ν⟦ Γν ⊢ fixG G₀ ⟧ ∷ Γν , var zero ∷ mapVec (renameG suc) Γδ ,
      renameG suc (substG (fixG G₀) (lookup σ)) ∷ mapVec (renameG suc) σ
      ⊢ G₀ ⟧
      c}
    (subst-lookup-map {f = suc} (substG (fixG G₀) (lookup σ) ∷ σ) G₁ .from)
    (fix-suc (substG G₁ (lookup (substG (fixG G₀) (lookup σ) ∷ σ))) .to
    (subst-lookup-fix G₁ .to y)
    )
  )
δunroll-to (G ∙ G₁) (inr (x , y)) = inr (νunroll-to G x , δunroll-to G₁ y)
δunroll-to {G₀ = G₀} (var zero) (□ x) = □ (δunroll-to G₀ x)
δunroll-to {σ = σ} (var (suc i)) {Γδ = Γδ} x =
  subst (λ G → ⟦ _ ⊢ fixG′ _ G ⟧ _) (sym (lookup-map (renameG suc) Γδ i)) (fix-suc (lookup Γδ i) .to x)
δunroll-to (□ □G) (□ x) = □ (δunroll-to (□G .!) x)

-- δunroll-from : ∀ {c} {w} {G₀ : Gram (suc n)} (G : Gram (suc n))
--                  {Γν : Vec Set n} {Γδ : Vec (Gram m) n} {Γ : Vec Lang m}
--                  (x
--                   : ⟦ Γ ⊢
--                     fixG′
--                     (δ⟦ ν⟦ Γν ⊢ fixG G₀ ⟧ ∷ Γν , var zero ∷ mapVec (renameG suc) Γδ ,
--                      renameG suc (substG (fixG G₀) (lookup σ)) ∷ mapVec (renameG suc) σ
--                      ⊢ G₀ ⟧
--                      c)
--                     (δ⟦ ν⟦ Γν ⊢ fixG G₀ ⟧ ∷ Γν , var zero ∷ mapVec (renameG suc) Γδ ,
--                      renameG suc (substG (fixG G₀) (lookup σ)) ∷ mapVec (renameG suc) σ
--                      ⊢ G ⟧
--                      c)
--                     ⟧
--                     w) →
--                ⟦ Γ ⊢ δ⟦ Γν , Γδ , σ ⊢ fixG′ G₀ G ⟧ c ⟧ w
-- δunroll-from {c = c′} (‵ c) x with c ≟ c′
-- ... | yes _ = x
-- ... | no _ = x
-- δunroll-from (A · G) (x , y) = x , δunroll-from G y
-- δunroll-from (G ∪ G₁) (inl x) = inl (δunroll-from G x)
-- δunroll-from (G ∪ G₁) (inr x) = inr (δunroll-from G₁ x)
-- δunroll-from {σ = σ} {G₀ = G₀} (G ∙ G₁) (inl (u , v , refl , x , y)) = inl (u , v , refl , δunroll-from G x ,
--   subst-lookup-fix G₁ .from
--     (fix-suc (substG G₁ (lookup (substG (fixG G₀) (lookup σ) ∷ σ))) .from
--       (mapfix {_} {_} {_} {substG G₁ _} {renameG suc (substG G₁ (lookup (substG (fixG G₀) (lookup σ) ∷ σ)))} {_}
--         (subst-lookup-map {f = suc} (substG (fixG G₀) (lookup σ) ∷ σ) G₁ .to)
--         y))
--   )
-- δunroll-from (G ∙ G₁) (inr (x , y)) = inr (νunroll-from G x , δunroll-from G₁ y)
-- δunroll-from {G₀ = G} (var zero) (□ x) = □ (δunroll-from G x)
-- δunroll-from (var (suc i)) {Γδ = Γδ} x =
--   let x = subst (λ G → ⟦ _ ⊢ fixG′ _ G ⟧ _) (lookup-map (renameG suc) Γδ i) x
--   in fix-suc (lookup Γδ i) .from x
-- δunroll-from (□ □G) (□ x) = □ (δunroll-from (□G .!) x)

δunroll : ∀{c w} {G₀ : Gram (suc n)} (G : Gram (suc n)) {σ : Vec (Gram n) n} {Gs : Vec (Gram n) n}
        → {Γ : Vec Lang n}
        → ⟦ Γ ⊢ δ⟦ mapVec ν⟦ tabulate (λ _ → ⊥) ⊢_⟧ Gs , tabulate var , σ ⊢ fixG′ G₀ G ⟧ c ⟧ w
        ↔ ⟦ Γ ⊢ fixG′
                (δ⟦ mapVec ν⟦ tabulate (λ _ → ⊥) ⊢_⟧ (G₀ ∷ mapVec (renameG suc) Gs)
                    , tabulate var
                    , renameG suc (substG (fixG G₀) (lookup σ)) ∷ mapVec (renameG suc) σ
                    ⊢ G₀ ⟧ c)
                (δ⟦ mapVec ν⟦ tabulate (λ _ → ⊥) ⊢_⟧ (G₀ ∷ mapVec (renameG suc) Gs)
                    , tabulate var
                    , renameG suc (substG (fixG G₀) (lookup σ)) ∷ mapVec (renameG suc) σ
                    ⊢ G ⟧ c)
        ⟧ w
δunroll {n = n} G {Gs = Gs} {Γ = Γ} .to x = {!δunroll-to {n} {n} {Γ} {_} {_} {_} {_} G {mapVec ν⟦ _ ⊢_⟧ Gs} {tabulate var} x!}
δunroll G .from x = {!δunroll-from G x!}

_⇒_ : (G₁ G₂ : Gram n) → Set₁
G₁ ⇒ G₂ = ∀ {Γ w} → ⟦ Γ ⊢ G₁ ⟧ w → ⟦ Γ ⊢ G₂ ⟧ w

mapδ-to : ∀ G₁ G₂ (f : G₁ ⇒ G₂) {Γ : Vec Lang m} {w} →
          δ c ⟦ Γ ⊢ G₁ ⟧ w → δ c ⟦ Γ ⊢ G₂ ⟧ w
mapδ-to G₁ G₂ f = f

-- mapδ : (∀{Γ i} → lookup Γν i ↔ ν ⟦ Γ ⊢ lookup σ i ⟧) → (∀{Γ i w} → ⟦ Γ ⊢ lookup Γδ i ⟧ w ↔ δ c ⟦ Γ ⊢ lookup σ i ⟧ w) → G₁ ⇔ G₂ → δ⟦ Γν , Γδ , σ ⊢ G₁ ⟧ c ⇔ δ⟦ Γν , Γδ , σ ⊢ G₂ ⟧ c
-- mapδ {Γν = Γν} {σ = σ} {Γδ = Γδ} {G₁ = G₁} {G₂ = G₂} Γνc Γδc bi {Γ} {w} =
--   ↔trans
--     (δG-correct
--       {Γ = mapVec (λ G → ⟦ Γ ⊢ G ⟧) σ}
--       {Γν = Γν}
--       {Γ′ = Γ}
--       {Γδ = Γδ}
--       {σ = σ}
--       (λ i → {!!}) -- subst (λ X → lookup Γν i ↔ X _) (sym (lookup-map (λ G → ⟦ Γ ⊢ G ⟧) σ i)) Γνc)
--       (λ i → {!!}) -- subst (λ X → ⟦ Γ ⊢ lookup Γδ i ⟧ _ ↔ X _) (sym (lookup-map (λ G → ⟦ Γ ⊢ G ⟧) σ i)) Γδc)
--       (λ i → {!!}) -- subst (λ X → ⟦ Γ ⊢ lookup σ i ⟧ _ ↔ X _) (sym (lookup-map (λ G → ⟦ Γ ⊢ G ⟧) σ i)) ↔refl)
--       G₁)
--   (↔trans
--     bi
--     (↔sym
--     (δG-correct
--       {Γ = mapVec (λ G → ⟦ Γ ⊢ G ⟧) σ}
--       {Γν = Γν}
--       {Γ′ = Γ}
--       {Γδ = Γδ}
--       {σ = σ}
--       (λ i → subst (λ X → lookup Γν i ↔ X _) (sym (lookup-map (λ G → ⟦ Γ ⊢ G ⟧) σ i)) Γνc)
--       (λ i → subst (λ X → ⟦ Γ ⊢ lookup Γδ i ⟧ _ ↔ X _) (sym (lookup-map (λ G → ⟦ Γ ⊢ G ⟧) σ i)) Γδc)
--       (λ i → subst (λ X → ⟦ Γ ⊢ lookup σ i ⟧ _ ↔ X _) (sym (lookup-map (λ G → ⟦ Γ ⊢ G ⟧) σ i)) ↔refl)
--       G₂)))
-- 

