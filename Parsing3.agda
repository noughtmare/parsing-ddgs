open import Agda.Builtin.Equality
open import Level using (Level)

data Symbol : Set where
  `+ `≤ `x `[ `] `:= `, `while `do `return `0 `1 `2 `3 `4 `5 `6 `7 `8 `9 : Symbol

data String : Set where
  [] : String
  _∷_ : Symbol → String → String
infixr 5 _∷_

variable w : String

_++_ : (_ _ : String) → String
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys
infixr 5 _++_

data ⊥ : Set where
data ⊤ : Set where
  tt : ⊤
data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    π₁ : A
    π₂ : B
record Σ (A : Set) (f : A → Set) : Set where
  constructor _,_
  field
    π₁ : A
    π₂ : f π₁
infixr 4 _,_
infixr 2 _×_
infixr 1 _⊎_

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

variable n : Nat

data Fin : Nat → Set where
  zero : Fin (suc n)
  suc : Fin n → Fin (suc n)

Lang : Set₁
Lang = String → Set

module ◇ where
  ∅ ε : Lang
  ∅ _ = ⊥
  ε w = w ≡ []

  `_ : Symbol → Lang
  (` c) w = w ≡ c ∷ []

  _∪_ _∙_ : (_ _ : Lang) → Lang
  (L₁ ∪ L₂) w = L₁ w ⊎ L₂ w
  (L₁ ∙ L₂) w = Σ String λ u → Σ String λ v → w ≡ u ++ v × L₁ u × L₂ v
  

const : {ℓ ℓ′ : Level} {A : Set ℓ} {B : Set ℓ′} → A → B → A
const x _ = x

Lang₁ : Nat → Set₁
Lang₁ n = (Fin n → Lang) → Lang

data Gram₁ (n : Nat) : (Lang₁ n) → Set₁ where
  ∅ : Gram₁ n (const ◇.∅)
  ε : Gram₁ n (const ◇.ε)
  `_ : (c : Symbol) → Gram₁ n (const (◇.` c))
  _∪_ : {L₁ L₂ : Lang₁ n} → Gram₁ n L₁ → Gram₁ n L₂ → Gram₁ n (λ Γ → L₁ Γ ◇.∪ L₂ Γ)
  _∙_ : {L₁ L₂ : Lang₁ n} → Gram₁ n L₁ → Gram₁ n L₂ → Gram₁ n (λ Γ → L₁ Γ ◇.∙ L₂ Γ)
  var : (i : Fin n) → Gram₁ n (λ Γ → Γ i)
infixr 100 `_

infixr 1 _∪_
infixr 2 _∙_

-- there's always a starting nonterminal, which has index zero.
record Gram : Set₁ where
  field
    nonterminal : Nat
    L : Fin (suc nonterminal) → Lang₁ (suc nonterminal)
    production : (i : Fin (suc nonterminal)) → Gram₁ (suc nonterminal) (L i)

variable
  A : Set
  G G₁ G₂ : Gram

⟦_⟧₁ : {L : Lang₁ n} → Gram₁ n L → (Fin n → Lang) → Lang
⟦ ∅ ⟧₁ _ _ = ⊥
⟦ ε ⟧₁ _ w = w ≡ []
⟦ ` c ⟧₁ _ w = w ≡ c ∷ []
⟦ G₁ ∪ G₂ ⟧₁ Γ w = ⟦ G₁ ⟧₁ Γ w ⊎ ⟦ G₂ ⟧₁ Γ w
⟦ G₁ ∙ G₂ ⟧₁ Γ w = Σ String λ u → Σ String λ v → w ≡ u ++ v × ⟦ G₁ ⟧₁ Γ u × ⟦ G₂ ⟧₁ Γ v
⟦ var x ⟧₁ Γ w = Γ x w

cong : {A B : Set} → (P : Set → Set) → A ≡ B → P A ≡ P B
cong _ refl = refl

cong₂ : {ℓ : Level} {A B C : Set ℓ} {x x′ : A} {y y′ : B} → (P : A → B → C) → x ≡ x′ → y ≡ y′ → P x y ≡ P x′ y′
cong₂ _ refl refl = refl

postulate funext : {A : Set} {f g : A → Set} → ((x : A) → f x ≡ g x) → f ≡ g

⟦_⟧₁≡L : {L : Lang₁ n} (G : Gram₁ n L) {Γ : Fin n → Lang} {w : String} → ⟦ G ⟧₁ Γ w ≡ L Γ w
⟦ ∅ ⟧₁≡L = refl
⟦ ε ⟧₁≡L = refl
⟦ ` c ⟧₁≡L = refl
⟦ G ∪ G₁ ⟧₁≡L = cong₂ _⊎_ ⟦ G ⟧₁≡L ⟦ G₁ ⟧₁≡L
⟦ G ∙ G₁ ⟧₁≡L {_} {w} = cong₂ (λ L₁ L₂ → (L₁ ◇.∙ L₂) w) (funext (λ u → ⟦ G ⟧₁≡L {_} {u})) (funext (λ v → ⟦ G₁ ⟧₁≡L {_} {v}))
⟦ var i ⟧₁≡L = refl

data μ {L : Fin n → Lang₁ n} (F : (i : Fin n) → Gram₁ n (L i)) (S : Fin n) : Lang where
  step : ⟦ F S ⟧₁ (μ F) w → μ F S w

⟦_⟧ : Gram → Lang
⟦ G ⟧ = let open Gram G in μ production zero

ν : Lang → Set
δ : Symbol → Lang → Lang

ν L = L []
δ c L w = L (c ∷ w)

data Dec (A : Set) : Set where
  yes : A → Dec A
  no : (A → ⊥) → Dec A

variable L : Lang₁ n

ν₁? : {Γ : Fin n → Lang} → Gram₁ n L → ((i : Fin n) → Dec (ν (Γ i))) → Dec (ν (L Γ))
ν₁? ∅ _ = no (λ z → z)
ν₁? ε _ = yes refl
ν₁? (` c) _ = no (λ ())
ν₁? {Γ = Γ} (G ∪ G₁) ev with ν₁? {Γ = Γ} G ev | ν₁? {Γ = Γ} G₁ ev
... | yes x | _ = yes (inl x)
... | no _ | yes y = yes (inr y)
... | no ¬x | no ¬y = no λ where
  (inl x) → ¬x x
  (inr y) → ¬y y
ν₁? {Γ = Γ} (G ∙ G₁) ev with ν₁? {Γ = Γ} G ev | ν₁? {Γ = Γ} G₁ ev
... | yes x | yes y = yes ([] , [] , refl , x , y)
... | yes _ | no ¬y = no λ where
  ([] , [] , refl , _ , y) → ¬y y
... | no ¬x | _ = no λ where
  ([] , [] , refl , x , _) → ¬x x
ν₁? (var i) ev = ev i

mut : Gram
mut = record
  { nonterminal = suc zero
  ; L = λ { zero → _ ; (suc zero) → _ }
  ; production = λ where
    zero → var (suc zero)
    (suc zero) → var zero
  }

¬νmut : ν ⟦ mut ⟧ → ⊥
¬νmut (step (step x)) = ¬νmut x



ν? : (G : Gram) → Dec (ν ⟦ G ⟧)
ν? G = {!!}
  where open Gram G

-- ⟦_⟧ : Gram → Lang
-- ⟦ G ⟧ = let open Gram G in ⟦ production zero ⟧₁ (μ production)
-- 
-- digit : Gram₁ n
-- digit = ` `0 ∪ ` `1 ∪ ` `2 ∪ ` `3 ∪ ` `4 ∪ ` `5 ∪ ` `6 ∪ ` `7 ∪ ` `8 ∪ ` `9
-- 
-- imp : Gram
-- imp = record
--     { nonterminal = suc (suc zero)
--     ; production = λ where
--         stmt → ` `x ∙ ` `:= ∙ var expr ∪ var stmt ∙ ` `, ∙ var stmt ∪ ` `while ∙ var expr ∙ ` `do ∙ var stmt ∪ ` `return ∙ var expr
--         expr → ` `x ∪ var nat ∪ var expr ∙ ` `+ ∙ var expr ∪ var expr ∙ ` `≤ ∙ var expr ∪ ` `[ ∙ var stmt ∙ ` `]
--         nat → digit ∪ digit ∙ var nat
--     } where pattern stmt = zero
--             pattern expr = suc zero
--             pattern nat = suc (suc zero)
-- 
-- 
-- palindrome : Gram
-- palindrome = record
--   { nonterminal = zero
--   ; production = λ _ → ` `0 ∙ var zero ∙ ` `0
--                      ∪ ` `1 ∙ var zero ∙ ` `1
--                      ∪ ε ∪ ` `1 ∪ ` `0
--   }
-- 
-- _ : ⟦ palindrome ⟧ (`1 ∷ `0 ∷ `1 ∷ [])
-- _ = inr (inl (`1 ∷ [] , _ , refl , refl , `0 ∷ [] , _ , refl , step (inr (inr (inr (inr refl)))) , refl))
-- 
-- -- _⇒_ : (_ _ : Gram₁ A) → Set₁
-- -- _⇒_ {A} G₁ G₂ = {x : A} {Γ″ : A → Lang} {w : String} → ⟦ G₁ ⟧₁ Γ″ w → ⟦ G₂ ⟧₁ Γ″ w
-- 
-- map⟦_⟧₁ : {Γ Γ′ : Fin n → Lang} (G : Gram₁ n) {w : String} → ((i : Fin n) {w : String} → Γ i w → Γ′ i w) → ⟦ G ⟧₁ Γ w → ⟦ G ⟧₁ Γ′ w
-- map⟦ ∅ ⟧₁ _ ()
-- map⟦ ε ⟧₁ _ refl = refl
-- map⟦ ` c ⟧₁ _ x = x
-- map⟦ G ∪ G₁ ⟧₁ ev (inl x) = inl (map⟦ G ⟧₁ ev x)
-- map⟦ G ∪ G₁ ⟧₁ ev (inr x) = inr (map⟦ G₁ ⟧₁ ev x)
-- map⟦ G ∙ G₁ ⟧₁ ev (u , v , refl , x , y) = u , v , refl , map⟦ G ⟧₁ ev x , map⟦ G₁ ⟧₁ ev y
-- map⟦ var i ⟧₁ ev = ev i
-- 
-- νμ→∅ : (F : Fin n → Gram₁ n) (S : Fin n) → ν (μ F S) → ν (⟦ F S ⟧₁ (λ _ _ → ⊥))
-- νμ→∅ F S (step x) with F S
-- ... | ε = refl
-- νμ→∅ F S (step (inl x)) | G₁ ∪ G₂ = inl (map⟦ G₁ ⟧₁ {!!} x)
-- νμ→∅ F S (step (inr x)) | G₁ ∪ G₂ = {!!}
-- ... | G₁ ∙ G₂ = {!!}
-- ... | var v = {!!}
-- 
-- ν₁? : (G : Gram₁ n) {Γ : Fin n → Lang} → ((i : Fin n) → Dec (ν (Γ i))) → Dec (ν (⟦ G ⟧₁ Γ))
-- ν₁? ∅ ev = no (λ ())
-- ν₁? ε ev = yes refl
-- ν₁? (` x) ev = no (λ ())
-- ν₁? (G₁ ∪ G₂) ev with ν₁? G₁ ev | ν₁? G₂ ev
-- ... | yes x | _ = yes (inl x)
-- ... | no _ | yes y = yes (inr y)
-- ... | no ¬x | no ¬y = no (λ where
--   (inl x) → ¬x x
--   (inr y) → ¬y y)
-- ν₁? (G₁ ∙ G₂) ev with ν₁? G₁ ev | ν₁? G₂ ev
-- ... | yes x | yes y = yes ([] , [] , refl , x , y)
-- ... | yes _ | no ¬y = no λ where ([] , [] , refl , _ , y) → ¬y y
-- ... | no ¬x | _ = no λ where ([] , [] , refl , x , _) → ¬x x
-- ν₁? (var x) ev = ev x
-- 
-- νμ? : (G : Gram) → let open Gram G in Dec (ν (μ production zero))
-- νμ? G = {!!}
--   where open Gram G
-- 
-- ν? : (G : Gram) → Dec (ν ⟦ G ⟧)
-- ν? G with νμ? G
-- ... | yes (step x) = yes x
-- ... | no ¬x = no λ x → ¬x (step x)
--   where open Gram G
-- 
-- δ? : Symbol → Gram → Gram
-- δ? = {!!}
-- 
