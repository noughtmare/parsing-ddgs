{-# OPTIONS --safe #-}

--------------------------------------------------------------------------------
-- Basic definitions
--------------------------------------------------------------------------------

data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x

data Symbol : Set where
  `+ : Symbol
  `x : Symbol

data ⊥ : Set where

data Dec (A : Set) : Set where
  yes : A → Dec A
  no : (A → ⊥) → Dec A

_≟_ : (a b : Symbol) → Dec (a ≡ b)
`+ ≟ `+ = yes refl
`+ ≟ `x = no (λ ())
`x ≟ `+ = no (λ ())
`x ≟ `x = yes refl

data String : Set where
  [] : String
  _∷_ : Symbol → String → String

_++_ : (_ _ : String) → String
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

variable w : String

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

_⊎?_ : {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎? _ = yes (inl x)
no x ⊎? yes y = yes (inr y)
no ¬x ⊎? no ¬y = no λ where
  (inl x) → ¬x x
  (inr y) → ¬y y

_×?_ : {A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×? yes y = yes (x , y)
yes x ×? no ¬y = no (λ z → ¬y (_×_.π₂ z))
no ¬x ×? y = no (λ z → ¬x (_×_.π₁ z))

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    π₁ : A
    π₂ : B π₁

infixr 20 _,_

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

variable n : Nat

data Fin : Nat → Set where
  zero : Fin (suc n)
  suc : Fin n → Fin (suc n)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

concat : List String → String
concat [] = []
concat (x ∷ xs) = x ++ concat xs

data All {A : Set} (P : A → Set) : List A → Set where
  [] : All P []
  _∷_ : {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

record _↔_ (A : Set) (B : Set) : Set where
  field
    to : A → B
    from : B → A
open _↔_

-- we could go further and demand that these two functions really form a bijection,
-- but that is not necessary in our case.

↔refl : {A : Set} → A ↔ A
↔refl = record { to = λ x → x ; from = λ x → x }

↔sym : {A B : Set} → A ↔ B → B ↔ A
↔sym x = record { to = x .from ; from = x .to }

↔Dec : {A B : Set} → (A ↔ B) → Dec B → Dec A
↔Dec f (yes x) = yes (from f x)
↔Dec f (no ¬x) = no (λ x → ¬x (to f x))

List? : {A : Set} → Dec (List A)
List? = yes []

--------------------------------------------------------------------------------
-- Languages
--------------------------------------------------------------------------------

Lang : Set₁
Lang = String → Set

variable L : Lang

ν : Lang → Set
ν f = f []

δ : Symbol → Lang → Lang
δ c f w = f (c ∷ w)

-- Pre-grammars

data PreGram (n : Nat) : Set₁ where
  ∅ ε : PreGram n
  ‵_ : Symbol → PreGram n
  _∪_ _▸_ : PreGram n → PreGram n → PreGram n
  _·_ : Set → PreGram n → PreGram n
  _⋆ : PreGram n → PreGram n
  var : Fin n → PreGram n

⟦_⟧ : PreGram n → (Fin n → Lang) → Lang
⟦ ∅ ⟧ Γ _ = ⊥
⟦ ε ⟧ Γ w = w ≡ []
⟦ ‵ c ⟧ Γ w = w ≡ (c ∷ [])
⟦ A ∪ B ⟧ Γ w = ⟦ A ⟧ Γ w ⊎ ⟦ B ⟧ Γ w
⟦ A ▸ B ⟧ Γ w = Σ String λ u → Σ String λ v → (w ≡ (u ++ v)) × (⟦ A ⟧ Γ u × ⟦ B ⟧ Γ v)
⟦ A · B ⟧ Γ w = A × ⟦ B ⟧ Γ w
⟦ A ⋆ ⟧ Γ w = Σ (List String) λ xs → (w ≡ concat xs) × All (⟦ A ⟧ Γ) xs
⟦ var i ⟧ Γ w = Γ i w

preν : PreGram n → (Fin n → Set) → Set
preν ∅ _ = ⊥
preν ε _ = ⊤
preν (‵ x) _ = ⊥
preν (φ ∪ ψ) Γ = preν φ Γ ⊎ preν ψ Γ
preν (φ ▸ ψ) Γ = preν φ Γ × preν ψ Γ
preν (x · φ) Γ = x × preν φ Γ
preν (φ ⋆) Γ = List (preν φ Γ)
preν (var i) Γ = Γ i

preν↔ν : (φ : PreGram n) {Γ : Fin n → Lang} → preν φ (λ i → ν (Γ i)) ↔ ν (⟦ φ ⟧ Γ)
to (preν↔ν ∅) ()
from (preν↔ν ∅) ()
to (preν↔ν ε) _ = refl
from (preν↔ν ε) _ = tt
to (preν↔ν (‵ _)) ()
from (preν↔ν (‵ _)) ()
to (preν↔ν (φ ∪ ψ)) (inl x) = inl (to (preν↔ν φ) x)
to (preν↔ν (φ ∪ ψ)) (inr x) = inr (to (preν↔ν ψ) x)
from (preν↔ν (φ ∪ ψ)) (inl x) = inl (from (preν↔ν φ) x)
from (preν↔ν (φ ∪ ψ)) (inr x) = inr (from (preν↔ν ψ) x)
to (preν↔ν (φ ▸ ψ)) (x , y) = [] , [] , refl , to (preν↔ν φ) x , to (preν↔ν ψ) y
from (preν↔ν (φ ▸ ψ)) ([] , [] , refl , x , y) = from (preν↔ν φ) x , from (preν↔ν ψ) y
to (preν↔ν (x · φ)) (π₁ , π₂) = π₁ , to (preν↔ν φ) π₂
from (preν↔ν (x · φ)) (π₁ , π₂) = π₁ , from (preν↔ν φ) π₂
to (preν↔ν (φ ⋆)) [] = [] , refl , []
to (preν↔ν (φ ⋆)) (_ ∷ xs) = to (preν↔ν (φ ⋆)) xs
from (preν↔ν (φ ⋆)) _ = []
to (preν↔ν (var i)) x = x
from (preν↔ν (var i)) x = x

preδ : Symbol → PreGram n → (Fin n → Set) → (Fin n → PreGram n) → PreGram n
preδ c ∅ _ _ = ∅
preδ c ε _ _ = ∅
preδ c (‵ x) _ _ with c ≟ x
... | yes _ = ε
... | no _ = ∅
preδ c (φ ∪ ψ) Γν Γδ = preδ c φ Γν Γδ ∪ preδ c ψ Γν Γδ
preδ c (φ ▸ ψ) Γν Γδ = (preδ c φ Γν Γδ ▸ ψ) ∪ (preν φ Γν · preδ c ψ Γν Γδ)
preδ c (x · φ) Γν Γδ = x · preδ c φ Γν Γδ
preδ c (φ ⋆) Γν Γδ = preδ c φ Γν Γδ ▸ (φ ⋆)
preδ c (var i) Γν Γδ = Γδ i

_⇔_ : Lang → Lang → Set
P ⇔ Q = (w : String) → P w ↔ Q w

preδ↔δ : (φ : PreGram n) (c : Symbol) {ΓL : Fin n → Lang} {Γδ : Fin n → PreGram n} 
  → ((i : Fin n) → ⟦ Γδ i ⟧ ΓL ⇔ δ c (ΓL i))
  → ⟦ preδ c φ (λ i → ν (ΓL i)) Γδ ⟧ ΓL ⇔ δ c (⟦ φ ⟧ ΓL)
to (preδ↔δ ∅ c Γ w) ()
from (preδ↔δ ∅ c Γ w) ()
to (preδ↔δ ε c Γ w) ()
from (preδ↔δ ε c Γ w) ()
to (preδ↔δ (‵ x) c Γ w) y with c ≟ x
to (preδ↔δ (‵ x) .x Γ .[]) refl | yes refl = refl
to (preδ↔δ (‵ x) c Γ w) () | no ¬x≡c
from (preδ↔δ (‵ x) c Γ w) y with c ≟ x
from (preδ↔δ (‵ x) .x Γ .[]) refl | yes refl = refl
from (preδ↔δ (‵ x) .x Γ .[]) refl | no ¬x≡c = ¬x≡c refl
to (preδ↔δ (φ ∪ ψ) c Γ w) (inl x) = inl (to (preδ↔δ φ c Γ w) x)
to (preδ↔δ (φ ∪ ψ) c Γ w) (inr x) = inr (to (preδ↔δ ψ c Γ w) x)
from (preδ↔δ (φ ∪ ψ) c Γ w) (inl x) = inl (from (preδ↔δ φ c Γ w) x)
from (preδ↔δ (φ ∪ ψ) c Γ w) (inr x) = inr (from (preδ↔δ ψ c Γ w) x)
to (preδ↔δ (φ ▸ ψ) c Γ w) (inl (u , v , refl , x , y)) = (c ∷ u) , v , refl , to (preδ↔δ φ c Γ u) x , y
to (preδ↔δ (φ ▸ ψ) c Γ w) (inr (x , y)) = [] , (c ∷ w) , refl , to (preν↔ν φ) x , to (preδ↔δ ψ c Γ w) y
from (preδ↔δ (φ ▸ ψ) c Γ w) ([] , (.c ∷ v) , refl , x , y) = inr (from (preν↔ν φ) x , from (preδ↔δ ψ c Γ w) y)
from (preδ↔δ (φ ▸ ψ) c Γ w) ((.c ∷ u) , v , refl , x , y) = inl (u , v , refl , from (preδ↔δ φ c Γ u) x , y)
to (preδ↔δ (x · φ) c Γ w) (π₁ , π₂) = π₁ , to (preδ↔δ φ c Γ w) π₂
from (preδ↔δ (x · φ) c Γ w) (π₁ , π₂) = π₁ , from (preδ↔δ φ c Γ w) π₂
to (preδ↔δ (φ ⋆) c Γ .(u ++ concat xs)) (u , .(concat xs) , refl , x , xs , refl , y) = ((c ∷ u) ∷ xs) , refl , (to (preδ↔δ φ c Γ u) x ∷ y)
from (preδ↔δ (φ ⋆) c Γ .(x ++ concat xs)) (((.c ∷ x) ∷ xs) , refl , (x₁ ∷ y)) = x , concat xs , refl , from (preδ↔δ φ c Γ x) x₁ , xs , refl , y
from (preδ↔δ (φ ⋆) c Γ w) (([] ∷ xs) , pf , (x ∷ y)) = from (preδ↔δ (φ ⋆) c Γ w) (xs , pf , y)
preδ↔δ (var i) c Γ w = Γ i w

--------------------------------------------------------------------------------
-- Decidable grammars
--------------------------------------------------------------------------------

data Gram (n : Nat) : (PreGram n) → Set₁ where
  ∅ : Gram n ∅
  ε : Gram n ε
  ‵_ : (c : Symbol) → Gram n (‵ c)
  _∪_ : {φ ψ : PreGram n} → Gram n φ → Gram n ψ → Gram n (φ ∪ ψ)
  _▸_ : {φ ψ : PreGram n} → Gram n φ → Gram n ψ → Gram n (φ ▸ ψ)
  _·_ : {A : Set} {φ : PreGram n} → Dec A → Gram n φ → Gram n (A · φ)
  _⋆ : {φ : PreGram n} → Gram n φ → Gram n (φ ⋆)
  var : (i : Fin n) → Gram n (var i) 

pre : {φ : PreGram n} → Gram n φ → PreGram n
pre {φ = φ} _ = φ

⟦_⟧′ : {φ : PreGram n} → Gram n φ → (Fin n → Lang) → Lang
⟦ G ⟧′ = ⟦ pre G ⟧

ν? : {φ : PreGram n} {Γν : Fin n → Set} 
  (P : Gram n φ)
  (Γ : (i : Fin n) → Dec (Γν i))
  → Dec (preν φ Γν)
ν? ∅ _ = no λ ()
ν? ε _ = yes tt
ν? (‵ c) _ = no λ ()
ν? (P ∪ Q) Γ = ν? P Γ ⊎? ν? Q Γ
ν? (P ▸ Q) Γ = ν? P Γ ×? ν? Q Γ
ν? (x · P) Γ = x ×? ν? P Γ
ν? (P ⋆) _ = yes []
ν? (var i) Γ = Γ i

δ? : {φ : PreGram n} {Γν : Fin n → Set} {Γδ : Fin n → PreGram n} 
  (c : Symbol) 
  → Gram n φ 
  → ((i : Fin n) → Dec (Γν i))
  → ((i : Fin n) → Gram n (Γδ i))
  → Gram n (preδ c φ Γν Γδ)
δ? c ∅ _ _ = ∅
δ? c ε _ _ = ∅
δ? c (‵ x) _ _ with c ≟ x
... | yes _ = ε
... | no _ = ∅
δ? c (x ∪ x₁) Γν Γδ = δ? c x Γν Γδ ∪ δ? c x₁ Γν Γδ
δ? c (x ▸ y) Γν Γδ = (δ? c x Γν Γδ ▸ y) ∪ (ν? x Γν · δ? c y Γν Γδ)
δ? c (x · x₁) Γν Γδ = x · δ? c x₁ Γν Γδ
δ? c (x ⋆) Γν Γδ = δ? c x Γν Γδ ▸ (x ⋆)
δ? c (var i) Γν Γδ = Γδ i



ν?₀ : {φ : PreGram zero} (P : Gram zero φ) → Dec (preν φ (λ ()))
ν?₀ P = ν? P λ ()

δ?₀ : {φ : PreGram zero} (c : Symbol) → Gram zero φ → Gram zero (preδ c φ (λ ()) (λ ()))
δ?₀ c P = δ? c P (λ ()) (λ ())

parse : {φ : PreGram zero} → (w : String) → Gram zero φ → Dec (⟦ φ ⟧ (λ ()) w)
parse {φ = φ} [] x = ↔Dec (↔sym (preν↔ν φ)) (ν?₀ x)
parse {φ = φ} (c ∷ w) x = ↔Dec (↔sym (preδ↔δ φ c (λ ()) w)) (parse w (δ?₀ c x))
