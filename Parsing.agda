-- {-# OPTIONS --safe #-}
module Parsing  where

data Symbol : Set where
  `+ : Symbol
  `x : Symbol

open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.Nat hiding (_-_)
open import Level using (Level ; _⊔_) renaming (suc to lsuc)

String : Set
String = List Symbol

Language : Set₁
Language = String → Set

infixr 9 _++_
_++_ : ∀ {A : Set} (xs ys : List A) → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

private variable n : Nat

data Fin : Nat → Set where
  zero : Fin (suc n)
  suc  : Fin n → Fin (suc n)

data _⊎_ {ℓ₁ ℓ₂ : Level} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

infixr 8 _×_
record _×_ {ℓ₁ ℓ₂ : Level} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field
    fst : A
    snd : B

data Option (A : Set) : Set where
  none : Option A
  some : A → Option A

data Grammar (n : Nat) : Set₁ where
  ∅ ε          : Grammar n
  char         : Symbol → Grammar n
  _∪_ _∩_ _∙_  : (_ _ : Grammar n) → Grammar n
  _·_          : Set → Grammar n → Grammar n
  var          : Fin n → Grammar n
  fix          : Grammar (suc n) → Grammar n

data ⊥ : Set where

⊥-elim : ∀ {ℓ} {A : Set ℓ} → ⊥ → A
⊥-elim ()

_∘_ : ∀{ℓ : Level} {A B C : Set ℓ} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

data EnvSlice (n : Nat) : Nat → Set₁ where
  []  : EnvSlice n n
  _∷_ : {m : Nat} → Grammar m → EnvSlice n m → EnvSlice n (suc m)

Env : Nat → Set₁
Env n = EnvSlice zero n

_+++_ : {n m : Nat} → EnvSlice n m → Env n → Env m
[] +++ e₂ = e₂
(x ∷ e₁) +++ e₂ = x ∷ (e₁ +++ e₂)

data _≼_ : {n m : Nat} → Env n → Env m → Set₁ where
  e≼e : {m : Nat} {e : Env m} → e ≼ e 
  ≼∷ : {n m : Nat} {e : Env n} {e′ : Env m} {G : Grammar m} → e ≼ e′ → e ≼ (G ∷ e′)

data Dec (A : Set) : Set where
  yes : A → Dec A
  no : (A → ⊥) → Dec A

_≟_ : (x y : Symbol) → Dec (x ≡ y)
`+ ≟ `+ = yes refl
`+ ≟ `x = no λ ()
`x ≟ `+ = no λ ()
`x ≟ `x = yes refl

Decidable : {A : Set} → (P : A → Set) → Set
Decidable {A = A} P = {x : A} → Dec (P x)

lookup : Env n → Fin n → Language

⟦_⟧ : Grammar n → Env n → Language

lookup (g ∷ e) zero = ⟦ g ⟧ e
lookup (g ∷ e) (suc k) = lookup e k

data Fix (G : Grammar (suc n)) (e : Env n) : Language where
    step : {w : String} → ⟦ G ⟧ (fix G ∷ e) w → Fix G e w

⟦ ∅      ⟧ _ _ = ⊥
⟦ ε      ⟧ _ w = w ≡ []
⟦ char x ⟧ _ w = w ≡ (x ∷ [])
⟦ A ∪ B  ⟧ e w = ⟦ A ⟧ e w ⊎ ⟦ B ⟧ e w
⟦ A ∩ B  ⟧ e w = ⟦ A ⟧ e w × ⟦ B ⟧ e w
⟦ A ∙ B  ⟧ e w = Σ (String × String) λ (u , v) → (w ≡ (u ++ v)) × (⟦ A ⟧ e u × ⟦ B ⟧ e v) 
⟦ A · G  ⟧ e w = Dec A × ⟦ G ⟧ e w
⟦ var k  ⟧ e w = (lookup e k) w
⟦ fix G  ⟧ e w = (Fix G e) w

mape : {n m : Nat} {e₁ : EnvSlice (suc n) m} {e₂ : Env n} {G₁ G₂ : Grammar n} (G : Grammar m)
    → (⟦ G₁ ⟧ e₂ [] → ⟦ G₂ ⟧ e₂ [])
    → ⟦ G ⟧ (e₁ +++ (G₁ ∷ e₂)) [] → ⟦ G ⟧ (e₁ +++ (G₂ ∷ e₂)) []
mape (char c) _ x = x
mape ε _ x = x
mape (G ∪ G₁) f (inl x) = inl (mape G f x)
mape (G ∪ G₁) f (inr x) = inr (mape G₁ f x)
mape (G ∩ G₁) f (x , y) = mape G f x , mape G₁ f y
mape (G ∙ G₁) f (([] , []) , (refl , (x , y))) = ([] , []) , (refl , (mape G f x , mape G₁ f y))
mape {e₁ = []} (var zero) f x = f x
mape (A · G) f (s , x) = s , mape G f x
mape {e₁ = G ∷ e₁} (var zero) f x = mape {e₁ = e₁} G f x
mape {e₁ = []} (var (suc j)) f x = x
mape {e₁ = _ ∷ e₁} (var (suc j)) f x = mape {e₁ = e₁} (var j) f x
mape {e₁ = e₁} (fix G) f (step x) = step (mape {e₁ = fix G ∷ e₁} G f x)

foo : {n m : Nat} (G : Grammar n) (G′ : Grammar (suc m)) {G″ : Grammar m} (e : EnvSlice (suc m) n) {e′ : Env m}
    → (⟦ G ⟧ (e +++ (G″ ∷ e′)) [] → ⟦ G′ ⟧ (G″ ∷ e′) [])
    → ⟦ G ⟧ (e +++ (fix G′ ∷ e′)) [] → ⟦ G′ ⟧ (G″ ∷ e′) []
foo ε             G′ e₁        k x = k refl
foo (G ∪ G₁)      G′ e₁        k (inl x) = foo G G′ e₁ (k ∘ inl) x
foo (G ∪ G₁)      G′ e₁        k (inr x) = foo G₁ G′ e₁ (k ∘ inr) x
foo (G ∩ G₁)      G′ e₁        k (x , y) = foo G G′ e₁ (λ x′ → foo G₁ G′ e₁ (λ y′ → k (x′ , y′)) y) x
foo (G ∙ G₁)      G′ e₁        k (([] , []) , (refl , (x , y))) = foo G G′ e₁ (λ x′ → foo G₁ G′ e₁ (λ y′ → k (([] , []) , (refl , (x′ , y′)))) y) x
foo (A · G)       G′ e₁        k (s , x) = foo G G′ e₁ (λ z → k (s , z)) x
foo (var zero)    G′ []        k (step x) = foo G′ G′ [] (λ z → z) x
foo (var zero)    G′ (G ∷ e₁)  k x = foo G G′ e₁ k x
foo (var (suc i)) G′ []        k x = k x
foo (var (suc i)) G′ (_ ∷ e₁)  k x = foo (var i) G′ e₁ k x
foo (fix G)       G′ e₁        k (step x) = foo G G′ (fix G ∷ e₁) (k ∘ step) x

record _↔_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
    to∘from : (x : B) → to (from x) ≡ x
    from∘to : (x : A) → from (to x) ≡ x
open _↔_

↔refl : (A : Set) → A ↔ A
to (↔refl _) x = x
from (↔refl _) x = x
to∘from (↔refl _) _ = refl
from∘to (↔refl _) _ = refl

from∅ : {G : Grammar (suc zero)} → ⟦ G ⟧ (∅ ∷ []) [] → ⟦ fix G ⟧ [] []
from∅ {G = G} x = step (mape {e₁ = []} G (λ ()) x)

to∅ : {G : Grammar (suc zero)} → ⟦ fix G ⟧ [] [] → ⟦ G ⟧ (∅ ∷ []) []
to∅ {G = G} (step x) = foo G G [] (λ z → z) x

data Vec {ℓ : Level} (A : Set ℓ) : Nat → Set ℓ where
  [] : Vec A 0
  _∷_ : A → Vec A n → Vec A (suc n)

ν : Language → Set
ν f = f []

δ : Language → Symbol → Language
δ f s = λ w → f (s ∷ w) 

data ⊤ : Set where
  tt : ⊤

data νe : Env n → Set₁ where
    [] : νe []
    _∷_ : {G : Grammar n} {e : Env n} → Dec (ν (⟦ G ⟧ e)) → νe e → νe (G ∷ e)

ν? : (G : Grammar n) → {e : Env n} → νe e → Dec (ν (⟦ G ⟧ e))
ν? ∅ {e} _ = no λ ()
ν? ε _ = yes refl
ν? (char x) _ = no (λ ())
ν? (G ∪ G₁) e with ν? G e | ν? G₁ e
... | yes x | _ = yes (inl x)
... | no _ | yes y = yes (inr y)
... | no ¬x | no ¬y = no λ { (inl x) → ¬x x ; (inr y) → ¬y y }
ν? (G ∩ G₁) e with ν? G e | ν? G₁ e
... | yes x | yes y = yes (x , y)
... | no ¬x | _ = no (λ (x , _) → ¬x x)
... | yes _ | no ¬x = no (λ (_ , x) → ¬x x)
ν? (G ∙ G₁) e with ν? G e | ν? G₁ e
... | yes x | yes y = yes (([] , []) , (refl , (x , y)))
... | yes _ | no ¬y = no λ { (([] , []) , (refl , (_ , y))) → ¬y y }
... | no ¬x | _ = no λ { (([] , []) , (refl , (x , _))) → ¬x x } 
ν? (A · G) e with ν? G e
... | yes x = yes ({!!} , x)
... | no ¬x = {!!}
ν? (var zero) (x ∷ _) = x
ν? (var (suc i)) (_ ∷ x) = ν? (var i) x
ν? (fix G) {e = e} x with ν? G {e = ∅ ∷ e} (no (λ ()) ∷ x)
... | yes x = yes (step (mape {e₁ = []} G (λ ()) x))
... | no ¬x = no λ { (step x) → ¬x (foo G G [] {e′ = e} (λ z → z) x) }

cong : {A B : Set} {x y : A} (P : A → B) → x ≡ y → P x ≡ P y
cong _ refl = refl

cong₂ : {A B C : Set} {x y : A} {x′ y′ : B} (P : A → B → C) → x ≡ y → x′ ≡ y′ → P x x′ ≡ P y y′
cong₂ _ refl refl = refl

↔⊎ : {A A′ B B′ : Set} → A ↔ A′ → B ↔ B′ → (A ⊎ B) ↔ (A′ ⊎ B′)
to (↔⊎ l r) (inl x) = inl (to l x) 
to (↔⊎ l r) (inr x) = inr (to r x)
from (↔⊎ l r) (inl x) = inl (from l x)
from (↔⊎ l r) (inr x) = inr (from r x)
to∘from (↔⊎ l r) (inl x) = cong inl (to∘from l x)
to∘from (↔⊎ l r) (inr x) = cong inr (to∘from r x)
from∘to (↔⊎ l r) (inl x) = cong inl (from∘to l x)
from∘to (↔⊎ l r) (inr x) = cong inr (from∘to r x)

↔× : {A A′ B B′ : Set} → A ↔ A′ → B ↔ B′ → (A × B) ↔ (A′ × B′)
to (↔× ↔₁ ↔₂) (x , y) = to ↔₁ x , to ↔₂ y
from (↔× ↔₁ ↔₂) (x , y) = from ↔₁ x , from ↔₂ y
to∘from (↔× ↔₁ ↔₂) (x , y) = cong₂ _,_ (to∘from ↔₁ x) (to∘from ↔₂ y)
from∘to (↔× ↔₁ ↔₂) (x , y) = cong₂ _,_ (from∘to ↔₁ x) (from∘to ↔₂ y)

δ? : (G : Grammar zero) → (s : Symbol) → Σ (Grammar zero) λ G′ → {w : String} → δ (⟦ G ⟧ []) s w ↔ ⟦ G ⟧ [] w
δ? = {!!}

-- 𝒢 : {n : Nat} → Grammar n → Env n → Symbol → Set
-- 𝒢 {n} G e s = Σ (Grammar n) λ G′ → (w : String) → δ (⟦ G ⟧ e) s w ↔ ⟦ G′ ⟧ e w
-- 
-- δ? : (G : Grammar n) (e : Env n) → (s : Symbol) → Vec (𝒢 G e s) n → 𝒢 G e s
-- δ? ∅ e s de = ∅ , λ _ → ↔refl ⊥
-- δ? ε e s de = ∅ , λ _ → record { to = λ () ; from = λ () ; to∘from = λ () ; from∘to = λ () }
-- δ? (char c) e s de with c ≟ s
-- ... | yes refl = ε , λ where
--   [] → record { to = λ { refl → refl } ; from = λ { refl → refl } ; to∘from = λ { refl → refl } ; from∘to = λ { refl → refl } }
--   (_ ∷ _) → record { to = λ () ; from = λ () ; to∘from = λ () ; from∘to = λ () }
-- ... | no ¬x = ∅ , λ _ → record { to = λ { refl → ¬x refl } ; from = λ () ; to∘from = λ () ; from∘to = λ { refl → ⊥-elim (¬x refl) } }
-- δ? (G₁ ∪ G₂) e s de with δ? G₁ e s de | δ? G₂ e s de
-- ... | G₁′ , l | G₂′ , r = G₁′ ∪ G₂′ , λ w → ↔⊎ (l w) (r w)
-- δ? (G₁ ∩ G₂) e s de with δ? G₁ e s de | δ? G₂ e s de
-- ... | G₁′ , l | G₂′ , r = G₁′ ∩ G₂′ , λ w → ↔× (l w) (r w)
-- δ? (G₁ ∙ G₂) e s de with δ? G₁ e s de | δ? G₂ e s de
-- ... | G₁′ , l | G₂′ , r = ((ε ∩ G₁) ∙ G₂′) ∪ (G₁′ ∙ G₂) , λ w → record
--   { to = λ where
--     (([] , v) , (refl , (x , y))) → inl (([] , w) , refl , ((refl , x) , to (r w) y))
--     (((.s ∷ u) , v) , (refl , (x , y))) → inr ((u , v) , (refl , (to (l u) x , y)))
--   ; from = λ where
--     (inl (([] , .w) , (refl , ((refl , x) , y)))) → ([] , s ∷ w) , (refl , (x , from (r w) y))
--     (inl (((_ ∷ _) , _) , (refl , ((() , _) , _))))
--     (inr ((u , v) , (refl , (x , y)))) → (s ∷ u , v) , (refl , (from (l u) x , y))
--   ; to∘from = λ where
--     (inl (([] , .w) , (refl , ((refl , x) , y)))) → cong (λ X → inl (([] , w) , (refl , ((refl , x) , X)))) (to∘from (r w) y)
--     (inr ((u , v) , (refl , (x , y)))) → cong (λ X → inr ((u , v) , (refl , (X , y)))) (to∘from (l u) x)
--   ; from∘to = λ where
--     (([] , .(s ∷ w)) , (refl , (x , y))) → cong (λ X → (([] , s ∷ w) , (refl , (x , X)))) (from∘to (r w) y)
--     (((.s ∷ u) , v) , (refl , (x , y))) → cong (λ X → ((s ∷ u , v) , (refl , (X , y)))) (from∘to (l u) x)
--   }
-- δ? (var zero) e (x ∷ de) s = {!!}
-- δ? (var (suc i)) (_ ∷ e) (x ∷ de) s = {!δ? (var i) e de s!}
-- δ? (fix G) e de s with δ? G (fix G ∷ e) ({!var zero!} ∷ de) s
-- ... | G′ , pf = fix G′ , {!!}
-- 
-- ⟦_⟧? : (G : Grammar zero) → Decidable (⟦ G ⟧ [])
-- ⟦ G ⟧? {[]} = ν? G tt
-- ⟦ G ⟧? {s ∷ w} with δ? G [] [] s
-- ... | G′ , ↔ with ⟦ G′ ⟧? {w}
-- ... | yes x = yes (from (↔ w) x)
-- ... | no ¬x = no (¬x ∘ to (↔ w))

--     fixzero : {w : String} → Fix (var zero) [] w → ⊥
--     fixzero (step x) = fixzero x
-- 
--     from∘to : {G : Grammar (suc zero)} {x : ⟦ fix G ⟧ [] []} → from (to x) ≡ x
--     from∘to {∅} {step ()}
--     from∘to {ε} {step refl} = refl
--     from∘to {char c} {step ()}
--     from∘to {G ∪ G₁} {step (inl x)} = cong step {!!}
--     from∘to {G ∪ G₁} {step (inr x)} = cong step {!!}
--     from∘to {G ∩ G₁} {step (x , y)} = cong step {!!}
--     from∘to {G ∙ G₁} {step (([] , []) , (refl , (x , y)))} = cong step {!!}
--     from∘to {var zero} {x} = ⊥-elim (fixzero x)
--     from∘to {fix G} {step (step x)} = cong step {!!}
-- 
--     trans : {A : Set} {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
--     trans refl refl = refl
-- 
--     postulate
--       funext : {A B : Set} {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g
--       funext′ : {A B : Set} {f g : {A} → B} → ({x : A} → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})
-- 
--     data All {ℓ : Level} {A : Set} (P : A → Set ℓ) : List A → Set (lsuc ℓ) where
--       [] : All P []
--       _∷_ : {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)
-- 
--     data ZipWith {ℓ₁ ℓ₂ : Level} {A : Set} {P : A → Set ℓ₁} {Q : A → Set ℓ₂} (f : {x : A} → P x → Q x → Set) : {xs : List A} → All P xs → All Q xs → Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
--       [] : ZipWith f [] [] 
--       _∷_ : ∀{x y z xs ys zs} → f {x} y z → ZipWith f {xs = xs} ys zs → ZipWith f (y ∷ ys) (z ∷ zs) 
-- 
--     foldr₂ : {ℓ : Level} {A B : Set} {X : Set ℓ} → (A → B → X → X) → X → List A → List B → X
--     foldr₂ = {!!}
-- 
--     dfoldr : {ℓ : Level} {A : Set} {P : A → Set} {X : Set ℓ} {xs : List A} → ({x : A} → P x → X → X) → X → All P xs → X
--     dfoldr c n [] = n
--     dfoldr c n (x ∷ xs) = c x (dfoldr c n xs)
-- 
--     dfoldr₂ : {ℓ ℓ₁ ℓ₂ : Level} {A : Set} {P : A → Set ℓ₁} {Q : A → Set ℓ₂} {X : Set ℓ} {xs : List A} → ({x : A} → P x → Q x → X → X) → X → All P xs → All Q xs → X
--     dfoldr₂ c n [] [] = n
--     dfoldr₂ c n (y ∷ ys) (z ∷ zs) = c y z (dfoldr₂ c n ys zs)
-- 
--     tfhelper : {n : Nat} (G : Grammar (suc n)) {G′ : Grammar (suc zero)} {e₁ : EnvSlice (suc zero) (suc n)}
--       {x : ⟦ G ⟧ (e₁ +++ (∅ ∷ [])) []}
--       (f : {G″ : Grammar zero} → ⟦ G ⟧ (e₁ +++ (G″ ∷ [])) [] → ⟦ G′ ⟧ (G″ ∷ []) [])
--       → foo G G′ e₁ f (mape {e₁ = e₁} G (λ ()) x) ≡ f x
-- 
--     tfhelpers : {ns : List Nat} (Gs : All (λ n → Grammar (suc n)) ns) {G′ : Grammar (suc zero)}
--       {es : All (λ n → EnvSlice (suc zero) (suc n)) ns}
--       {xs : ZipWith (λ G e → ⟦ G ⟧ (e +++ (∅ ∷ [])) []) Gs es}
--       (f : {G″ : Grammar zero} → ZipWith (λ G e → ⟦ G ⟧ (e +++ (G″ ∷ [])) []) Gs es → ⟦ G′ ⟧ (G″ ∷ []) [])
--       → dfoldr₂ {X = {!ZipWith (λ G e → ⟦ G ⟧ (e +++ (G″ ∷ [])) []) Gs es → _!}} (λ G e r xs′ → foo G G′ e (λ x′ → r ({!x′!} ∷ xs′)) (mape {e₁ = e} G (λ ()) {!!})) {!!} Gs es (λ x → x) ≡ {!!}
--       -- foo G₁ G′ e₁ (λ x′ → foo G₂ G′ e₂ (λ y′ → f x′ y′) (mape {e₁ = e₂} G₂ (λ ()) y)) (mape {e₁ = e₁} G₁ (λ ()) x) ≡ f x y
--     tfhelpers = {!!}
-- 
--     -- tfhelper₂ : {n m : Nat} (G₁ : Grammar (suc n)) (G₂ : Grammar (suc m)) {G′ : Grammar (suc zero)}
--     --   {e₁ : EnvSlice (suc zero) (suc n)} {e₂ : EnvSlice (suc zero) (suc m)}
--     --   {x : ⟦ G₁ ⟧ (e₁ +++ (∅ ∷ [])) []} {y : ⟦ G₂ ⟧ (e₂ +++ (∅ ∷ [])) []}
--     --   (f : {G″ : Grammar zero} → ⟦ G₁ ⟧ (e₁ +++ (G″ ∷ [])) [] → ⟦ G₂ ⟧ (e₂ +++ (G″ ∷ [])) [] → ⟦ G′ ⟧ (G″ ∷ []) [])
--     --   → foo G₁ G′ e₁ (λ x′ → foo G₂ G′ e₂ (λ y′ → f x′ y′) (mape {e₁ = e₂} G₂ (λ ()) y)) (mape {e₁ = e₁} G₁ (λ ()) x) ≡ f x y
--     -- tfhelper₂ ε G₂ {x = refl} f = tfhelper G₂ (f refl)
--     -- tfhelper₂ (G₁ ∪ G₃) G₂ {x = inl x} f = tfhelper₂ G₁ G₂ {x = x} (λ x y → f (inl x) y)
--     -- tfhelper₂ (G₁ ∪ G₃) G₂ {x = inr x} f = tfhelper₂ G₃ G₂ {x = x} (λ x y → f (inr x) y)
--     -- tfhelper₂ (G₁ ∩ G₃) G₂ {G′} {e₁} {x = x , y} f = trans (cong (λ X → foo G₁ G′ e₁ X (mape G₁ (λ ()) x)) (funext λ x → {!tfhelper₂ G₃ G₂ (λ {G″} y z → f (mape {G₂ = G″} G₁ (λ ()) x , y) z)!})) {!!}
--     -- tfhelper₂ (G₁ ∙ G₃) G₂ {x = ([] , []) , (refl , (x , y))} f = {!!}
--     -- tfhelper₂ {suc n} (var zero) G₂ {e₁ = G ∷ e₁} f = tfhelper₂ G G₂ f
--     -- tfhelper₂ {zero} (var zero) G₂ {e₁ = G ∷ ()} _
--     -- tfhelper₂ {suc n} (var (suc i)) G₂ {G′} {e₁ = _ ∷ e₁} {y = y} f = tfhelper₂ {n} (var i) G₂ {e₁ = e₁} f
--     -- tfhelper₂ (fix G₁) G₂ {x = step x} f = tfhelper₂ G₁ G₂ (λ x y → f (step x) y)
-- 
--     tfhelper ε {x = refl} f = refl
--     tfhelper (G ∪ G₁) {x = inl x} f = tfhelper G {x = x} (f ∘ inl)
--     tfhelper (G ∪ G₁) {x = inr x} f = tfhelper G₁ {x = x} (f ∘ inr)
--     tfhelper (G ∩ G₁) {G′ = G′} {e₁ = e₁} {x = x , y} f = {!!}
--     -- trans
--     --   (cong {A = {G″ : Grammar zero} → _} (λ X → foo G G′ e₁ X (mape G (λ ()) x)) {!funext λ x′ → tfhelper G₁ {G′} {e₁} {y} (λ y′ → f (x′ , y′))!})
--     --   (tfhelper G {G′} {e₁} {x} λ x′ → f (x′ , {!!}))
--     -- {!tfhelper₂ G G₁ {x = x} {y = y} (λ x y → f (x , y))!}
--     tfhelper (G ∙ G₁) {x = ([] , []) , (refl , (x , y))} f = {!tfhelper₂ G G₁ {x = x} {y = y} (λ x y → f (([] , []) , (refl , (x , y))))!}
--     tfhelper {suc n} (var zero) {e₁ = G ∷ e₁} {x = x} f = tfhelper G f
--     tfhelper {zero} (var zero) {e₁ = G ∷ ()} _
--     tfhelper {suc n} (var (suc i)) {e₁ = _ ∷ e₁} f = tfhelper {n} (var i) {e₁ = e₁} f
--     tfhelper (fix G) {x = step x} f = tfhelper G (f ∘ step)
-- 
--     to∘from : {G : Grammar (suc zero)} {x : ⟦ G ⟧ (∅ ∷ []) []} → to {G = G} (from x) ≡ x
--     to∘from {G = G} = tfhelper G (λ z → z)

{- -- alternatively, with the --polarity flag

{-# OPTIONS --polarity #-}

char : Symbol → Language
char x w = w ≡ (x ∷ [])

data _⊎_ (@++ A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

infixr 8 _×_
infixr 7 _,_
record _×_ (@++ A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

record Σ (@++ A : Set) (@++ B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

_∪_ : @++ Language → @++ Language → Language
(A ∪ B) w = A w ⊎ B w

infixr 7 _∙_
_∙_ : @++ Language → @++ Language → Language
(A ∙ B) w = Σ (_ × _) λ (xs , ys) → (w ≡ xs ++ ys) × A xs × B ys

data fix (f : @++ Language → Language) : Language where
  step : ∀ {w} → f (fix f) w → fix f w

exp : Language
exp = fix λ X → (X ∙ char `+  ∙ X) ∪ char `x

_ : exp (`x ∷ `+ ∷ `x ∷ `+ ∷ `x ∷ [])
_ = step (inl (((`x ∷ []) , _)
               , (refl , step (inr refl) , ((`+ ∷ []) , _) , refl
               , refl , (step (inl (((`x ∷ []) , _) , refl
               , step (inr refl) , ((`+ ∷ []) , _) , (refl , (refl
               , (step (inr refl))))))))))

-}

