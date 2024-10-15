{-# OPTIONS --cubical --guarded #-}

module DDG3 where

open import Cubical.Foundations.Prelude hiding (_[_↦_])
open import Cubical.Foundations.Transport
open import Cubical.Data.Nat
open import Cubical.Data.Maybe
open import Cubical.Data.List
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Agda.Builtin.Unit
open import Cubical.Relation.Nullary.Base
open import Cubical.Foundations.Function
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.HLevels

--------------------------------------------------------------------------------
-- Vendored Guarded Prelude (trusted code, best skipped on first read):

module Prims where
  primitive
    primLockUniv : Set₁

open Prims renaming (primLockUniv to LockU) public

private
  variable
    l : Level
    A B : Set l

postulate
  Tick : LockU

▹_ : ∀ {l} → Set l → Set l
▹ A = (@tick x : Tick) -> A

map▹ : (A → B) → ▹ A → ▹ B
map▹ f x t = f (x t)

▸_ : ∀ {l} → ▹ Set l → Set l
▸ A = (@tick x : Tick) → A x

next : A → ▹ A
next x = λ _ → x

postulate
  dfix : ∀ {l} {A : Set l} → (▹ A → A) → ▹ A
  pfix : ∀ {l} {A : Set l} (f : ▹ A → A) → dfix f ≡ next (f (dfix f))

fix′ : ∀ {l} {A : Set l} → (▹ A → A) → A
fix′ f = f (dfix f)

-- End of trusted code
--------------------------------------------------------------------------------

pfix′ : ∀ {l} {A : Set l} (f : ▹ A → A) {@tick t : Tick} → dfix f t ≡ f (dfix f)
pfix′ f {t} i = pfix f i t

-- Cubical Agda does not like String and Char
data Tok : Set where
  TX : Tok
  T+ : Tok
  Tℕ : ℕ → Tok

¬TX≡T+ : ¬(TX ≡ T+)
¬TX≡T+ p = subst (λ where TX → Tok ; T+ → ⊥ ; (Tℕ _) → ⊥) p TX

¬TX≡Tℕ : ∀{n} → ¬(TX ≡ Tℕ n)
¬TX≡Tℕ p = subst (λ where TX → Tok ; T+ → ⊥ ; (Tℕ _) → ⊥) p TX

¬T+≡TX : ¬(T+ ≡ TX)
¬T+≡TX p = subst (λ where TX → ⊥ ; T+ → Tok ; (Tℕ _) → ⊥) p T+

¬T+≡Tℕ : ∀{n} → ¬(T+ ≡ Tℕ n)
¬T+≡Tℕ p = subst (λ where TX → ⊥ ; T+ → Tok ; (Tℕ _) → ⊥) p T+

¬Tℕ≡TX : ∀{n} → ¬(Tℕ n ≡ TX)
¬Tℕ≡TX {n} p = subst (λ where TX → ⊥ ; T+ → ⊥ ; (Tℕ _) → Tok) p (Tℕ n)

¬Tℕ≡T+ : ∀{n} → ¬(Tℕ n ≡ T+)
¬Tℕ≡T+ {n} p = subst (λ where TX → ⊥ ; T+ → ⊥ ; (Tℕ _) → Tok) p (Tℕ n)

Tℕ-inj : ∀{n m} → Tℕ n ≡ Tℕ m → n ≡ m
Tℕ-inj {n} = cong (λ where (Tℕ n) → n ; _ → n)

discreteTok : Discrete Tok
discreteTok TX TX = yes refl
discreteTok TX T+ = no ¬TX≡T+
discreteTok TX (Tℕ _) = no ¬TX≡Tℕ
discreteTok T+ TX = no ¬T+≡TX
discreteTok T+ T+ = yes refl
discreteTok T+ (Tℕ x) = no ¬T+≡Tℕ
discreteTok (Tℕ x) TX = no ¬Tℕ≡TX
discreteTok (Tℕ x) T+ = no ¬Tℕ≡T+
discreteTok (Tℕ x) (Tℕ y) with discreteℕ x y
... | yes x≡y = yes (cong Tℕ x≡y)
... | no ¬x≡y = no λ Tℕx≡Tℕy → ¬x≡y (Tℕ-inj Tℕx≡Tℕy)

Lang : Set₁
Lang = List Tok → Set

fix₀ : (Lang → Lang) → Lang
fix₀ f = fix′ λ x → f λ w → ▸ λ t → x t w

fix : ∀ {A : Set} → ((A → Lang) → A → Lang) → A → Lang
fix f = fix′ λ x → f λ y w → ▸ λ t → x t y w

then : ∀{l} {A : Set l} {f : ▹ (A → Lang) → A → Lang} {x w} → f (dfix f) x w → ▸ (λ t → dfix f t x w)
then {f = f} x _ = transport (sym (cong (λ x → x _ _) (pfix′ f))) x

ere : ∀{l} {A : Set l} {f : ▹ (A → Lang) → A → Lang} {x w} → ▸ (λ t → dfix f t x w) → ▸ (λ t → f (dfix f) x w)
ere {f = f} x t = transport (cong (λ x → x _ _) (pfix′ f)) (x t)

_∈_ : List Tok → Lang → Set
w ∈ P = P w

⊘ : Lang
⊘ _ = ⊥

𝒰 : Lang
𝒰 _ = ⊤

ε : Lang
ε w = w ≡ []

tok : Tok → Lang
tok t w = w ≡ t ∷ []

string : List Tok → Lang
string s w = w ≡ s

_∪_ : Lang → Lang → Lang
(P ∪ Q) w = P w ⊎ Q w

_∩_ : Lang → Lang → Lang
(P ∩ Q) w = P w × Q w

_ᶜ : Lang → Lang
(P ᶜ) w = P w → ⊥

_∖_ : Lang → Lang → Lang
(P ∖ Q) = P ∩ (Q ᶜ)

infixr 22 _*_

-- dependent sequencing
_*_ : (P : Lang) → (∀ {w} → P w → Lang) → Lang
(P * f) w = Σ (_ × _) λ (u , v) → (w ≡ u ++ v) × (Σ (P u) λ x → f x v)

infixr 22 _⋆_
infixr 20 _∪_

-- non-dependent sequencing
_⋆_ : Lang → Lang → Lang
P ⋆ Q = P * λ _ → Q 

natLang : Lang
natLang w = Σ ℕ λ n → w ≡ Tℕ n ∷ []

guard : Bool → Lang
guard false = ⊘
guard true = ε

expr : Lang
expr = fix (λ f b →
      guard b ⋆ f false ⋆ tok T+ ⋆ f true
    ∪ tok TX
  ) true

x+x+x : (TX ∷ T+ ∷ TX ∷ T+ ∷ TX ∷ []) ∈ expr
x+x+x =
  inl $
    _ , refl , refl ,
    _ , refl ,
    then (inr refl) ,
    _ , refl , refl ,
    then (inl $
      _ , refl , refl ,
      _ , refl ,
      then (inr refl) ,
      _ , refl , refl ,
      then (inr refl))

liar : Lang
liar = fix₀ _ᶜ

anyLiar : ∀{x} → x ∈ liar
-- I thought 'ere' might be useful here, but it seems like this is not provable.
anyLiar = λ x → {!!}

-- We can prove interesting things about our languages, for example that they are unambiguous:

unambiguous : Lang → Set
unambiguous P = ∀{w} → isProp (w ∈ P)

unambiguous⊘ : unambiguous ⊘
unambiguous⊘ ()

unambiguous𝒰 : unambiguous 𝒰
unambiguous𝒰 tt tt = refl

unambiguousε : unambiguous ε
unambiguousε = isPropXs≡[]

unambiguousTok : ∀{t} → unambiguous (tok t)
unambiguousTok {t} {w} = Discrete→isSet (discreteList discreteTok) w (t ∷ [])

-- unambiguous∩ : ∀{P Q : [ Lang ]} → unambiguous P → unambiguous Q → unambiguous (P ∩ Q)
-- unambiguous∩ uaP uaQ (n , x₁ , y₁) (m , x₂ , y₂) refl with uaP (n , x₁) (n , x₂) refl | uaQ (n , y₁) (n , y₂) refl
-- ... | refl | refl = refl
-- 
-- -- Not true:
-- -- unambiguous* : ∀{P : [ Lang ]} {f : ∀ {n} .{pf} {w} → P {n} pf w → Lang n} → unambiguous P → (∀ {w} (x : ∀{n} .{pf′} → P {n} pf′ w) → unambiguous (λ {n} → f {n} {mkProxy} {w} x)) → unambiguous (P * f) 
-- -- unambiguous* uaP uaQ (n , (u₁ , v₁) , refl , Pu₁ , fv₁) (n , (u₂ , v₂) , fst , Pu₂ , fv₂) refl with uaP (n , Pu₁) (n , {!Pu₂!}) refl
-- -- ... | a = {!!}
-- -- counterexample: natLang * λ _ → natLang matches "123" with both "12","3" and "1","23"
-- 
-- postulate ℕshowInjective : ∀ x y → toList (Data.Nat.Show.show x) ≡ toList (Data.Nat.Show.show y) → x ≡ y

-- foo : (p₁ : w ≡ Tℕ n ∷ []) → (p₂ : w ≡ Tℕ m ∷ []) → p₁ ≡ p₂

unambiguousNatLang : unambiguous natLang
unambiguousNatLang {w = w} (n , p₁) (m , p₂) =
  let n≡m = Tℕ-inj (cons-inj₁ (subst (\w → w ≡ _) p₁ p₂))
  in Σ≡Prop (λ _ → Discrete→isSet (discreteList discreteTok) _ _) n≡m

-- unambiguousExpr : unambiguous expr
-- unambiguousExpr (suc (suc n) , inj₁ ((.[] , .(('x' ∷ []) ++ [])) , refl , refl , (.('x' ∷ []) , .[]) , refl , inj₂ refl , (.('+' ∷ []) , v) , () , refl , snd)) (.(suc (suc n)) , inj₂ refl) refl
-- unambiguousExpr (suc (suc n) , inj₁ ((.[] , .(('x' ∷ []) ++ ('+' ∷ []) ++ snd₂)) , refl , refl , (.('x' ∷ []) , .(('+' ∷ []) ++ snd₂)) , refl , inj₂ refl , (.('+' ∷ []) , snd₂) , refl , refl , snd)) (.(suc (suc n)) , inj₁ ((.[] , .([] ++ ('x' ∷ []) ++ ('+' ∷ []) ++ snd₂)) , refl , refl , (.('x' ∷ []) , .([] ++ ('+' ∷ []) ++ snd₂)) , refl , inj₂ refl , (.('+' ∷ []) , .([] ++ snd₂)) , refl , refl , snd₁)) refl = {!snd₁!}
-- unambiguousExpr (suc (suc n) , inj₂ refl) (.(suc (suc n)) , inj₁ ((.[] , .(('x' ∷ []) ++ ('+' ∷ []) ++ v″)) , () , refl , (.('x' ∷ []) , .(('+' ∷ []) ++ v″)) , refl , inj₂ refl , (.('+' ∷ []) , v″) , refl , refl , snd)) refl
-- unambiguousExpr (suc zero , inj₂ refl) (.1 , inj₂ refl) refl = refl
-- unambiguousExpr (suc (suc n) , inj₂ refl) (.(suc (suc n)) , inj₂ refl) refl = refl
