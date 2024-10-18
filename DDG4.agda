module DDG4 where

-- open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.Transport
-- open import Cubical.Data.Nat
-- open import Cubical.Data.Maybe
-- open import Cubical.Data.List
-- open import Cubical.Data.Empty as ⊥
-- open import Cubical.Data.Sum
-- open import Cubical.Data.Sigma
-- open import Cubical.Data.Bool
-- open import Agda.Builtin.Unit
-- open import Cubical.Relation.Nullary.Base
-- open import Cubical.Foundations.Function
-- open import Cubical.Relation.Nullary

open import Data.Nat using (ℕ ; suc)
open import Data.Bool using (Bool ; true ; false)
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit
open import Data.List
open import Data.Product
open import Data.Sum

-- Cubical Agda does not like String and Char
data Tok : Set where
  TX : Tok
  T+ : Tok
  Tℕ : ℕ → Tok

-- ¬TX≡T+ : ¬(TX ≡ T+)
-- ¬TX≡T+ p = subst (λ where TX → Tok ; T+ → ⊥ ; (Tℕ _) → ⊥) p TX
-- 
-- ¬TX≡Tℕ : ∀{n} → ¬(TX ≡ Tℕ n)
-- ¬TX≡Tℕ p = subst (λ where TX → Tok ; T+ → ⊥ ; (Tℕ _) → ⊥) p TX
-- 
-- ¬T+≡TX : ¬(T+ ≡ TX)
-- ¬T+≡TX p = subst (λ where TX → ⊥ ; T+ → Tok ; (Tℕ _) → ⊥) p T+
-- 
-- ¬T+≡Tℕ : ∀{n} → ¬(T+ ≡ Tℕ n)
-- ¬T+≡Tℕ p = subst (λ where TX → ⊥ ; T+ → Tok ; (Tℕ _) → ⊥) p T+
-- 
-- ¬Tℕ≡TX : ∀{n} → ¬(Tℕ n ≡ TX)
-- ¬Tℕ≡TX {n} p = subst (λ where TX → ⊥ ; T+ → ⊥ ; (Tℕ _) → Tok) p (Tℕ n)
-- 
-- ¬Tℕ≡T+ : ∀{n} → ¬(Tℕ n ≡ T+)
-- ¬Tℕ≡T+ {n} p = subst (λ where TX → ⊥ ; T+ → ⊥ ; (Tℕ _) → Tok) p (Tℕ n)

Tℕ-inj : ∀{n m} → Tℕ n ≡ Tℕ m → n ≡ m
Tℕ-inj {n} = cong (λ where (Tℕ n) → n ; _ → n)

-- discreteTok : Discrete Tok
-- discreteTok TX TX = yes refl
-- discreteTok TX T+ = no ¬TX≡T+
-- discreteTok TX (Tℕ _) = no ¬TX≡Tℕ
-- discreteTok T+ TX = no ¬T+≡TX
-- discreteTok T+ T+ = yes refl
-- discreteTok T+ (Tℕ x) = no ¬T+≡Tℕ
-- discreteTok (Tℕ x) TX = no ¬Tℕ≡TX
-- discreteTok (Tℕ x) T+ = no ¬Tℕ≡T+
-- discreteTok (Tℕ x) (Tℕ y) with discreteℕ x y
-- ... | yes x≡y = yes (cong Tℕ x≡y)
-- ... | no ¬x≡y = no λ Tℕx≡Tℕy → ¬x≡y (Tℕ-inj Tℕx≡Tℕy)

Lang : Set₁
Lang = List Tok → Set

⊘ : Lang
⊘ _ = ⊥

-- normal fixed point of languages
fix₀ : (Lang → Lang) → Lang
fix₀ f w = Σ[ n ∈ ℕ ] go n w where
  go : ℕ → Lang
  go 0 = ⊘ -- ran out of fuel
  go (suc n) = f (go n)

-- -- data-dependent fixed point of languages
-- fix : ∀ {A : Set} → ((A → Lang) → A → Lang) → A → Lang
-- fix f = fix′ λ x → f λ y w → ▸ λ t → x t y w
-- 
-- -- useful for proving that a string is in a fixed point language.
-- then : ∀{l} {A : Set l} {f : ▹ (A → Lang) → A → Lang} {x w} → f (dfix f) x w → ▸ (λ t → dfix f t x w)
-- then {f = f} x _ = transport (sym (cong (λ x → x _ _) (pfix′ f))) x
-- 
-- -- perhaps not useful
-- -- ere : ∀{l} {A : Set l} {f : ▹ (A → Lang) → A → Lang} {x w} → ▸ (λ t → dfix f t x w) → ▸ (λ t → f (dfix f) x w)
-- -- ere {f = f} x t = transport (cong (λ x → x _ _) (pfix′ f)) (x t)

_∈_ : List Tok → Lang → Set
w ∈ P = P w


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
expr = fix₀ (λ x → x ⋆ tok T+ ⋆ x ∪ tok TX)

x+x+x₁ : (TX ∷ T+ ∷ TX ∷ T+ ∷ TX ∷ []) ∈ expr
x+x+x₁ = 3 , inj₁ (_ , refl , inj₂ refl , _ , refl , refl , inj₁ (_ , refl , inj₂ refl , _ , refl , refl , inj₂ refl))

x+x+x₂ : (TX ∷ T+ ∷ TX ∷ T+ ∷ TX ∷ []) ∈ expr
x+x+x₂ = 3 , inj₁ (_ , refl , inj₁ (_ , refl , inj₂ refl , _ , refl , refl , inj₂ refl) , _ , refl , refl , inj₂ refl)

-- -- language of expressions with associativity disambiguation
-- expr : Lang
-- expr = fix (λ f b →
--       guard b ⋆ f false ⋆ tok T+ ⋆ f true
--     ∪ tok TX
--   ) true
-- 
-- x+x+x : (TX ∷ T+ ∷ TX ∷ T+ ∷ TX ∷ []) ∈ expr
-- x+x+x =
--   inl $
--     _ , refl , refl ,
--     _ , refl ,
--     then (inr refl) ,
--     _ , refl , refl ,
--     then (inl $
--       _ , refl , refl ,
--       _ , refl ,
--       then (inr refl) ,
--       _ , refl , refl ,
--       then (inr refl))
-- -- This should be the only proof that 'x+x+x' is in 'expr'
-- 
-- liar : Lang
-- liar = fix₀ _ᶜ
-- 
-- -- anyLiar : ∀{x} → x ∈ liar
-- -- -- I thought 'ere' might be useful here, but it seems like this is not provable.
-- -- anyLiar = λ x → {!!}
-- 
-- -- We can prove interesting things about our languages, for example that they are unambiguous:
-- 
-- unambiguous : Lang → Set
-- unambiguous P = ∀{w} → isProp (w ∈ P)
-- 
-- unambiguous⊘ : unambiguous ⊘
-- unambiguous⊘ ()
-- 
-- unambiguous𝒰 : unambiguous 𝒰
-- unambiguous𝒰 tt tt = refl
-- 
-- unambiguousε : unambiguous ε
-- unambiguousε = isPropXs≡[]
-- 
-- unambiguousGuard : ∀{b} → unambiguous (guard b)
-- unambiguousGuard {false} {w} = unambiguous⊘ {w}
-- unambiguousGuard {true} = unambiguousε
-- 
-- unambiguousTok : ∀{t} → unambiguous (tok t)
-- unambiguousTok {t} {w} = Discrete→isSet (discreteList discreteTok) w (t ∷ [])
-- 
-- -- unambiguous∩ : ∀{P Q : [ Lang ]} → unambiguous P → unambiguous Q → unambiguous (P ∩ Q)
-- -- unambiguous∩ uaP uaQ (n , x₁ , y₁) (m , x₂ , y₂) refl with uaP (n , x₁) (n , x₂) refl | uaQ (n , y₁) (n , y₂) refl
-- -- ... | refl | refl = refl
-- 
-- rightRadicals : Lang → Lang
-- rightRadicals P w = Σ[ pre ∈ List Tok ] P pre × P (pre ++ w)
-- 
-- leftRadicals : Lang → Lang
-- leftRadicals P w = Σ[ post ∈ List Tok ] P post × P (w ++ post)
-- 
-- findSuffix : (u v : List Tok) → Σ[ s ∈ _ ] (Σ[ b ∈ _ ] u ≡ b ++ s) × (Σ[ b ∈ _ ] v ≡ b ++ s)
-- findSuffix [] v = [] , ([] , refl) , (v , sym (++-unit-r v))
-- findSuffix u@(_ ∷ _) [] = [] , (u , sym (++-unit-r u)) , ([] , refl)
-- findSuffix (x ∷ u) (y ∷ v) with findSuffix u v | discreteTok x y
-- ... | s , ([] , u≡s) , [] , v≡s | yes x≡y = x ∷ s , ([] , cong (x ∷_) u≡s) , [] , (subst (λ x → _ ≡ _ ∷ x) v≡s (subst (λ x → x ∷ _ ≡ _ ∷ _) x≡y refl))
-- --  Note: here we drop the proof that the elements before the suffix are different, thus we forget we found the largest suffix.
-- ... | s , ([] , u≡s) , [] , v≡s | no _ = s , ((x ∷ []) , cong (x ∷_) u≡s) , (y ∷ []) , cong (y ∷_) v≡s
-- ... | s , ([] , u≡s) , (b₂@(_ ∷ _) , v≡s) | _ = s , ((x ∷ []) , (cong (x ∷_) u≡s)) , (y ∷ b₂ , cong (y ∷_) v≡s)
-- ... | s , (b₁@(_ ∷ _) , p₁) , (b₂ , p₂) | _ = s , ((x ∷ b₁) , (cong (x ∷_) p₁)) , ((y ∷ b₂) , (cong (y ∷_) p₂)) 
-- 
-- findRadical : ∀{w u₁ v₁ u₂ v₂ : List Tok} → (w ≡ u₁ ++ v₁) → (w ≡ u₂ ++ v₂) → Σ _ λ r → ((u₁ ≡ u₂ ++ r) × (r ++ v₁ ≡ v₂)) ⊎ ((u₁ ++ r ≡ u₂) × (v₁ ≡ r ++ v₂))
-- findRadical p₁ p₂ = {!!}
-- 
-- unambiguous⋆ : ∀{P Q} → (∀{w} → rightRadicals P w → leftRadicals Q w → ε w) → unambiguous P → unambiguous Q → unambiguous (P ⋆ Q) 
-- unambiguous⋆ pf uaP uaQ ((u₁ , v₁) , p₁ , x) ((u₂ , v₂) , p₂ , y) = {!!}
-- 
-- -- TODO: figure out suitable precondition
-- -- unambiguous* : ∀{P} {f : ∀ {w} → P w → Lang} → unambiguous P → (∀ {w} x → unambiguous (f {w} x)) → unambiguous (P * f) 
-- -- unambiguous* uaP uaQ ((u₁ , v₁) , x) ((u₂ , v₂) , y) = {!!}
-- -- unambiguous* uaP uaQ (n , (u₁ , v₁) , refl , Pu₁ , fv₁) (n , (u₂ , v₂) , fst , Pu₂ , fv₂) refl with uaP (n , Pu₁) (n , {!Pu₂!}) refl
-- -- ... | a = {!!}
-- -- Without precondition counter example: natLang * λ _ → natLang matches "123" with both "12","3" and "1","23"
-- 
-- unambiguousNatLang : unambiguous natLang
-- unambiguousNatLang (n , p₁) (m , p₂) =
--   let n≡m : n ≡ m
--       n≡m = Tℕ-inj (cons-inj₁ (subst (λ w → w ≡ _) p₁ p₂))
--   in Σ≡Prop (λ _ → Discrete→isSet (discreteList discreteTok) _ _) n≡m
-- 
-- unambiguousExpr : unambiguous expr
-- unambiguousExpr (inl x) (inl y) = cong inl (unambiguous⋆ (
--   λ where
--     {[]} _ _ → refl
--     {_ ∷ _} (_ , pre≡[] , pre++w≡[]) _ → ⊥.rec (¬cons≡nil (subst (λ x → x ++ _ ≡ _) pre≡[] pre++w≡[]))
--   ) unambiguousε (unambiguous⋆ {!!} {!!} (unambiguous⋆ {!!} unambiguousTok {!!})) x y)
-- unambiguousExpr (inl x) (inr y) = {!!}
-- unambiguousExpr (inr x) (inl y) = {!!}
-- unambiguousExpr (inr x) (inr y) = cong inr (unambiguousTok x y)
-- 
