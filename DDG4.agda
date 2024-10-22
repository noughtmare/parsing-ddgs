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
open import Function

-- Cubical Agda does not like String and Char
data Tok : Set where
  TX : Tok
  T+ : Tok
  Tℕ : ℕ → Tok

Tℕ-inj : ∀{n m} → Tℕ n ≡ Tℕ m → n ≡ m
Tℕ-inj {n} = cong (λ where (Tℕ n) → n ; _ → n)

Lang : Set₁
Lang = List Tok → Set

⊘ : Lang
⊘ _ = ⊥

_∈_ : List Tok → Lang → Set
w ∈ P = P w

-- bare fixed point of languages
fix₀ : (Lang → Lang) → Lang
fix₀ f w = Σ[ n ∈ ℕ ] go n w where
  go : ℕ → Lang
  go 0 = ⊘ -- ran out of fuel
  go (suc n) = f (go n)

-- ffix₀ : ∀{f x} → (∀{y z : Lang} → (∀{w} → y w → z w) → ∀{w} → f y w → f z w) → x ∈ fix₀ f → x ∈ f (fix₀ f)
-- ffix₀ fmap (suc n , p) = fmap (n ,_) p

module _ (F : Lang → Lang) where

    record Applicative (I : Set) (M : (I → Set) → Set) : Set₁ where
      field
        return : ∀{A} → A → M (λ _ → A)
        ap : ∀{A B} → M (λ i → A i → B i) → M A → M B

    postulate traverse : ∀{I M L w} {L′ : I → Lang} → Applicative I M → (∀{w} → L w → M (λ i → L′ i w)) → F L w → M (λ i → F (L′ i) w)

    fmap : ∀{L L′ w} → (∀{w} → L w → L′ w) → F L w → F L′ w
    fmap = traverse {M = λ x → x tt} (record { return = λ x → x ; ap = λ f x → f x })

    ffix₀ : (∀{w} → fix₀ F w → F (fix₀ F) w) × (∀{w} → F (fix₀ F) w → fix₀ F w)
    ffix₀ = (λ { (suc n , x) → fmap (n ,_) x })
          , (λ x → {!traverse {I = ℕ} {M = Σ ℕ} ? ? ?!})

-- data-dependent fixed point of languages
fix : ∀ {A : Set} → ((A → Lang) → A → Lang) → A → Lang
fix {A} f x w = Σ[ n ∈ ℕ ] go n x w where
  go : ℕ → A → Lang
  go 0 = λ _ → ⊘ -- ran out of fuel
  go (suc n) = f (go n)


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
(P * f) w = Σ[ (u , v) ∈ _ × _ ] (w ≡ u ++ v) × (Σ[ x ∈ P u ] f x v)

infixr 22 _⋆_
infixr 20 _∪_

-- non-dependent sequencing
_⋆_ : Lang → Lang → Lang
P ⋆ Q = P * λ _ → Q 

natLang : Lang
natLang w = Σ[ n ∈ ℕ ] w ≡ Tℕ n ∷ []

guard : Bool → Lang
guard false = ⊘
guard true = ε

expr₀ : Lang
expr₀ = fix₀ (λ x → x ⋆ tok T+ ⋆ x ∪ tok TX)

x+x+x₁ : (TX ∷ T+ ∷ TX ∷ T+ ∷ TX ∷ []) ∈ expr₀
x+x+x₁ = 3 , inj₁ (_ , refl , inj₂ refl , _ , refl , refl , inj₁ (_ , refl , inj₂ refl , _ , refl , refl , inj₂ refl))

x+x+x₂ : (TX ∷ T+ ∷ TX ∷ T+ ∷ TX ∷ []) ∈ expr₀
x+x+x₂ = 3 , inj₁ (_ , refl , inj₁ (_ , refl , inj₂ refl , _ , refl , refl , inj₂ refl) , _ , refl , refl , inj₂ refl)

-- language of expressions with associativity disambiguation
expr : Lang
expr = fix (λ f b →
      guard b ⋆ f false ⋆ tok T+ ⋆ f true
    ∪ tok TX
  ) true

x+x+x : (TX ∷ T+ ∷ TX ∷ T+ ∷ TX ∷ []) ∈ expr
x+x+x = 3 ,
  inj₁ (
    _ , refl , refl ,
    _ , refl ,
    inj₂ refl ,
    _ , refl , refl ,
    inj₁ (
      _ , refl , refl ,
      _ , refl ,
      inj₂ refl ,
      _ , refl , refl ,
      inj₂ refl))
-- This should be the only proof that 'x+x+x' is in 'expr'

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
