module DDG4 where

open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; z≤n ; _⊔_)
open import Data.Nat.Properties
open import Data.Bool using (Bool ; true ; false)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Data.Empty
open import Data.Unit
open import Data.List hiding ([_])
open import Data.Product
open import Data.Sum
open import Function
open import Level using (Level)
open import Relation.Unary using (_⇒_)

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

-- _∈_ : List Tok → Lang → Set
-- w ∈ P = P w

fueled : (Lang → Lang) → ℕ → Lang
fueled f 0 = ⊘ -- ran out of fuel
fueled f (suc n) = f (fueled f n)

[_] : Lang → Set
[ f ] = ∀{w} → f w

record Container : Set₁ where
  constructor _▹_
  field
    Shape : Lang
    Position : ∀{w} → Shape w → Lang

□_ : Lang → Lang
(□ f) w = ∀{w′} → length w′ ≤ length w → f w′

-- ⟦_⟧ : Container → Lang → Lang
-- ⟦ S ▹ P ⟧ X w = Σ[ x ∈ S w ] P x w → X w

data Desc : Set₁ where
  I : Desc
  _∪_ : Desc → Desc → Desc
  K : Lang → Desc

⟦_⟧ : Desc → Lang → Lang
⟦ I ⟧ X = X
⟦ σ₁ ∪ σ₂ ⟧ X w = ⟦ σ₁ ⟧ X w ⊎ ⟦ σ₂ ⟧ X w
⟦ K L ⟧ _ = L

data Fix (σ : Desc) : Lang where
  step : [ ⟦ σ ⟧ (Fix σ) ⇒ Fix σ ]

FFix : ∀{σ w} → Fix σ w ↔ ⟦ σ ⟧ (Fix σ) w
FFix = mk↔′ (λ where (step x) → x) step (λ _ → refl) λ where (step x) → refl



-- bare fixed point of languages
fix₀ : (Lang → Lang) → Lang
fix₀ f w = ∃[ n ] fueled f n w

module _ (F : Lang → Lang) where

    record Applicative (M : (ℕ → Set) → Set) : Set₁ where
      field
        pure : ∀{A} → (∀{i j} → i ≤ j → A i → A j) → A 0 → M A
        ap : ∀{A B} → (∀{i j} → i ≤ j → A i → A j) → M (λ i → ∀{j} → i ≤ j → A j → B j) → M A → M B
    open Applicative

    postulate traverse : ∀{M L w} {L′ : ℕ → Lang} → Applicative M → (∀{w} → L w → M (λ i → L′ i w)) → F L w → M (λ i → F (L′ i) w)

    idApplicative : Applicative λ x → x 0
    pure idApplicative _ x = x
    ap idApplicative _ f x = f ≤-refl x

    ΣApplicative : Applicative (Σ ℕ)
    pure ΣApplicative _ x = 0 , x
    ap ΣApplicative wk (n , f) (m , x) = n ⊔ m , f (m≤m⊔n n m) (wk (m≤n⊔m n m) x)

    fmap : ∀{L L′ w} → (∀{w} → L w → L′ w) → F L w → F L′ w
    fmap {L′ = L′} = traverse {L′ = const _} idApplicative

    sequence : ∀{M w} {L : ℕ → Lang} → Applicative M → F (λ w → M (λ i → L i w)) w → M (λ i → F (L i) w)
    sequence a = traverse a id

    ffix₀ : Σ[ f ∈ (∀{w} → fix₀ F w → F (fix₀ F) w) ] Σ[ g ∈ (∀{w} → F (fix₀ F) w → fix₀ F w) ] (∀{w x} → f {w} (g x) ≡ x) × (∀{w x} → g {w} (f x) ≡ x)
    ffix₀ = (λ { (suc n , x) → fmap (n ,_) x })
          , (λ x → let n , y = sequence {M = Σ ℕ} {L = fueled F} ΣApplicative x in suc n , y)
          , (λ {w} {x} → begin (let n , y = sequence ΣApplicative x in fmap (n ,_) y)
                         ≡⟨ {!!} ⟩ -- in this case the fuel of all the branches is weakened to the maximum fuel.
                                   -- That means it is not exactly equal, but it should be equivalent according to some sensible relation.
                                x
                         ∎)
          , λ { {w} {suc n , x} → begin (let n′ , y = sequence ΣApplicative (fmap (n ,_) x) in suc n′ , y)
                                  ≡⟨ {!!} ⟩ -- I think this is some kind of naturality
                                         suc n , sequence {L = const _} idApplicative x 
                                  ≡⟨ {!!} ⟩ -- This is essentially 'fmap id ≡ id'
                                         suc n , x
                                  ∎ }

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

-- _∪_ : Lang → Lang → Lang
-- (P ∪ Q) w = P w ⊎ Q w

-- _∩_ : Lang → Lang → Lang
-- (P ∩ Q) w = P w × Q w

_ᶜ : Lang → Lang
(P ᶜ) w = P w → ⊥

-- _∖_ : Lang → Lang → Lang
-- (P ∖ Q) = P ∩ (Q ᶜ)

infixr 22 _*_

-- dependent sequencing
-- _*_ : (P : Lang) → (∀ {w} → P w → Lang) → Lang
-- (P * f) w = Σ[ (u , v) ∈ _ × _ ] (w ≡ u ++ v) × (Σ[ x ∈ P u ] f x v)

infixr 22 _⋆_
infixr 20 _∪_

-- non-dependent sequencing
-- _⋆_ : Lang → Lang → Lang
-- P ⋆ Q = P * λ _ → Q 

natLang : Lang
natLang w = Σ[ n ∈ ℕ ] w ≡ Tℕ n ∷ []

guard : Bool → Lang
guard false = ⊘
guard true = ε

-- Expr : Lang
-- Expr = Fix ((const Bool) ▹ (λ where false → {!x ⋆ tok T+ ⋆ x!} ; true → {!!}))

-- expr₀ : Lang
-- expr₀ = fix₀ (λ x → x ⋆ tok T+ ⋆ x ∪ tok TX)

-- x+x+x₁ : (TX ∷ T+ ∷ TX ∷ T+ ∷ TX ∷ []) ∈ expr₀
-- x+x+x₁ = 3 , inj₁ (_ , refl , inj₂ refl , _ , refl , refl , inj₁ (_ , refl , inj₂ refl , _ , refl , refl , inj₂ refl))
-- 
-- x+x+x₂ : (TX ∷ T+ ∷ TX ∷ T+ ∷ TX ∷ []) ∈ expr₀
-- x+x+x₂ = 3 , inj₁ (_ , refl , inj₁ (_ , refl , inj₂ refl , _ , refl , refl , inj₂ refl) , _ , refl , refl , inj₂ refl)
-- 
-- -- language of expressions with associativity disambiguation
-- expr : Lang
-- expr = fix (λ f b →
--       guard b ⋆ f false ⋆ tok T+ ⋆ f true
--     ∪ tok TX
--   ) true
-- 
-- x+x+x : (TX ∷ T+ ∷ TX ∷ T+ ∷ TX ∷ []) ∈ expr
-- x+x+x = 3 ,
--   inj₁ (
--     _ , refl , refl ,
--     _ , refl ,
--     inj₂ refl ,
--     _ , refl , refl ,
--     inj₁ (
--       _ , refl , refl ,
--       _ , refl ,
--       inj₂ refl ,
--       _ , refl , refl ,
--       inj₂ refl))
-- -- This should be the only proof that 'x+x+x' is in 'expr'

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

variable
  ℓ : Level
  A B : Set ℓ

-- ν : (List A → B) → B -- “nullable”
ν : Lang → Set -- “nullable”
ν f = f []

𝒟 : (List A → B) → List A → (List A → B) -- “derivative”
𝒟 f u = λ v → f (u ++ v)

δ : (List A → B) → A → (List A → B)
δ f a = 𝒟 f (a ∷ [])

variable P Q : Lang → Lang

open Inverse

foo : ∀{F : Set → Set}{A : Set} → (∃[ B ] F ⊥ ≡ (A × B)) ↔ (∃[ C ] F (F ⊥) ≡ (A × C))
to foo (b , x) = {!!}
from foo = {!!}
to-cong foo = {!!}
from-cong foo = {!!}
inverse foo = {!!}

νf : (Lang → Lang) → Set → Set
νf P νres = P (const νres) []

proper : (Lang → Lang) → Set₁
proper P = (f g : Lang) (w : List Tok) → (∀{w′} → length w′ ≤ length w → f w′ → g w′) → P f w → P g w

-- ν (fix₀ P) = P (λ L w → ?) []

-- νfix : proper P → ν (fix₀ P) ↔ ∃[ n ] (fueled () n)
-- νfix {P = P} pr = mk↔′
--   (λ x → pr (fix₀ P) (const (ν (fix₀ P))) [] (λ where
--     {w′ = []} _ → id)
--     (proj₁ (ffix₀ P) x))
--   (λ x → {!!})
--   {!!}
--   {!!}

variable σ σ′ σ″ : Desc

νσ : Desc → Set → Set
νσ I x = x
νσ (σ₁ ∪ σ₂) x = νσ σ₁ x ⊎ νσ σ₂ x
νσ (K L) _ = ν L

x≡stepx : (x : Fix I []) → x ≡ step x
x≡stepx (step x) = cong step (x≡stepx x)

-- ⟦_⟧map : ∀{L L′} → (σ : Desc) → (∀{w} → L w → L′ w) → ∀{w} → ⟦ σ ⟧ L w → ⟦ σ ⟧ L′ w
-- ⟦ I ⟧map f x = f x
-- ⟦ σ₁ ∪ σ₂ ⟧map f (inj₁ x) = inj₁ (⟦ σ₁ ⟧map f x)
-- ⟦ σ₁ ∪ σ₂ ⟧map f (inj₂ y) = inj₂ (⟦ σ₂ ⟧map f y)

fmapFix : (∀{L w} → ⟦ σ ⟧ L w → ⟦ σ′ ⟧ L w) → (∀{w} → Fix σ w → Fix σ′ w)
fmapFix {σ} {σ′} f (step x) = step (f (fmapFix′ σ f x))
  where
    fmapFix′ : ∀{σ σ′ w} → (σ″ : Desc) → (∀{L w} → ⟦ σ ⟧ L w → ⟦ σ′ ⟧ L w) → ⟦ σ″ ⟧ (Fix σ) w → ⟦ σ″ ⟧ (Fix σ′) w
    fmapFix′ {σ = σ} {σ′} I f x = fmapFix f x
    fmapFix′ (σ₁ ∪ σ₂) f (inj₁ x) = inj₁ (fmapFix′ σ₁ f x)
    fmapFix′ (σ₁ ∪ σ₂) f (inj₂ y) = inj₂ (fmapFix′ σ₂ f y)
    fmapFix′ (K _) f x = x

νFix : ν (Fix σ) ↔ νσ σ (ν (Fix σ))
νFix {σ} = mk↔′ to₁ (from′ {σ} {σ}) to∘from from∘to where
    to₁ : ∀{σ} → ν (Fix σ) → νσ σ (ν (Fix σ))
    to₁ {σ} (step x) = to₂ {σ} {σ} x where
        to₂ : ∀{σ σ′} → ν (⟦ σ ⟧ (Fix σ′)) → νσ σ (ν (Fix σ′))
        to₂ {I} = id
        to₂ {σ₁ ∪ σ₂} (inj₁ x) = inj₁ (to₂ {σ₁} x)
        to₂ {σ₁ ∪ σ₂} (inj₂ y) = inj₂ (to₂ {σ₂} y)
        to₂ {K _} x = x
    from′ : ∀{σ σ′} → νσ σ (ν (Fix σ′)) → ν (Fix σ′) 
    from′ {I} x = x
    from′ {σ₁ ∪ σ₂} (inj₁ x) = from′ {σ = σ₁} x
    from′ {σ₁ ∪ σ₂} (inj₂ y) = from′ {σ = σ₂} y
    from′ {K L} x = {!!}
    -- from′ {σ = I} ()
    -- from′ {σ₁ ∪ σ₂} (inj₁ x) = fmapFix inj₁ (from′ x)
    -- from′ {σ₁ ∪ σ₂} (inj₂ y) = fmapFix inj₂ (from′ y)
    to∘from : (x : νσ σ (ν (Fix σ))) → to₁ {σ} (from′ x) ≡ x
    -- to∘from {I} ()
    -- to∘from {σ₁ ∪ σ₂} (inj₁ x) = {!!}
    -- to∘from {σ₁ ∪ σ₂} (inj₂ y) = {!!}
    -- to∘from {σ₁ ∪ σ₂} (inj₁ x) = {!to∘from {σ₁} x!}
    -- to∘from {σ₁ ∪ σ₂} (inj₂ y) = {!to∘from {σ₂} y!}
    from∘to : (x : ν (Fix σ)) → from′ (to₁ x) ≡ x
    -- from∘to {I} (step x) = trans (from∘to x) (x≡stepx x)


  -- (λ where
  --   (step (s , k)) → s , λ where
  --     {[]} z≤n p → k z≤n p
  --     {x ∷ w′} () )
  -- (λ (s , p) → step (s , (λ where
  --   {[]} z≤n pos → p z≤n pos
  --   {_ ∷ _} ())))
  -- (λ where
  --   (s , k) → {!!})
  -- λ x → {!!}

-- νfix : ν (fix₀ P) ↔ P ⊘
-- to νfix (suc zero , x) = ?
-- to (νfix {P = P}) (suc (suc zero) , x) = {!P!}
-- to νfix (suc (suc (suc n)) , x) = {!!}
-- from νfix x = suc zero , ?
-- to-cong νfix = {!!}
-- from-cong νfix = {!!}
-- inverse νfix = {!!}
-- 
