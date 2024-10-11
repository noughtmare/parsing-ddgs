open import Data.Char hiding (_≤_ ; _<_)
open import Data.List hiding ([_] ; _++_ ; concat) renaming (length to List-length ; replicate to List-replicate)
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Sum
open import Data.Product
open import Data.Bool hiding (_≤_ ; _<_)
open import Data.Nat
open import Data.List.Relation.Unary.All hiding (fromList) renaming (toList to All-toList)
open import Data.String hiding (_≤_ ; _<_) renaming (_++_ to _+++_ ; _≟_ to eqs )
import Data.Nat.Show
open import Function using (id ; _∘_)
import Data.List.Properties
import Data.Nat.Properties
open import Relation.Unary using (_⇒_ ; _∪_)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Vec hiding ([_]) renaming (length to Vec-length ; _++_ to _++V_)

variable n n′ m m′ : ℕ

record FinString (n : ℕ) : Set where
  field
    len : ℕ
    s : Vec Char len
    len<n : len < n
open FinString

emptyFS : FinString (suc n)
len emptyFS = 0
s emptyFS = []
len<n emptyFS = s≤s z≤n

FinString0→⊥ : FinString 0 → ⊥
FinString0→⊥ x with x .len<n
... | ()

FS0-unique : (x y : FinString 0) → x ≡ y
FS0-unique x with FinString0→⊥ x
... | ()

wkFS≤ : (n ≤ m) → FinString n → FinString m
wkFS≤ n≤m x .len = x .len
wkFS≤ _ x .s = x .s
wkFS≤ n≤m x .len<n = Data.Nat.Properties.≤-trans (x .len<n) n≤m

-- wkFS : (n < m) → FinString n → FinString m
-- wkFS _ x .s = x .s
-- wkFS pf′ x .pf = Data.Nat.Properties.<-trans (x .pf) pf′

[_] : (ℕ → Set₁) → Set₁
[ P ] = ∀{n} → P n

-- ⟨_⟩ : (ℕ → Set₁) → Set₁
-- ⟨ P ⟩ = ∀{n} → .(1 ≤ n) → P n

infix 9 □_
record □_ {l} (A : ℕ → Set l) (n : ℕ) : Set l where
  constructor mkBox
  field call : ∀ {m} → .(m < n) → A m
open □_ public

-- infix 9 □⁺_
-- record □⁺_ {l} (A : ℕ → Set l) (n : ℕ) : Set l where
--   constructor mkBox
--   field call : ∀ {m} → .(1 ≤ m) → .(m < n) → A m
-- open □⁺_ public

Lang : ℕ → Set₁
Lang n = FinString n → Set

record Lang⁺ (n : ℕ) : Set₁ where
  field
    lang : Lang n
    nonempty : ∀{w} → lang w → 1 ≤ w .len
open Lang⁺

-- extract : n < m → (□ Lang) m → Lang n
-- extract n<m □Lang = call □Lang n<m
-- 
-- wkLang : (n ≤ m) → Lang m → Lang n
-- wkLang pf P = P ∘ wkFS≤ pf

empty : [ Lang ]
empty _ = ⊥

empty⁺ : [ Lang⁺ ]
lang empty⁺ = empty
nonempty empty⁺ ()

universe : [ Lang ]
universe _ = ⊤

ε : [ Lang ]
ε w with w .len
... | 0 = ⊤
... | suc _ = ⊥

char : Char → [ Lang ]
char c w with w .len | w .s
... | 1 | c′ ∷ [] = c ≡ c′
... | 0 | _ = ⊥
... | suc (suc _) | _ = ⊥

char⁺ : Char → [ Lang⁺ ]
lang (char⁺ c) = char c
nonempty (char⁺ c) {record { len = suc zero }} _ = Data.Nat.Properties.≤-refl

string : (s′ : String) → [ Lang ]
string s′ w with Data.String.uncons s′ | w .len | w .s | w .len<n
... | nothing | 0 | _ | _ = ⊤
... | nothing | suc _ | _ | _ = ⊥
... | just (c , s″) | suc len′ | c′ ∷ w′ | s≤s pf = c ≡ c′ × string s″ (record { len = len′ ; s = w′ ; len<n = pf })
... | just _ | 0 | _ | _ = ⊥

-- -- _∪_ : [ Lang ⇒ Lang ⇒ Lang ]
-- -- (P ∪ Q) w = P w ⊎ Q w
-- 
-- -- _∩_ : Lang → Lang → Lang
-- -- (P ∩ Q) w = P w × Q w

m<n⇒m<1+n : m < n → m < 1 + n
m<n⇒m<1+n z<s               = z<s
m<n⇒m<1+n (s<s m<n@(s≤s _)) = s<s (m<n⇒m<1+n m<n)

1+n+m≡n+1+m : 1 + (n + m) ≡ n + (1 + m)
1+n+m≡n+1+m {zero} = refl
1+n+m≡n+1+m {suc n} = cong suc 1+n+m≡n+1+m

m≤n+m : m ≤ n + m
m≤n+m {zero} {n} = z≤n
m≤n+m {suc m} {n} = subst (λ x → suc m ≤ x) 1+n+m≡n+1+m (s≤s m≤n+m)

foo : ∀{a b} → (a < n) → (b < m) → (a + b) < (n + m)
foo {.(suc _)} {m} {zero} {b} (s≤s a<n) b<m = Data.Nat.Properties.<-trans b<m (s≤s m≤n+m)
foo {.(suc _)} {m} {suc a} {b} (s≤s a<n) b<m = s≤s (foo a<n b<m)

_++_ : FinString n → FinString m → FinString (n + m)
(x ++ y) .len = x .len + y .len
(x ++ y) .s = x .s ++V y .s
_++_ {n} {m} x y .len<n = foo (x .len<n) (y .len<n)

-- This is like a (non-commutative) separating conjunction
_∗_ : Lang n → Lang m → Lang (n + m)
(P ∗ Q) w = Σ (_ × _) λ (u , v) → (w ≡ u ++ v) × P u × Q v

natLang : [ Lang ]
natLang w = ∃ λ n → string (Data.Nat.Show.show n) w

-- -- fix′ : (∀{n} → Lang n → Lang (suc n)) → ∀{m} → Lang (suc m)
-- -- fix′ f {zero} = f empty
-- -- fix′ f {suc m} = f (fix′ f)

≤-lower : .(n ≤ m) → (□ Lang) m → (□ Lang) n
call (≤-lower n≤m A) p<n = call A (Data.Nat.Properties.≤-trans p<n n≤m)

-- ≤-lower⁺ : .(1 ≤ n) → .(n ≤ m) → (□⁺ Lang) m → (□⁺ Lang) n
-- call (≤-lower⁺ {n} {m} 1≤n n≤m A) {p} 1≤p p<n = call A 1≤p (Data.Nat.Properties.≤-trans p<n n≤m)

-- takeS : ℕ → String → String
-- takeS zero s = ""
-- takeS (suc n) s = 

postulate takeFS : ∀ n → suc n < m → FinString m → FinString (suc n)
-- takeFS zero _ _ = emptyFS
-- takeFS (suc n) pf fs = {!!}

-- dropS : ℕ → String → String
-- dropS zero s = s
-- dropS (suc n) s with Data.String.tail s
-- ... | nothing = ""
-- ... | just s′ = dropS n s′

-- postulate length-drop : ∀ n s → length (dropS n s) ≤ length s

-- drop∸ : ∀{A} → (n : ℕ) → Vec {0} A m → Vec A (m ∸ n)
-- drop∸ zero x = x
-- drop∸ (suc n) [] = []
-- drop∸ (suc n) (_ ∷ x) = drop∸ n x

dropFS : ℕ → FinString n → FinString n
len (dropFS n w) = len w ∸ n
s (dropFS n w) = {!dropS n (s fs)!}
len<n (dropFS n w) = {!Data.Nat.Properties.≤-trans (s≤s (length-drop n (s fs))) (pf fs)!}

-- postulate drop-empty : ∀{m pf} → dropFS {m} n (wkFS≤ pf emptyFS) ≡ wkFS≤ pf emptyFS
-- 
_□∗⁺_ : [ □ Lang ⇒ Lang⁺ ⇒ Lang⁺ ]
lang (_□∗⁺_ {n} P Q) w = Σ (Σ ℕ (λ n′ → suc n′ < n)) λ (n , pf) → call P pf (takeFS n pf w) × lang Q (dropFS n w)
nonempty (P □∗⁺ Q) {w} ((n , _) , _ , nonemptyQ) = Data.Nat.Properties.≤-trans (nonempty Q nonemptyQ) (Data.Nat.Properties.m∸n≤m (w .len) n)


postulate _⁺∗□_ : [ Lang⁺ ⇒ □ Lang ⇒ Lang⁺ ]

-- x (_□∗⁺_ {n} P Q) w = Σ (Σ ℕ (λ n′ → suc n′ < n)) λ (n , pf) → call P pf (takeFS n pf w) × x Q (dropFS n w)
-- pf (_□∗⁺_ {zero} P Q) = tt
-- Lang⁺.pf (_□∗⁺_ {suc n} P record { x = x ; pf = pf }) (m , P-empty , Q-empty) = pf (subst x (drop-empty {proj₁ m} {_} {s≤s z≤n}) Q-empty)
-- 
-- -- postulate n≡n+0 : n ≡ n + 0
-- -- 
-- -- _⁺∗□_ : [ Lang⁺ ⇒ □ Lang ⇒ Lang⁺ ]
-- -- x (P ⁺∗□ Q) = subst Lang (sym n≡n+0) (x P ∗ call Q (qux (pf P)))
-- -- pf (_⁺∗□_ {suc n} P Q) w = {!w!}

fix□ : [ □ Lang ⇒ Lang ] → [ □ Lang ]
fix□ f {zero} .call ()
fix□ f {suc m} .call n<sucm = f (≤-lower (≤-pred n<sucm) (fix□ f {m}))

fix : [ □ Lang ⇒ Lang ] → [ Lang ]
fix f = call (fix□ f) Data.Nat.Properties.≤-refl

expr : [ Lang ]
expr = fix λ x → lang (x □∗⁺ (char⁺ '+' ⁺∗□ x)) ∪ char 'x'

-- -- {-# TERMINATING #-}
-- -- expr : Lang
-- -- expr = (expr ∗ (char '+' ∗ expr)) ∪ char 'x'
-- -- 
-- -- x+x : expr "x+x"
-- -- x+x = inj₁ (_ , refl , inj₂ refl , _ , refl , refl , inj₂ refl)
-- -- 
-- -- x+x+xr : expr "x+x+x"
-- -- x+x+xr = inj₁ (_ , refl , inj₂ refl , _ , refl , refl , x+x)
-- -- 
-- -- x+x+xl : expr "x+x+x"
-- -- x+x+xl = inj₁ (_ , refl , x+x , _ , refl , refl , inj₂ refl)
-- -- 
-- -- -- Data-dependent
-- -- 
-- -- ⅀ : (P : Lang) → (∀{w} → P w → Lang) → Lang
-- -- ⅀ P f w = Σ (P w) λ x → f x w
-- -- 
-- -- ℿ : (P : Lang) → (∀{w} → P w → Lang) → Lang
-- -- ℿ P f w = (x : P w) → f x w 
-- -- 
-- -- -- Dependent (non-commutative) separating conjunction (Arjen has also used this)
-- -- _＊_ : (P : Lang) → (∀{w} → P w → Lang) → Lang
-- -- (P ＊ f) w = Σ (_ × _) λ (u , v) → (w ≡ u ++ v) × Σ (P u) λ x → f x v 
-- -- 
-- -- replicateLang : ℕ → Lang → Lang
-- -- replicateLang 0 P = ε
-- -- replicateLang (suc n) P = P ＊ λ _ → replicateLang n P
-- -- 
-- -- ndots : Lang
-- -- ndots = natLang ＊ λ where (n , refl) → replicateLang n (char '.')
-- -- 
-- -- fivedots : ndots "5....."
-- -- fivedots = _ , refl , (5 , refl) ,
-- --   _ , refl , refl ,
-- --   _ , refl , refl ,
-- --   _ , refl , refl ,
-- --   _ , refl , refl ,
-- --   _ , refl , refl ,
-- --   refl
-- -- 
-- -- 
-- 
