open import Data.Char hiding (_≤_ ; _<_)
open import Data.List hiding ([_] ; concat) renaming (length to List-length ; replicate to List-replicate)
-- open import Data.Empty
open import Data.Empty.Polymorphic
open import Data.Unit
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Sum
open import Data.Product
open import Data.Bool hiding (_≤_ ; _<_)
open import Data.Nat hiding (_*_)
open import Data.List.Relation.Unary.All hiding (fromList) renaming (toList to All-toList)
open import Data.String using (toList)
import Data.Nat.Show
open import Function using (id ; _∘_ ; const)
import Data.List.Properties
import Data.Nat.Properties
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Vec hiding ([_] ; toList) renaming (length to Vec-length ; _++_ to _++V_)

variable n n′ m m′ : ℕ

data Proxy (n : ℕ) : Set where
  mkProxy : Proxy n

[_] : (ℕ → Set₁) → Set₁
[ P ] = ∀{n} → P n

String : Set
String = List Char

-- The proxy is just to help inference
Lang : ℕ → Set₁
Lang n = .(Proxy n) → String → Set

empty : [ Lang ]
empty _ _ = ⊥

universe : [ Lang ]
universe _ _ = ⊤

ε : [ Lang ]
ε _ w = w ≡ []

char : Char → [ Lang ]
char c _ w = w ≡ c ∷ []

string : (s′ : String) → [ Lang ]
string s′ _ w = w ≡ s′

infixr 20 _⇒_

_⇒_ : (ℕ → Set₁) → (ℕ → Set₁) → (ℕ → Set₁)
(P ⇒ Q) x = P x → Q x

_∪_ : [ Lang ⇒ Lang ⇒ Lang ]
(P ∪ Q) pf w = P pf w ⊎ Q pf w

_∩_ : [ Lang ⇒ Lang ⇒ Lang ]
(P ∩ Q) pf w = P pf w × Q pf w

infixr 22 _*_

-- dependent sequencing
_*_ : ∀{n} → (P : Lang n) → (∀ .{pf} {w} → P pf w → Lang n) → Lang n
(P * f) pf w = Σ (_ × _) λ (u , v) → (w ≡ u ++ v) × (Σ (P pf u) λ x → f x pf v)

infixr 22 _⋆_
infixr 20 _∪_

-- non-dependent sequencing
_⋆_ : [ Lang ⇒ Lang ⇒ Lang ]
P ⋆ Q = P * λ _ → Q 

natLang : [ Lang ]
natLang _ w = ∃ λ n → w ≡ Data.String.toList (Data.Nat.Show.show n)

fix : ∀{A : Set} → A → (∀{n} → (A → Lang n) → (A → Lang n)) → [ Lang ]
fix _ f {0} = empty
fix x f {suc n} = f (λ x _ → fix x f {n} mkProxy) x

guard : Bool → [ Lang ]
guard false = empty
guard true = ε

expr : [ Lang ]
expr = fix true λ f b → guard b ⋆ f false ⋆ char '+' ⋆ f true ∪ char 'x'

-- To prove a string is in a language, we just have to find a step
-- number and prove the language at that step contains the string.
_∈_ : String → [ Lang ] → Set
w ∈ P = ∃ λ n → P {n} mkProxy w

x+x+x : Data.String.toList "x+x+x" ∈ expr
x+x+x = 3 , inj₁ (([] , Data.String.toList "x+x+x") , (refl , (refl , (('x' ∷ [] , Data.String.toList "+x+x") , (refl , ((inj₂ refl) , (toList "+" , toList "x+x") , (refl , (refl , (inj₁ (([] , toList "x+x") , (refl , (refl , (toList "x" , toList "+x") , (refl , ((inj₂ refl) , ((toList "+" , toList "x") , (refl , (refl , (inj₂ refl))))))))))))))))))
-- x+x+x = 3 , inj₁ (("x" , "+x+x") , (refl , refl , (("+" , "x+x") , (refl , (refl , (inj₁ (("x" , "+x") , (refl , (refl , (("+" , "x") , (refl , (refl , (inj₂ refl)))))))))))))
-- impossible to do it the other way around:
-- x+x+x = 2 , inj₁ (("x+x" , "+x") , (refl , {!!} , ("+" , "x") , (refl , refl , (inj₂ refl))))

-- We can prove interesting things about our languages, for example that they are unambiguous:

-- Ambiguity should be obvious as long as the step-indexed results are
-- monotonically increasing with the step number.  If that is not the
-- case then we have a choice:
--
--  1. all proofs need to be the same regardless of step number, or
--  2. the proofs only need to be the same for each step number pointwise
--
-- We chose 2, because we know then that at least the type of the
-- proofs we consider will always be equal.
--
-- An example where it matters is the barber paradox language, which
-- has different proofs at each (even) step number. So, it would be
-- considered ambiguous under the former and unambiguous under the
-- latter definition.
unambiguous : [ Lang ] → Set
unambiguous P = ∀{w} → (x y : w ∈ P) → proj₁ x ≡ proj₁ y → x ≡ y

unambiguousEmpty : unambiguous empty
unambiguousEmpty ()

unambiguousUniverse : unambiguous universe
unambiguousUniverse (_ , tt) (_ , tt) refl = refl

unambiguousε : unambiguous ε
unambiguousε (_ , refl) (_ , refl) refl = refl

unambiguousChar : ∀{c} → unambiguous (char c)
unambiguousChar (_ , refl) (_ , refl) refl = refl

unambiguousString : ∀{s} → unambiguous (string s)
unambiguousString (_ , refl) (_ , refl) refl = refl

unambiguous∩ : ∀{P Q : [ Lang ]} → unambiguous P → unambiguous Q → unambiguous (P ∩ Q)
unambiguous∩ uaP uaQ (n , x₁ , y₁) (m , x₂ , y₂) refl with uaP (n , x₁) (n , x₂) refl | uaQ (n , y₁) (n , y₂) refl
... | refl | refl = refl

-- Not true:
-- unambiguous* : ∀{P : [ Lang ]} {f : ∀ {n} .{pf} {w} → P {n} pf w → Lang n} → unambiguous P → (∀ {w} (x : ∀{n} .{pf′} → P {n} pf′ w) → unambiguous (λ {n} → f {n} {mkProxy} {w} x)) → unambiguous (P * f) 
-- unambiguous* uaP uaQ (n , (u₁ , v₁) , refl , Pu₁ , fv₁) (n , (u₂ , v₂) , fst , Pu₂ , fv₂) refl with uaP (n , Pu₁) (n , {!Pu₂!}) refl
-- ... | a = {!!}
-- counterexample: natLang * λ _ → natLang matches "123" with both "12","3" and "1","23"

postulate ℕshowInjective : ∀ x y → toList (Data.Nat.Show.show x) ≡ toList (Data.Nat.Show.show y) → x ≡ y

unambiguousNatLang : unambiguous natLang
unambiguousNatLang (_ , n , refl) (_ , m , pf) refl with ℕshowInjective n m pf | pf
... | refl | refl = refl

unambiguousExpr : unambiguous expr
unambiguousExpr (suc (suc n) , inj₁ ((.[] , .(('x' ∷ []) ++ [])) , refl , refl , (.('x' ∷ []) , .[]) , refl , inj₂ refl , (.('+' ∷ []) , v) , () , refl , snd)) (.(suc (suc n)) , inj₂ refl) refl
unambiguousExpr (suc (suc n) , inj₁ ((.[] , .(('x' ∷ []) ++ ('+' ∷ []) ++ snd₂)) , refl , refl , (.('x' ∷ []) , .(('+' ∷ []) ++ snd₂)) , refl , inj₂ refl , (.('+' ∷ []) , snd₂) , refl , refl , snd)) (.(suc (suc n)) , inj₁ ((.[] , .([] ++ ('x' ∷ []) ++ ('+' ∷ []) ++ snd₂)) , refl , refl , (.('x' ∷ []) , .([] ++ ('+' ∷ []) ++ snd₂)) , refl , inj₂ refl , (.('+' ∷ []) , .([] ++ snd₂)) , refl , refl , snd₁)) refl = {!snd₁!}
unambiguousExpr (suc (suc n) , inj₂ refl) (.(suc (suc n)) , inj₁ ((.[] , .(('x' ∷ []) ++ ('+' ∷ []) ++ v″)) , () , refl , (.('x' ∷ []) , .(('+' ∷ []) ++ v″)) , refl , inj₂ refl , (.('+' ∷ []) , v″) , refl , refl , snd)) refl
unambiguousExpr (suc zero , inj₂ refl) (.1 , inj₂ refl) refl = refl
unambiguousExpr (suc (suc n) , inj₂ refl) (.(suc (suc n)) , inj₂ refl) refl = refl

-- The language that contains all things that are not in the previous
-- iteration of the language. The 0th iteration is always empty, so
-- the 1st contains everything and the 2nd is empty again etc.
barber : [ Lang ]
barber = fix tt λ where f tt pf w → f tt pf w → ⊥

barber1 : ∀ {s} → s ∈ barber
barber1 = 1 , λ ()

barber3 : ∀ {s} → s ∈ barber
barber3 = 3 , λ x → x id

