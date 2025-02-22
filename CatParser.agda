open import Data.Char using (Char ; _≟_)

data Ob : Set where
  𝟏     : Ob
  _ẋ_   : Ob → Ob → Ob
  -- _⇒_   : Ob → Ob → Ob
  Lang  : Ob

variable A B C : Ob

data K : Ob → Ob → Set where

  -- ev       : K (A ⇒ (B × A)) B
  -- curry    : K (A × B) C → K A (B ⇒ C)
  -- uncurry  : K A (B ⇒ C) → K (A × B) C

  -- fork     : K A B → K A C → K A (B × C)
  exl      : K (A ẋ B) A
  exr      : K (A ẋ B) B

  -- id       : K A A
  compose  : K B C → K A B → K A C

  ∅        : K A Lang
  ε        : K A Lang
  _∪_      : K A Lang → K A Lang → K A Lang
  _∗_      : K A Lang → K A Lang → K A Lang
  `_       : Char → K A Lang
  μ        : K (Lang ẋ A) Lang → K A Lang

-- const : K 𝟏 (A ⇒ (B ⇒ A))
-- const = curry (compose (curry exl) exr)

expr : K 𝟏 Lang
expr = μ ((` 'x') ∪ (exl ∗ ((` '+') ∗ exl)))

-- mutual recursion of expressions and statements
lang : K 𝟏 Lang
lang
  = μ ((` 'x')
    ∪ ((exl ∗ ((` '+') ∗ exl))
    ∪ ((` '{') ∗ (μ (((` '!') ∗ compose exl exr)
                    ∪ (exl ∗ ((` ';') ∗ exl)))
               ∗ (` '}')))))

open import Data.List
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Function

data 𝟙 : Set₁ where
  one : 𝟙

String : Set
String = List Char

Ob⟦_⟧ : Ob → Set₁
Ob⟦ 𝟏 ⟧ = 𝟙 
Ob⟦ o ẋ o₁ ⟧ = Ob⟦ o ⟧ × Ob⟦ o₁ ⟧
Ob⟦ Lang ⟧ = String → Set

K⟦_⟧ : K A B → Ob⟦ A ⟧ → Ob⟦ B ⟧

data Fix (φ : K (Lang ẋ A) Lang) (x : Ob⟦ A ⟧) (w : String) : Set where
  step : K⟦ φ ⟧ (Fix φ x , x) w → Fix φ x w 

K⟦ exl ⟧ (π₁ , π₂) = π₁ 
K⟦ exr ⟧ (π₁ , π₂) = π₂
K⟦ compose φ ψ ⟧ x = K⟦ φ ⟧ (K⟦ ψ ⟧ x)
K⟦ ∅ ⟧ _ _ = ⊥
K⟦ ε ⟧ _ w = w ≡ []
K⟦ φ ∪ ψ ⟧ x w = K⟦ φ ⟧ x w ⊎ K⟦ ψ ⟧ x w
K⟦ φ ∗ ψ ⟧ x w = ∃[ u ] ∃[ v ] w ≡ u ++ v × K⟦ φ ⟧ x u × K⟦ ψ ⟧ x v
K⟦ ` c ⟧ x w = w ≡ c ∷ []
K⟦ μ φ ⟧ x = K⟦ φ ⟧ (Fix φ x , x)

open import Relation.Nullary.Decidable as Dec
import Function.Properties.Equivalence as ⇔
open import Function.Bundles

Parser : (String → Set) → Set
Parser L = (w : String) → Dec (L w)

_∗-parse_ : {P Q : String → Set} → Parser P → Parser Q → Parser (λ w → ∃[ u ] ∃[ v ] w ≡ u ++ v × P u × Q v)
(φ ∗-parse ψ) [] = Dec.map (mk⇔ (λ x → [] , [] , refl , x) (λ { ([] , [] , refl , x) → x })) (φ [] ×-dec ψ [])
(φ ∗-parse ψ) (c ∷ w) = Dec.map
  {!   !}
  ((φ [] ×-dec ψ (c ∷ w)) ⊎-dec ((φ ∘ (c ∷_)) ∗-parse ψ) w )

DecOb : ∀ o → Ob⟦ o ⟧ → Set
DecOb 𝟏 one = ⊤
DecOb (o ẋ o₁) (φ , ψ) = DecOb o φ × DecOb o₁ ψ
DecOb Lang L = Parser L

parseK : (f : K A B) → {x : Ob⟦ A ⟧} → DecOb A x → DecOb B (K⟦ f ⟧ x)
parseK exl (x , _) = x
parseK exr (_ , x) = x
parseK (compose φ ψ) x = parseK φ (parseK ψ x)
parseK ∅ _ w = no λ ()
parseK ε _ [] = yes refl
parseK ε _ (_ ∷ _) = no λ ()
parseK (φ ∪ ψ) x w = parseK φ x w ⊎-dec parseK ψ x w
parseK (φ ∗ ψ) x = parseK φ x ∗-parse parseK ψ x
parseK (` c) _ [] = no λ ()
parseK (` c) _ (x ∷ []) = Dec.map (mk⇔ (λ { refl → refl }) λ { refl → refl }) (c ≟ x)
parseK (` c) _ (_ ∷ _ ∷ _) = no λ ()
parseK (μ φ) x = parseK φ ((λ w → Dec.map (mk⇔ step (λ { (step x) → x })) (parseK (μ φ) x w)) , x)