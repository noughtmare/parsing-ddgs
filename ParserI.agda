open import Data.Char
open import Data.List
open import Data.Empty
open import Data.Product
open import Data.Sum as Sum
open import Data.Unit hiding (_≟_)
open import Relation.Nullary.Decidable
open import Level hiding (zero ; suc)
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Fin hiding (_≟_)
open import Data.Nat hiding (_*_ ; _≟_)

String : Set
String = List Char

Lang : Set₁
Lang = String → Set

variable
    ℓ ℓ′ : Level
    A : Set ℓ
    c : Char

-- semantics
module ◇ where
    ν : Lang → Set
    ν L = L []

    δ : Char → Lang → Lang
    (δ c L) w = L (c ∷ w)

    ∅ : Lang
    ∅ _ = ⊥

    ε : Lang
    ε w = w ≡ []

    ‵_ : Char → Lang
    (‵ c) w = w ≡ c ∷ []

    _·_ : {A : Set} → Dec A → Lang → Lang
    _·_ {A} _ P w = A × P w 

    _∪_ : Lang → Lang → Lang
    (P ∪ Q) w = P w ⊎ Q w

    _*_ : Lang → Lang → Lang
    (P * Q) w = ∃[ u ] ∃[ v ] w ≡ u ++ v × P u × Q v

-- syntax
data Exp : Set₁ where
  ∅ : Exp
  ε : Exp
  ‵_ : (c : Char) → Exp
  _·_ : {A : Set} → Dec A → Exp → Exp
  _∪_ : Exp → Exp → Exp
  _*_ : Exp → Exp → Exp
  I : Exp
  μ : Exp → Exp

variable
    n m : ℕ
    L : Lang
    w : String
    e e₀ e′ : Exp

-- mapping syntax onto semantics
⟦_⟧₁ : Exp → Lang → Lang

data ⟦_⟧ (e : Exp) : Lang where
  ∞ : ⟦ e ⟧₁ ⟦ e ⟧ w → ⟦ e ⟧ w

⟦ ∅ ⟧₁ _ = ◇.∅
⟦ ε ⟧₁ _ = ◇.ε
⟦ ‵ c ⟧₁ _ = ◇.‵ c
⟦ x · e ⟧₁ L = x ◇.· ⟦ e ⟧₁ L
⟦ e ∪ e₁ ⟧₁ L = ⟦ e ⟧₁ L ◇.∪ ⟦ e₁ ⟧₁ L
⟦ e * e₁ ⟧₁ L = ⟦ e ⟧₁ L ◇.* ⟦ e₁ ⟧₁ L
⟦ I ⟧₁ L = L
⟦ μ e ⟧₁ _ = ⟦ e ⟧

! : ⟦ e ⟧ w → ⟦ e ⟧₁ ⟦ e ⟧ w
! (∞ x) = x

-- substitution
sub : Exp → Exp → Exp
sub e₀ ∅ = ∅
sub e₀ ε = ε
sub e₀ (‵ c) = ‵ c
sub e₀ (x · e) = x · sub e₀ e
sub e₀ (e ∪ e₁) = sub e₀ e ∪ sub e₀ e₁
sub e₀ (e * e₁) = sub e₀ e * sub e₀ e₁
sub e₀ I = e₀
sub _ (μ e) = μ e

-- nullability

νe∅→νee : (e : Exp) → ◇.ν (⟦ e ⟧₁ ◇.∅) → ◇.ν (⟦ e ⟧₁ ⟦ e′ ⟧)
νe∅→νee ε x = x
νe∅→νee (x₁ · e) (x , y) = x , νe∅→νee e y
νe∅→νee (e ∪ e₁) (inj₁ x) = inj₁ (νe∅→νee e x)
νe∅→νee (e ∪ e₁) (inj₂ y) = inj₂ (νe∅→νee e₁ y)
νe∅→νee (e * e₁) ([] , [] , refl , x , y) = [] , [] , refl , νe∅→νee e x , νe∅→νee e₁ y
νe∅→νee I ()
νe∅→νee (μ e) x = x

νee→νe∅′ : (e : Exp) → ◇.ν (⟦ e ⟧₁ ⟦ e′ ⟧) → ◇.ν (⟦ e ⟧₁ ◇.∅) ⊎ ◇.ν (⟦ e′ ⟧₁ ◇.∅)
νee→νe∅′ ε x = inj₁ x
νee→νe∅′ (_ · e) (x , y) = Sum.map₁ (x ,_) (νee→νe∅′ e y)
νee→νe∅′ (e ∪ e₁) (inj₁ x) = Sum.map₁ inj₁ (νee→νe∅′ e x)
νee→νe∅′ (e ∪ e₁) (inj₂ y) = Sum.map₁ inj₂ (νee→νe∅′ e₁ y)
νee→νe∅′ (e * e₁) ([] , [] , refl , x , y) with νee→νe∅′ e x | νee→νe∅′ e₁ y
... | inj₁ x | inj₁ y = inj₁ ([] , [] , refl , x , y)
... | inj₂ x | _ = inj₂ x
... | inj₁ _ | inj₂ y = inj₂ y
νee→νe∅′ {e′ = e} I (∞ x) = inj₂ (reduce (νee→νe∅′ e x))
νee→νe∅′ (μ e) x = inj₁ x

νee→νe∅ : (e : Exp) → ◇.ν (⟦ e ⟧₁ ⟦ e ⟧) → ◇.ν (⟦ e ⟧₁ ◇.∅)
νee→νe∅ e x = reduce (νee→νe∅′ e x)

ν₁ : (e : Exp) → Dec (◇.ν L) → Dec (◇.ν (⟦ e ⟧₁ L))
ν₁ ∅ _ = no λ ()
ν₁ ε _ = yes refl
ν₁ (‵ c) _ = no λ ()
ν₁ (x · e) νe₀ = x ×-dec ν₁ e νe₀
ν₁ (e ∪ e₁) νe₀ = ν₁ e νe₀ ⊎-dec ν₁ e₁ νe₀
ν₁ (e * e₁) νe₀ = map′ (λ x → [] , [] , refl , x) (λ { ([] , [] , refl , x) → x }) (ν₁ e νe₀ ×-dec ν₁ e₁ νe₀)
ν₁ I νe₀ = νe₀
ν₁ (μ e) νe₀ = map′ (∞ ∘ νe∅→νee e) (νee→νe∅ e ∘ !) (ν₁ {L = ◇.∅} e (no λ ()))

ν : (e : Exp) → Dec (◇.ν ⟦ e ⟧)
ν e = ν₁ {L = ◇.∅} (μ e) (no λ ())

-- syntactic derivative

δ₁ : (c : Char) → (Σ[ e₀ ∈ Exp ] Dec (◇.ν ⟦ e₀ ⟧)) → Exp → Exp
δ₁ c _ ∅ = ∅
δ₁ c _ ε = ∅
δ₁ c _ (‵ c′) with c ≟ c′
... | yes _ = ε
... | no _ = ∅
δ₁ c e₀ (x · e) = x · δ₁ c e₀ e
δ₁ c e₀ (e ∪ e₁) = δ₁ c e₀ e ∪ δ₁ c e₀ e₁
δ₁ c (e₀ , νe₀) (e * e₁) = (δ₁ c (e₀ , νe₀) e * sub (μ e₀) e₁) ∪ (ν₁ {L = ⟦ _ ⟧} e νe₀ · δ₁ c (e₀ , νe₀) e₁)
δ₁ c e₀ I = I
δ₁ c _ (μ e) = μ (δ₁ c (e , ν e) e)

δ : Char → Exp → Exp
δ c e = δ₁ c (e , ν e) e

-- proving the correctness of our derivative

δ-sound-helper : (e : Exp) → ⟦ sub (μ e₀) e ⟧₁ ⟦ δ c e₀ ⟧ w → ⟦ e ⟧₁ ⟦ e₀ ⟧ w
δ-sound-helper ε x = x
δ-sound-helper (‵ c) x = x
δ-sound-helper (_ · e) (x , y) = x , δ-sound-helper e y
δ-sound-helper (e ∪ e₁) (inj₁ x) = inj₁ (δ-sound-helper e x)
δ-sound-helper (e ∪ e₁) (inj₂ y) = inj₂ (δ-sound-helper e₁ y)
δ-sound-helper (e * e₁) (u , v , refl , x , y) = u , v , refl , δ-sound-helper e x , δ-sound-helper e₁ y
δ-sound-helper {e₀ = e} I x = x
δ-sound-helper (μ e) x = x

δ-complete-helper : (e : Exp) → ⟦ e ⟧₁ ⟦ e₀ ⟧ w → ⟦ sub (μ e₀) e ⟧₁ ⟦ δ c e₀ ⟧ w
δ-complete-helper ε x = x
δ-complete-helper (‵ c) x = x
δ-complete-helper (_ · e) (x , y) = x , δ-complete-helper e y
δ-complete-helper (e ∪ e₁) (inj₁ x) = inj₁ (δ-complete-helper e x)
δ-complete-helper (e ∪ e₁) (inj₂ y) = inj₂ (δ-complete-helper e₁ y)
δ-complete-helper (e * e₁) (u , v , refl , x , y) = u , v , refl , δ-complete-helper e x , δ-complete-helper e₁ y
δ-complete-helper {e₀ = e} {w = w} {c = c} I (∞ x) = ∞ x
δ-complete-helper (μ e) x = x

δ-sound : ⟦ δ c e ⟧ w → ◇.δ c ⟦ e ⟧ w

δ-sound′ : ∀{νe₀} (e : Exp) → ⟦ δ₁ c (e₀ , νe₀) e ⟧₁ ⟦ δ c e₀ ⟧ w → ◇.δ c (⟦ e ⟧₁ ⟦ e₀ ⟧) w
δ-sound′ ∅ ()
δ-sound′ ε ()
δ-sound′ {c = c} (‵ c′) x with c ≟ c′
δ-sound′ {c = c} (‵ c′) refl | yes refl = refl
δ-sound′ {c = c} (‵ c′) () | no _
δ-sound′ (x₁ · e) (x , y) = x , δ-sound′ e y
δ-sound′ (e ∪ e₁) (inj₁ x) = inj₁ (δ-sound′ e x)
δ-sound′ (e ∪ e₁) (inj₂ y) = inj₂ (δ-sound′ e₁ y)
δ-sound′ {c = c} (e * e₁) (inj₁ (u , v , refl , x , y)) = c ∷ u , v , refl , δ-sound′ e x , δ-sound-helper e₁ y
δ-sound′ {c = c} {w = w} (e * e₁) (inj₂ (x , y)) = [] , c ∷ w , refl , x , δ-sound′ e₁ y
δ-sound′ {e₀ = e} I x = δ-sound x
δ-sound′ (μ e) (∞ x) = ∞ (δ-sound′ e x)

δ-sound {e = e} (∞ x) = ∞ (δ-sound′ e x)

δ-complete : ◇.δ c ⟦ e ⟧ w → ⟦ δ c e ⟧ w

δ-complete′ : (e : Exp) → ⊤ → ◇.δ c (⟦ e ⟧₁ ⟦ e₀ ⟧) w → ⟦ δ₁ c (e₀ , ν e₀) e ⟧₁ ⟦ δ c e₀ ⟧ w
δ-complete′ {c = c} (‵ c′) f refl with c ≟ c′
... | yes refl = refl
... | no ¬x = ¬x refl
δ-complete′ (_ · e) f (x , y) = x , δ-complete′ e f y
δ-complete′ (e ∪ e₁) f (inj₁ x) = inj₁ (δ-complete′ e f x)
δ-complete′ (e ∪ e₁) f (inj₂ y) = inj₂ (δ-complete′ e₁ f y)
δ-complete′ (e * e₁) f (c ∷ u , v , refl , x , y) = inj₁ (u , v , refl , δ-complete′ e f x , δ-complete-helper e₁ y)
δ-complete′ (e * e₁) f ([] , c ∷ w , refl , x , y) = inj₂ (x , δ-complete′ e₁ f y)
δ-complete′ {e₀ = e} I f x = δ-complete x
δ-complete′ (μ e) f (∞ x) = ∞ (δ-complete′ e tt x)

δ-complete {e = e} (∞ x) = ∞ (δ-complete′ e tt x)

-- putting it all together

parse : (e : Exp) (w : String) → Dec (⟦ e ⟧ w)
parse e [] = ν e
parse e (c ∷ w) = map′ δ-sound δ-complete (parse (δ c e) w)
