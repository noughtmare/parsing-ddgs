{-# OPTIONS --no-import-sorts #-} --safe

open import Agda.Primitive renaming (Set to Type ; Setω to Typeω)

import Function.Properties.Equivalence as ⇔
import Data.Bool as Bool
open Bool using (_∧_ ; _∨_)
open import Data.Bool using (Bool ; true ; false)
open import Data.Char using (Char ; _≟_)
open import Data.List as List hiding (foldl)
open import Data.Empty
open import Data.Product as Prod
open import Data.Sum as Sum
open import Data.Unit hiding (_≟_)
open import Relation.Nullary.Decidable as Dec hiding (from-yes ; from-no)
open import Relation.Nullary.Reflects
open import Level hiding (zero ; suc)
open import Relation.Binary.PropositionalEquality
open import Function hiding (_⟶_ ; typeOf)
open import Data.Fin hiding (_≟_)
open import Data.Nat hiding (_*_ ; _≟_ ; _!)
open import Relation.Nullary.Negation
import Data.String as String
open import Agda.Builtin.FromString
open import Relation.Binary using (_⇒_)

-- Utility & background definitions

typeOf : {A : Type} → Dec A → Type
typeOf {A = A} _ = A

transport : ∀{A B : Type} → A ≡ B → A → B
transport refl x = x

≡→⇔ : ∀ {A B : Type} → A ≡ B → A ⇔ B
≡→⇔ refl = ⇔.refl

lift⊎₂ : ∀{A B C D : Type} → (A → B → C) → A ⊎ D → B ⊎ D → C ⊎ D
lift⊎₂ f (inj₁ x) (inj₁ y) = inj₁ (f x y)
lift⊎₂ _ (inj₁ _) (inj₂ y) = inj₂ y
lift⊎₂ _ (inj₂ x) _ = inj₂ x

String : Type
String = List Char
instance
  string : IsString String 
  IsString.Constraint string _ = ⊤
  IsString.fromString string xs = String.toList xs

foldl : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B → B) → B → List A → B
foldl k z [] = z
foldl k z (c ∷ w) = foldl k (k c z) w

variable
    ℓ ℓ′ : Level
    A : Type ℓ
    c : Char
    w : String

--------------------------------------------------------------------------------

-- Semantics
module ◇ where
    -- Language
    Lang : Type₁
    Lang = String → Type

    variable L : Lang

    -- The empty language, contains nothing
    ∅ : Lang
    ∅ _ = ⊥

    -- The epsilon language, contains only the empty string
    ε : Lang
    ε w = w ≡ []

    _∪_ : Lang → Lang → Lang
    (P ∪ Q) w = P w ⊎ Q w

    _*_ : Lang → Lang → Lang
    (P * Q) w = ∃[ u ] ∃[ v ] w ≡ u ++ v × P u × Q v

    -- A single character language, contains only the string
    -- consisting of the given character.
    ‵_ : Char → Lang
    (‵ c) w = w ≡ c ∷ []

    -- Scalar multiplication. This one is a bit odd. It allows
    -- you to inject 
    _·_ : Type → Lang → Lang
    (A · P) w = A × P w 

    infix 22 ‵_
    infixr 20 _∪_
    infixr 21 _*_

    -- We can use the languages, but we have to write our proofs
    -- manually:

    abc : Lang
    abc = ‵ 'a' ∪ ‵ 'b' ∪ ‵ 'c'

    b∈abc : abc ('b' ∷ [])
    b∈abc = inj₂ (inj₁ refl)

    -- -- Note that we have to be clever to define recursive languages.
    -- fix : (Lang → Lang) → Lang
    -- fix f w = ∃[ n ] go n w where
    --   go : ℕ → Lang
    --   go zero = ∅
    --   go (suc n) = f (go n)

    data expr : Lang where
      var : (‵ 'x') w → expr w
      plus : (expr * (‵ '+') * expr) w → expr w

    -- expr : Lang
    -- expr = fix (λ expr → ‵ 'x' ∪ expr * ‵ '+' * expr)

    x+x+xᵣ x+x+xₗ {- x+x+x₄ -} : expr "x+x+x"
    -- x+x+xᵣ = 3 , inj₂ (_ , _ , refl , inj₁ refl , _ , _ , refl , refl , inj₂ (_ , _ , refl , inj₁ refl , _ , _ , refl , refl , inj₁ refl))
    x+x+xᵣ = plus (_ , _ , refl , var refl , _ , _ , refl , refl , plus (_ , _ , refl , var refl , _ , _ , refl , refl , var refl))

    -- Due to our definition of languages as 'String → Type', we can
    -- differentiate between the right associative parse (above) and
    -- the left associative parse (below).

    -- x+x+xₗ = 3 , inj₂ (_ , _ , refl , inj₂ (_ , _ , refl , inj₁ refl , _ , _ , refl , refl , inj₁ refl) , _ , _ , refl , refl , inj₁ refl)
    x+x+xₗ = plus (_ , _ , refl , plus (_ , _ , refl , var refl , _ , _ , refl , refl , var refl) , _ , _ , refl , refl , var refl)

    -- Unfortunately, defining infinite languages using 'fix' also
    -- introduces redundant parses:
    -- x+x+x₄ = 4 , inj₂ (_ , _ , refl , inj₁ refl , _ , _ , refl , refl , inj₂ (_ , _ , refl , inj₁ refl , _ , _ , refl , refl , inj₁ refl))
    -- This is not ideal and would complicate our proofs. Later we
    -- will use a different way to encode infinite languages.

    -- Since we can use the full power of the Agda language, proving
    -- language inclusion like this is undecidable.

    str : String → Lang
    str w′ w = w ≡ w′

    -- BNF: <brackets> ::= ε | [ <brackets> ] | <brackets> <brackets>
    data brackets : Lang where
      zero : brackets []
      one : brackets w → brackets ("[" ++ w ++ "]")
      two : {u v : String} → brackets u → brackets v → brackets (u ++ v)

    [[][[]]][] : brackets "[[][[]]][]"
    [[][[]]][] = two (one (two (one zero) (one (one zero)))) (one zero)

    -- This stuff should be explained later:
    ν : Lang → Type
    ν L = L []

    δ : Char → Lang → Lang
    (δ c L) w = L (c ∷ w)

    -- BNF:
    -- <sentence>  ::= <subject> <verb> <object>
    -- <subject>   ::= The cat | The dog
    -- <verb>      ::= played with | ate
    -- <object>    ::= the <adjective> yarn ball. | my homework
    -- <adjective> ::= ε | big | red

    adjective subject verb object sentence : Lang
    adjective = ε ∪ str "big " ∪ str "red "
    subject = str "The cat " ∪ str "The dog "
    verb = str "played with " ∪ str "ate "
    object = str "the " * adjective * str "yarn ball." ∪ str "my homework."
    sentence = subject * verb * object

    example₁ : sentence "The cat played with the red yarn ball."
    example₁ = "The cat " , _ , refl , inj₁ refl , "played with " , _ , refl , inj₁ refl , inj₁ ("the " , _ , refl , refl , "red " , "yarn ball." , refl , inj₂ (inj₂ refl) , refl)


    νfoldlδL≡L : ∀ w → ν (foldl δ L w) ≡ L w
    νfoldlδL≡L [] = refl
    νfoldlδL≡L (_ ∷ w) = νfoldlδL≡L w

    𝒟 : String → Lang → Lang
    (𝒟 w′ L) w = L (w′ ++ w) 

    example₂ : (𝒟 "The cat " sentence) w ⇔ (verb * object) w
    example₂ = mk⇔
      (λ where
        (_ , _ , refl , inj₁ refl , x) → x
        (_ , _ , () , inj₂ refl , _))
      λ x → _ , _ , refl , inj₁ refl , x

    example₃ : (𝒟 "played with " (verb * object)) w ⇔ object w
    example₃ = mk⇔
      (λ where
        (_ , _ , refl , inj₁ refl , x) → x
        (_ , _ , () , inj₂ refl , _))
      λ x → _ , _ , refl , inj₁ refl , x

    example₄ : (𝒟 "the " object) w ⇔ (adjective * str "yarn ball.") w
    example₄ = mk⇔
      (λ where
        (inj₁ (_ , _ , refl , refl , x)) → x)
      λ x → inj₁ (_ , _ , refl , refl , x)

    example₅ : (𝒟 "red " (adjective * str "yarn ball.")) w ⇔ (str "yarn ball.") w
    example₅ = mk⇔
      (λ where
        (_ , _ , refl , inj₂ (inj₂ refl) , x) → x
        (_ , _ , () , inj₂ (inj₁ refl) , _)
        (_ , _ , refl , inj₁ refl , ()))
      λ x → _ , _ , refl , inj₂ (inj₂ refl) , x

    example₆ : (𝒟 "yarn ball." (str "yarn ball.")) w ⇔ ε w
    example₆ = mk⇔
      (λ where refl → refl)
      λ where refl → refl

    example₇ : ν ε
    example₇ = refl

    νfoldl𝒟L≡L : ∀ ws → ν (foldl 𝒟 L ws) ≡ L (concat ws)
    νfoldl𝒟L≡L [] = refl
    νfoldl𝒟L≡L (_ ∷ ws) = νfoldl𝒟L≡L ws

    open Equivalence

    example₈ : sentence "The cat played with the red yarn ball."
    example₈ = transport (νfoldl𝒟L≡L {L = sentence} ("The cat " ∷ "played with " ∷ "the " ∷ "red " ∷ "yarn ball." ∷ [])) (example₂ .from (example₃ .from (example₄ .from (example₅ .from (example₆ .from example₇)))))

    variable P Q R S : Lang

    _⟶_ : Lang → Lang → Type
    P ⟶ Q = ∀{w} → P w → Q w

    record _⟷_ (P Q : Lang) : Type where
        constructor mk⟷
        field
            to : P ⟶ Q
            from : Q ⟶ P
    open _⟷_

    ⟷→⇔ : P ⟷ Q → ∀{w} → P w ⇔ Q w
    ⟷→⇔ bi = mk⇔ (bi .to) (bi .from)
    ⟷cong : ∀{P Q} {f : Lang → Lang} → (∀{P Q} → (P ⟶ Q) → f P ⟶ f Q) → P ⟷ Q → f P ⟷ f Q
    ⟷cong fmap bi = mk⟷ (fmap (bi .to)) (fmap (bi .from))
    ⟷cong₂ : ∀{P Q R S} {f : Lang → Lang → Lang} → (∀{P Q R S} → (P ⟶ R) → (Q ⟶ S) → f P Q ⟶ f R S) → P ⟷ R → Q ⟷ S → f P Q ⟷ f R S
    ⟷cong₂ fmap₂ bi₁ bi₂ = mk⟷ (fmap₂ (bi₁ .to) (bi₂ .to)) (fmap₂ (bi₁ .from) (bi₂ .from))

    ∪-map : (P ⟶ Q) → (R ⟶ S) → (P ∪ R) ⟶ (Q ∪ S)
    ∪-map f g (inj₁ x) = inj₁ (f x)
    ∪-map f g (inj₂ y) = inj₂ (g y)

    *-map₁ : (P ⟶ Q) → P * R ⟶ Q * R 
    *-map₁ f (_ , _ , refl , x , y) = _ , _ , refl , f x , y

    *-map : (P ⟶ Q) → (R ⟶ S) → P * R ⟶ Q * S 
    *-map f g (_ , _ , refl , x , y) = _ , _ , refl , f x , g y

    ·-map : (P ⟶ Q) → (A · P) ⟶ (A · Q)
    ·-map f = Prod.map₂ f

    ⟷refl : P ⟷ P
    ⟷refl = mk⟷ id id

    ⟷trans : P ⟷ Q → Q ⟷ R → P ⟷ R
    ⟷trans bi₁ bi₂ = mk⟷ (bi₂ .to ∘ bi₁ .to) (bi₁ .from ∘ bi₂ .from)


    ν* : (ν P × ν Q) ⇔ ν (P * Q)
    ν* = mk⇔ (λ x → [] , [] , refl , x) (λ { ([] , [] , refl , x) → x })

    δε : ∅ ⟷ δ c ε
    δε .to ()
    δε .from ()

    δ‵ : ∀{c c₁} → ((c ≡ c₁) · ε) ⟷ δ c (‵ c₁)
    δ‵ .to (refl , refl) = refl
    δ‵ .from refl = refl , refl

    δ* : (δ c P * Q ∪ (ν P · δ c Q)) ⟷ δ c (P * Q)
    δ* = mk⟷
        (λ where
            (inj₁ (_ , _ , refl , x)) → _ , _ , refl , x
            (inj₂ x) → [] , _ , refl , x)
        (λ where
            (_ ∷ _ , _ , refl , x) → inj₁ (_ , _ , refl , x)
            ([] , _ , refl , x) → inj₂ x)


open ◇ using (Lang)

--------------------------------------------------------------------------------

module ◆ where

  -- Definitions


  variable P Q R S : Lang

  -- ⟦_⟧₁ : {P : Lang} → Exp○ P Q → Lang
  -- ⟦_⟧₁ {Q = Q} _ = Q

  -- data ⟦_⟧ (e : Exp○ P Q) : Lang where
  --     ∞ : ⟦_⟧₁ {P = ⟦ e ⟧} e w → ⟦ e ⟧ w

  variable φ ψ : Lang → Lang

  data Exp : (Lang → Lang) → Type₁

  ○⟦_⟧ : Exp φ → Lang → Lang

  data ⟦_⟧ (e : Exp φ) : Lang where
    ∞′ : ○⟦ e ⟧ ⟦ e ⟧ w → ⟦ e ⟧ w

  data Exp where
    ∅   : Exp (const ◇.∅)
    ε   : Exp (const ◇.ε)
    ‵_  : (c : Char) → Exp (const (◇.‵ c))
    _·_ : {A : Type} → Dec A → Exp φ → Exp (λ L → (A ◇.· φ L))
    _∪_ : Exp φ → Exp ψ → Exp (λ L → φ L ◇.∪ ψ L)
    _*_ : Exp φ → Exp ψ → Exp (λ L → φ L ◇.* ψ L)
    I   : Exp id 
    μ   : (e : Exp φ) → Exp (λ _ → ⟦ e ⟧)

  ○⟦ ∅ ⟧ _ = ◇.∅
  ○⟦ ε ⟧ _ = ◇.ε
  ○⟦ (‵ c) ⟧ _ = ◇.‵ c
  ○⟦ x · e ⟧ L = typeOf x ◇.· ○⟦ e ⟧ L 
  ○⟦ e ∪ e₁ ⟧ L = ○⟦ e ⟧ L ◇.∪ ○⟦ e₁ ⟧ L
  ○⟦ e * e₁ ⟧ L = ○⟦ e ⟧ L ◇.* ○⟦ e₁ ⟧ L
  ○⟦ I ⟧ L = L
  ○⟦ μ e ⟧ _ = ⟦ e ⟧

  ○-correct : (e : Exp φ) → ○⟦ e ⟧ P ≡ φ P
  ○-correct ∅ = refl
  ○-correct ε = refl
  ○-correct (‵ c) = refl
  ○-correct (x · e) = cong (typeOf x ◇.·_) (○-correct e)
  ○-correct (e ∪ e₁) = cong₂ ◇._∪_ (○-correct e) (○-correct e₁)
  ○-correct (e * e₁) = cong₂ ◇._*_ (○-correct e) (○-correct e₁)
  ○-correct I = refl
  ○-correct (μ e) = refl

  ∞ : {e : Exp φ} → φ ⟦ e ⟧ w → ⟦ e ⟧ w
  ∞ {e = e} = foo (○-correct e) where
    foo : ∀ {L} → ○⟦ e ⟧ ⟦ e ⟧ ≡ L → L w → ⟦ e ⟧ w
    foo refl = ∞′

  ! : ∀{e : Exp φ} → ⟦ e ⟧ w → φ ⟦ e ⟧ w
  ! {e = e} = foo (○-correct e) where
    foo : ∀ {L} → ○⟦ e ⟧ ⟦ e ⟧ ≡ L → ⟦ e ⟧ w → L w
    foo refl (∞′ x) = x

  νμ : {e₀ : Exp ψ} (e : Exp φ) → ◇.ν (φ ⟦ e₀ ⟧) ⇔ ◇.ν (φ ◇.∅)
  νμ ∅ = ⇔.refl
  νμ ε = ⇔.refl
  νμ (‵ c) = ⇔.refl
  νμ (x · e) = ? -- ⇔cong (_ ×_) (νμ e)
  νμ (e ∪ e₁) = ? -- cong₂ _⊎_ (νμ e) (νμ e₁)
  νμ (e * e₁) = {!◇.ν*!}
  νμ I = {!!}
  νμ (μ e) = ⇔.refl

  ν₁ : Exp φ → Dec (◇.ν (φ ◇.∅))
  ν₁ ∅ = no λ ()
  ν₁ ε = yes refl
  ν₁ (‵ c) = no λ ()
  ν₁ (x · e) = x ×-dec ν₁ e
  ν₁ (e ∪ e₁) = ν₁ e ⊎-dec ν₁ e₁
  ν₁ (e * e₁) = Dec.map ◇.ν* (ν₁ e ×-dec ν₁ e₁)
  ν₁ I = no λ ()
  ν₁ (μ e) = Dec.map {!!} (ν₁ e)

  test : Exp _
  test = (‵ 'x') ∪ I

--   data Exp : Type₁ where
--     ∅ : Exp
--     ε : Exp
--     ‵_ : (c : Char) → Exp
--     _·_ : {A : Type} → Dec A → Exp → Exp
--     _∪_ : Exp → Exp → Exp
--     _*_ : Exp → Exp → Exp
-- 
--   ⟦_⟧ : Exp → Lang
--   ⟦ ∅ ⟧ = ◇.∅
--   ⟦ ε ⟧ = ◇.ε
--   ⟦ ‵ c ⟧ = ◇.‵ c
--   ⟦ x · e ⟧ = typeOf x ◇.· ⟦ e ⟧
--   ⟦ e ∪ e₁ ⟧ = ⟦ e ⟧ ◇.∪ ⟦ e₁ ⟧
--   ⟦ e * e₁ ⟧ = ⟦ e ⟧ ◇.* ⟦ e₁ ⟧
-- 
--   variable L : Lang
-- 
--   record Exp′ (L : Lang) : Type₁ where
--     constructor _~_
--     field
--       e : Exp
--       φ : ⟦ e ⟧ ◇.⟷ L
-- 
--   -- Goal
-- 
--   -- here we can explain the ν & δ stuff
-- 
--   ν : (e : Exp) → Dec (◇.ν ⟦ e ⟧)
--   δ : (c : Char) → (e : Exp) → Exp′ (◇.δ c ⟦ e ⟧)
--   -- δ : (c : Char) → (e : Exp) → Σ[ e′ ∈ Exp ] ⟦ e′ ⟧ ◇.⟷ ◇.δ c ⟦ e ⟧
-- 
--   -- δ-correct : ∀ e → ⟦ δ c e ⟧ ◇.⟷ ◇.δ c ⟦ e ⟧
--   -- δ-sound : ∀ e → ⟦ δ c e ⟧ w → ◇.δ c ⟦ e ⟧ w
--   -- δ-complete : ∀ e → ◇.δ c ⟦ e ⟧ w → ⟦ δ c e ⟧ w
-- 
--   ν′ : Exp′ L → Dec (◇.ν L)
--   ν′ (e ~ φ) = Dec.map (◇.⟷→⇔ φ) (ν e)
-- 
--   variable P Q R S : Lang
--   open ◇._⟷_
-- 
--   mapExp : P ◇.⟷ Q → Exp′ P → Exp′ Q
--   mapExp f (e ~ φ) = e ~ ◇.⟷trans φ f
-- 
--   δ⟷ : P ◇.⟷ Q → ◇.δ c P ◇.⟷ ◇.δ c Q
--   δ⟷ x .to = x .to
--   δ⟷ x .from = x .from
-- 
--   δ′ : (c : Char) → Exp′ L → Exp′ (◇.δ c L)
--   δ′ c (e ~ φ) = mapExp (δ⟷ φ) (δ c e)
-- 
--   parse : (_ : Exp′ L) (w : String) → Dec (L w)
--   parse e [] = ν′ e
--   parse e (c ∷ w) = parse (δ′ c e) w
-- 
--   -- Nullability
-- 
--   ⊥-dec : Dec ⊥
--   ⊥-dec = false because ofⁿ λ ()
-- 
--   []≡[]-dec : Dec ([] ≡ [])
--   []≡[]-dec = true because ofʸ refl
-- 
--   []≡x∷xs-dec : ∀{x : A} {xs} → Dec ([] ≡ x ∷ xs)
--   []≡x∷xs-dec = false because ofⁿ λ ()
-- 
--   ν ∅         = ⊥-dec
--   ν ε         = []≡[]-dec
--   ν (‵ c)     = []≡x∷xs-dec
--   ν (x · e)   = x ×-dec ν e 
--   ν (e ∪ e₁)  = ν e ⊎-dec ν e₁
--   ν (e * e₁)  = Dec.map ◇.ν* (ν e ×-dec ν e₁)
-- 
--   -- Derivation
-- 
--   ∅′ : Exp′ ◇.∅
--   ∅′ = ∅ ~ ◇.⟷refl
-- 
--   ε′ : Exp′ ◇.ε
--   ε′ = ε ~ ◇.⟷refl
-- 
--   _·′_ : Dec A → Exp′ L → Exp′ (A ◇.· L)
--   x ·′ (e ~ φ) = (x · e) ~ ◇.⟷cong {f = _ ◇.·_} ◇.·-map φ
-- 
--   _∪′_ : Exp′ P → Exp′ Q → Exp′ (P ◇.∪ Q)
--   (e ~ φ) ∪′ (e₁ ~ φ₁) = (e ∪ e₁) ~ ◇.⟷cong₂ {f = ◇._∪_} ◇.∪-map φ φ₁
-- 
--   _*′_ : Exp′ P → Exp′ Q → Exp′ (P ◇.* Q)
--   (e ~ φ) *′ (e₁ ~ φ₁) = (e * e₁) ~ ◇.⟷cong₂ {f = ◇._*_} ◇.*-map φ φ₁
-- 
--   δ c ∅         = ∅′
--   δ c ε         = mapExp ◇.δε ∅′
--   δ c (‵ c₁)    = mapExp ◇.δ‵ ((c ≟ c₁) ·′ ε′)
--   δ c (x · e)   = x ·′ δ c e
--   δ c (e ∪ e₁)  = δ c e ∪′ δ c e₁
--   δ c (e * e₁)  = mapExp ◇.δ* ((δ c e *′ (e₁ ~ ◇.⟷refl)) ∪′ (ν e ·′ δ c e₁))

-- Instead we restrict our class of languages

-- Syntax
data Exp : Type₁ where
    ∅ : Exp
    ε : Exp
    ‵_ : (c : Char) → Exp
    _·_ : {A : Type} → Dec A → Exp → Exp
    _∪_ : Exp → Exp → Exp
    _*_ : Exp → Exp → Exp
    I : Exp
    μ : Exp → Exp -- explain later
infix 22 ‵_
infixr 21 _*_
infixr 20 _∪_

variable
    n m : ℕ
    L : Lang
    e e₀ : Exp

-- Mapping syntax onto semantics
⟦_⟧₁ : Exp → Lang → Lang

data ⟦_⟧ (e : Exp) : Lang where
    ∞ : ⟦ e ⟧₁ ⟦ e ⟧ w → ⟦ e ⟧ w
! : ⟦ e ⟧ w → ⟦ e ⟧₁ ⟦ e ⟧ w
! (∞ x) = x
roll : ⟦ e ⟧₁ ⟦ e ⟧ w ⇔ ⟦ e ⟧ w
roll = mk⇔ ∞ !

⟦ ∅ ⟧₁ _ = ◇.∅
⟦ ε ⟧₁ _ = ◇.ε
⟦ ‵ c ⟧₁ _ = ◇.‵ c
⟦ x · e ⟧₁ L = typeOf x ◇.· ⟦ e ⟧₁ L
⟦ e ∪ e₁ ⟧₁ L = ⟦ e ⟧₁ L ◇.∪ ⟦ e₁ ⟧₁ L
⟦ e * e₁ ⟧₁ L = ⟦ e ⟧₁ L ◇.* ⟦ e₁ ⟧₁ L
⟦ I ⟧₁ L = L
⟦ μ e ⟧₁ _ = ⟦ e ⟧ -- explain this later

--------------------------------------------------------------------------------

-- Our goal is to define 
parse : (e : Exp) (w : String) → Dec (⟦ e ⟧ w)

-- Our approach uses the decomposition of languages into ν and δ.
-- Now we should explain the ◇.ν and ◇.δ

ν : (e : Exp) → Dec (◇.ν ⟦ e ⟧)
-- ν can easily be written to be correct by construction, however δ is more easily
-- written as a plain function and proven correct separately:
δ : Char → Exp → Exp
δ-sound    : ⟦ δ c e ⟧ w   → ◇.δ c ⟦ e ⟧ w
δ-complete : ◇.δ c ⟦ e ⟧ w → ⟦ δ c e ⟧ w

-- This follows the ν∘foldlδ decomposition.
parse e [] = ν e
parse e (c ∷ w) = map′ δ-sound δ-complete (parse (δ c e) w)

-- That was the main result of this paper. The remainder of the paper concerns
-- the implementation of ν, δ, δ-sound, and δ-commplete.

--------------------------------------------------------------------------------

-- Lemma 1. Nullability of e substituted in e is the same as the
-- nullability of e by itself
νe∅→νee : (e : Exp) → ◇.ν (⟦ e ⟧₁ ◇.∅) → ◇.ν (⟦ e ⟧₁ ⟦ e₀ ⟧) -- more general than we need, but easy
νee→νe∅ : (e : Exp) → ◇.ν (⟦ e ⟧₁ ⟦ e ⟧) → ◇.ν (⟦ e ⟧₁ ◇.∅)

-- Syntactic nullability
-- Correct by construction
ν₁ : (e : Exp) → Dec (◇.ν (⟦ e ⟧₁ ◇.∅))
ν₁ ∅ = no λ ()
ν₁ ε = yes refl
ν₁ (‵ c) = no λ ()
ν₁ (x · e) = x ×-dec ν₁ e
ν₁ (e ∪ e₁) = ν₁ e ⊎-dec ν₁ e₁
ν₁ (e * e₁) = map′ (λ x → [] , [] , refl , x) (λ { ([] , [] , refl , x) → x }) (ν₁ e ×-dec ν₁ e₁)
ν₁ I = no λ ()
ν₁ (μ e) = map′ (∞ ∘ νe∅→νee e) (νee→νe∅ e ∘ !) (ν₁ e)

-- Using Lemma 1 we can define ν in terms of ν₁
ν e = map′ (∞ ∘ νe∅→νee e) (νee→νe∅ e ∘ !) (ν₁ e)

-- TODO: show how ν works through examples

-- The forward direction is proven using straightforward induction.
νe∅→νee ε x = x
νe∅→νee (x₁ · e) (x , y) = x , νe∅→νee e y
νe∅→νee (e ∪ e₁) (inj₁ x) = inj₁ (νe∅→νee e x)
νe∅→νee (e ∪ e₁) (inj₂ y) = inj₂ (νe∅→νee e₁ y)
νe∅→νee (e * e₁) ([] , [] , refl , x , y) = [] , [] , refl , νe∅→νee e x , νe∅→νee e₁ y
νe∅→νee I ()
νe∅→νee (μ e) x = x

-- The backwards direction requires a bit more work. We use the
-- ν-split lemma:

-- If substituting e₀ into e is nullable then that must mean:
--  1. e  by itself was already nullable, or
--  2. e₀ by itself is nullable
ν-split : (e : Exp) → ◇.ν (⟦ e ⟧₁ ⟦ e₀ ⟧) → ◇.ν (⟦ e ⟧₁ ◇.∅) ⊎ ◇.ν (⟦ e₀ ⟧₁ ◇.∅)
ν-split ε x = inj₁ x
ν-split (_ · e) (x , y) = Sum.map₁ (x ,_) (ν-split e y)
ν-split (e ∪ e₁) (inj₁ x) = Sum.map₁ inj₁ (ν-split e x)
ν-split (e ∪ e₁) (inj₂ y) = Sum.map₁ inj₂ (ν-split e₁ y)
ν-split (e * e₁) ([] , [] , refl , x , y) = lift⊎₂ (λ x y → [] , [] , refl , x , y) (ν-split e x) (ν-split e₁ y)
ν-split {e₀ = e} I (∞ x) = inj₂ (reduce (ν-split e x))
ν-split (μ e) x = inj₁ x

-- The backwards direction of Lemma 1 is now simply a result of
-- ν-split where both sides of the disjoint union are equal and thus
-- we can reduce it to a single value.
νee→νe∅ e x = reduce (ν-split {e₀ = e} e x)

-- At this point (specifically the _*_ case of δ₁) we need to
-- introduce μ

-- Internal/syntactic substitution
sub : Exp → Exp → Exp
sub _ ∅ = ∅
sub _ ε = ε
sub _ (‵ c) = ‵ c
sub e₀ (x · e) = x · sub e₀ e
sub e₀ (e ∪ e₁) = sub e₀ e ∪ sub e₀ e₁
sub e₀ (e * e₁) = sub e₀ e * sub e₀ e₁
sub e₀ I = e₀
sub _ (μ e) = μ e

-- We would like to be able to say ⟦ sub e₀ e ⟧ ≡ ⟦ e ⟧₁ ⟦ e₀ ⟧, but
-- we can't because e₀'s free variable would get (implicitly)
-- captured. μ closes off an expression and thus prevents capture.

-- Lemma 2. (Internal) syntactic substitution is the same as
-- (external) semantic substitution. This is the raison d'être of μ.
sub-sem′ : (e : Exp) → ⟦ sub (μ e₀) e ⟧₁ L ≡ ⟦ e ⟧₁ ⟦ e₀ ⟧
sub-sem′ ∅ = refl
sub-sem′ ε = refl
sub-sem′ (‵ _) = refl
sub-sem′ (x · e) = cong (typeOf x ◇.·_) (sub-sem′ e) 
sub-sem′ (e ∪ e₁) = cong₂ ◇._∪_ (sub-sem′ e) (sub-sem′ e₁)
sub-sem′ (e * e₁) = cong₂ ◇._*_ (sub-sem′ e) (sub-sem′ e₁)
sub-sem′ I = refl
sub-sem′ (μ _) = refl

-- We only need to use this proof in its expanded form:
sub-sem : (e : Exp) → ⟦ sub (μ e₀) e ⟧₁ L w ≡ ⟦ e ⟧₁ ⟦ e₀ ⟧ w
sub-sem e = cong (λ L → L _) (sub-sem′ e)

-- Syntactic derivative

-- The e₀ argument stands for the whole expression
δ₁ : (c : Char) → Exp → Exp → Exp
δ₁ c _ ∅ = ∅
δ₁ c _ ε = ∅
δ₁ c _ (‵ c₁) = (c ≟ c₁) · ε
δ₁ c e₀ (x · e) = x · δ₁ c e₀ e
δ₁ c e₀ (e ∪ e₁) = δ₁ c e₀ e ∪ δ₁ c e₀ e₁
δ₁ c e₀ (e * e₁) = (δ₁ c e₀ e * sub (μ e₀) e₁) ∪ (Dec.map (⇔.trans (mk⇔ ! ∞) (≡→⇔ (sub-sem e))) (ν (sub (μ e₀) e)) · δ₁ c e₀ e₁)
δ₁ c e₀ I = I
δ₁ c _ (μ e) = μ (δ₁ c e e)

-- For a top-level expression the derivative is just the open δ₁ where e₀ is e itself.
δ c e = δ₁ c e e

-- TODO: show how δ works through examples.

-- The proofs are by induction and the sub-sem lemma
δ-sound′ : (e : Exp) → ⟦ δ₁ c e₀ e ⟧₁ ⟦ δ c e₀ ⟧ w → ◇.δ c (⟦ e ⟧₁ ⟦ e₀ ⟧) w
δ-sound′ (‵ _) (refl , refl) = refl
δ-sound′ (x₁ · e) (x , y) = x , δ-sound′ e y
δ-sound′ (e ∪ e₁) (inj₁ x) = inj₁ (δ-sound′ e x)
δ-sound′ (e ∪ e₁) (inj₂ y) = inj₂ (δ-sound′ e₁ y)
δ-sound′ {c = c} (e * e₁) (inj₁ (u , v , refl , x , y)) = c ∷ u , v , refl , δ-sound′ e x , transport (sub-sem e₁) y
δ-sound′ {c = c} {w = w} (e * e₁) (inj₂ (x , y)) = [] , c ∷ w , refl , x , δ-sound′ e₁ y
δ-sound′ {e₀ = e} I (∞ x) = ∞ (δ-sound′ e x)
δ-sound′ (μ e) (∞ x) = ∞ (δ-sound′ e x)

δ-sound {e = e} (∞ x) = ∞ (δ-sound′ e x)

δ-complete′ : (e : Exp) → ◇.δ c (⟦ e ⟧₁ ⟦ e₀ ⟧) w → ⟦ δ₁ c e₀ e ⟧₁ ⟦ δ c e₀ ⟧ w
δ-complete′ (‵ _) refl = refl , refl
δ-complete′ (_ · e) (x , y) = x , δ-complete′ e y
δ-complete′ (e ∪ e₁) (inj₁ x) = inj₁ (δ-complete′ e x)
δ-complete′ (e ∪ e₁) (inj₂ y) = inj₂ (δ-complete′ e₁ y)
δ-complete′ (e * e₁) (c ∷ u , v , refl , x , y) = inj₁ (u , v , refl , δ-complete′ e x , transport (sym (sub-sem e₁)) y)
δ-complete′ (e * e₁) ([] , c ∷ w , refl , x , y) = inj₂ (x , δ-complete′ e₁ y)
δ-complete′ {e₀ = e} I (∞ x) = ∞ (δ-complete′ e x)
δ-complete′ (μ e) (∞ x) = ∞ (δ-complete′ e x)

δ-complete {e = e} (∞ x) = ∞ (δ-complete′ e x)

-- Examples

-- In BNF:
-- <expr> ::= x | <expr> + <expr>
expr : Exp
expr = ‵ 'x' ∪ I * ‵ '+' * I

from-yes : (x : Dec A) → {case x of λ { (yes _) → ⊤ ; _ → ⊥}} → A
from-yes (yes x) = x

x+x+x : ⟦ expr ⟧ "x+x+x"
x+x+x = from-yes (parse _ _)

from-no : (x : Dec A) → {case x of λ { (no _) → ⊤ ; _ → ⊥}} → ¬ A
from-no (no x) = x

x+x+ : ¬ (⟦ expr ⟧ "x+x+")
x+x+ = from-no (parse _ _)

