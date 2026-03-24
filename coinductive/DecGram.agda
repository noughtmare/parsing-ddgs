{-# OPTIONS --guardedness #-}

module DecGram where

open import Agda.Primitive
open import Prelude
open import Lang
open import Gram
open T using (Tok ; _≟_)
open _↔_
open □Gram

variable G₃ : Gram n

data _~_ : (_ _ : Gram n) → Set₁ where
  ~rn : ∀{f : Fin n → Fin m}
    → G₁ ~ G₂
    → renameG f G₁ ~ renameG f G₂ 
  ~rnfix : ∀ G {f : Fin n → Fin m}
    → renameG f (fixG G) ~ fixG (renameG (consrn f) G)
  ~subst : ∀{k : Fin n → Gram m}
    → G₁ ~ G₂
    → substG G₁ k ~ substG G₂ k
  ~substfix : ∀ G (σ : Vec (Gram m) n)
    → substG (fixG G) (lookup σ) ~ fixG (substG G (lookup (var zero ∷ mapVec (renameG suc) σ)))
  ~δ : G₁ ~ G₂
    → δ⟦ Γν , Γδ , σ ⊢ G₁ ⟧ c ~ δ⟦ Γν , Γδ , σ ⊢ G₂ ⟧ c
  ~δfix : {Γν : Vec Set n} {Γδ : Vec (Gram m) n} {σ : Vec (Gram m) n}
    → δ⟦ Γν , Γδ , σ ⊢ fixG G ⟧ c
    ~ fixG
      (δ⟦ ν⟦ Γν ⊢ fixG G ⟧ ∷ Γν
         , δ⟦ Γν , mapVec (renameG suc) Γδ , mapVec (renameG suc) σ ⊢ fixG G ⟧ c ∷ mapVec (renameG suc) Γδ
         , mapVec (renameG suc) (substG (fixG G) (lookup σ) ∷ σ)
         ⊢ G ⟧ c)
  -- equivalence closure
  ~sym : G₁ ~ G₂ → G₂ ~ G₁
  ~refl : G₁ ~ G₂
  ~trans : G₁ ~ G₂ → G₂ ~ G₃ → G₁ ~ G₃

~ν : G₁ ~ G₂ → ν⟦ Γν ⊢ G₂ ⟧ ↔ ν⟦ Γν ⊢ G₁ ⟧
~ν = {!!}

data DecGram (n : ℕ) : Gram n → Set₁ where
    ∅ : DecGram n ∅
    ε : DecGram n ε
    ‵_ : (c : Tok) → DecGram n (‵ c)
    _·_ : Dec A → DecGram n G → DecGram n (A · G)
    _∪_ : DecGram n G₁ → DecGram n G₂ → DecGram n (G₁ ∪ G₂)
    _∙_ : DecGram n G₁ → DecGram n G₂ → DecGram n (G₁ ∙ G₂)
    var : (i : Fin n) → DecGram n (var i)
    μ : DecGram (suc n) G → DecGram n (fixG G)
    _◃_ :
      (∀{Γν} → ν⟦ Γν ⊢ G ⟧ ↔ ν⟦ Γν ⊢ G′ ⟧) → DecGram n G′ → DecGram n G

      ν⟦ Γν ⊢ δ⟦ Γν′ , Γδ , σ ⊢ G ⟧ ⟧ ↔ ...

renameDG : ∀{n m G} → (f : Fin n → Fin m) → DecGram n G → DecGram m (renameG f G)
renameDG f ∅ = ∅
renameDG f ε = ε
renameDG f (‵ c) = ‵ c
renameDG f (x · DG) = x · renameDG f DG
renameDG f (DG ∪ DG₁) = renameDG f DG ∪ renameDG f DG₁
renameDG f (DG ∙ DG₁) = renameDG f DG ∙ renameDG f DG₁
renameDG f (var i) = var (f i)
renameDG f (μ {G = G} DG) = ~rnfix G ◃ μ (renameDG (consrn f) DG)
-- renameDG f (μ {G = G} DG) = ⇔~ (renameFixG G f) ◃ μ (renameDG (consrn f) DG)
renameDG f (_◃_ {G = G₁} {G′ = G₂} R G) = ~rn R ◃ renameDG f G
-- renameDG f (_◃_ {G = G₁} {G′ = G₂} R G) = {!⇔rename {G = G₁} {G′ = G₂} {f = f} R!} ◃ renameDG f G

substDG : (σ : Vec (Gram m) n) → DecGram n G → ((i : Fin n) → DecGram m (lookup σ i)) → DecGram m (substG G (lookup σ))
substDG σ ∅ k = ∅
substDG σ ε k = ε
substDG σ (‵ c) k = ‵ c
substDG σ (x · G) k = x · substDG σ G k
substDG σ (G ∪ G₁) k = substDG σ G k ∪ substDG σ G₁ k
substDG σ (G ∙ G₁) k = substDG σ G k ∙ substDG σ G₁ k
substDG σ (var i) k = k i
substDG σ (μ {G = G′} G) k = ~substfix G′ σ ◃ μ (substDG (var zero ∷ mapVec (renameG suc) σ) G λ { zero → var zero ; (suc i) → subst (λ X → DecGram (suc _) X) (sym (lookup-map (renameG suc) σ i)) (renameDG suc (k i)) })
-- substDG σ (μ {G = G′} G) k = ⇔~ (↔sym (substDGμ G′)) ◃ μ (substDG (var zero ∷ mapVec (renameG suc) σ) G λ { zero → var zero ; (suc i) → subst (λ X → DecGram (suc _) X) (sym (lookup-map (renameG suc) σ i)) (renameDG suc (k i)) })
substDG σ (_◃_ {G = G₀} {G′ = G₁} R G) k = ~subst R ◃ substDG σ G k
-- substDG σ (_◃_ {G = G₀} {G′ = G₁} bi G) k = ⇔subst {G = G₀} {G′ = G₁} {k = lookup σ} bi ◃ substDG σ G k

-- example

expr′ : DecGram n _
expr′ = μ (‵ x ∪ var zero ∙ ‵ + ∙ var zero) where open Tok

-- nullability

-- foo : ∀ {Γν′}
--   → (∀{Γν} → (∀ i → Dec (lookup Γν i)) → Dec ν⟦ Γν ⊢ G₁ ⟧)
--   ↔ (∀{Γν} → (∀ i → Dec (lookup Γν i)) → Dec ν⟦ Γν ⊢ G₂ ⟧)
--   → (∀{Γν} → (∀ i → Dec (lookup Γν i)) → Dec ν⟦ Γν ⊢ δ⟦ Γν′ , Γδ , σ ⊢ G₁ ⟧ c ⟧)
--   ↔ (∀{Γν} → (∀ i → Dec (lookup Γν i)) → Dec ν⟦ Γν ⊢ δ⟦ Γν′ , Γδ , σ ⊢ G₂ ⟧ c ⟧)

ν?′ : DecGram n G → ∀ {Γν} → (∀ i → Dec (lookup Γν i)) → Dec ν⟦ Γν ⊢ G ⟧
ν?′ ∅ Γ = no (λ z → z)
ν?′ ε Γ = yes tt
ν?′ (‵ c) Γ = no (λ z → z)
ν?′ (x · G) Γ = x ×? ν?′ G Γ
ν?′ (G₁ ∪ G₂) Γ = ν?′ G₁ Γ ⊎? ν?′ G₂ Γ
ν?′ (G₁ ∙ G₂) Γ = ν?′ G₁ Γ ×? ν?′ G₂ Γ
ν?′ (var i) Γ = Γ i
ν?′ (μ {G = G′} G) Γ = mapDec (νfix G′) (ν?′ G (λ { zero → no λ () ; (suc i) → Γ i }))
ν?′ (_◃_ {G = G₁} {G′ = G₂} R G) {Γν = Γν} Γ =
  mapDec
    {!~ν R!}
    --(↔trans
    --  (νG-correct {Γ = mapVec const Γν} {Γν = Γν} G₂ (λ i → subst (λ X → lookup Γν i ↔ X []) (sym ((lookup-map const Γν i))) ↔refl))
    --(↔trans
    --  (↔sym {!bi!})
    --  (↔sym (νG-correct G₁ (λ i → subst (λ X → lookup Γν i ↔ X []) (sym ((lookup-map const Γν i))) ↔refl)))))
    (ν?′ G Γ)

-- -- (∀ {Γ} → ν ⟦ Γ ⊢ G₁ ⟧ ↔ ν ⟦ Γ ⊢ G₂ ⟧) → ν⟦ Γν ⊢ G₁ ⟧ ↔ ν⟦ Γν ⊢ G₂ ⟧

ν?₀ : DecGram zero G → Dec (ν ⟦ G ⟧)

ν? : DecGram n G → (∀ i → Dec (ν (lookup Γ i))) → Dec (ν ⟦ Γ ⊢ G ⟧)
ν? {G = G} {Γ = Γ′} DG Γ = mapDec (νG-correct {Γν = mapVec ν Γ′} G (↔lookup ν Γ′)) (ν?′ DG (λ i → mapDec (↔sym (↔lookup ν Γ′ i)) (Γ i)))

ν?₀ G = ν? G λ ()

-- derivative

data VAll {A : Set₁} (f : A → Set₁) : Vec A n → Set₁ where
   [] : VAll f []
   _∷_ : ∀{x} {xs : Vec A n} → f x → VAll f xs → VAll f (x ∷ xs)

renamesucDGs : ∀{Gs : Vec (Gram m) n} → VAll (DecGram m) Gs → VAll (DecGram (suc m)) (mapVec (renameG suc) Gs)
renamesucDGs [] = []
renamesucDGs (x ∷ xs) = renameDG suc x ∷ renamesucDGs xs

lookupVAll : {Xs : Vec A n} {f : A → Set₁} (i : Fin n) → VAll f Xs → f (lookup Xs i)
lookupVAll zero (x ∷ _) = x
lookupVAll (suc i) (_ ∷ xs) = lookupVAll i xs

δ? : (c : Tok) → DecGram n G → DecGram n (δ⟦ Γν , Γδ , σ ⊢ G ⟧ c)
-- δ? : {σ : Vec (Gram n) n} {Gs : Vec (Gram n) n}
--    → (DGs : VAll (DecGram n) Gs)
--    → (c : Tok)
--    → ((i : Fin n) → DecGram n (lookup σ i))
--    → DecGram n G → DecGram n (δ⟦ mapVec ν⟦ tabulate (λ _ → ⊥) ⊢_⟧ Gs , tabulate var , σ ⊢ G ⟧ c)
δ? DGs c σc ∅ = ∅
δ? DGs c σc ε = ∅
δ? DGs c σc (‵ c′) with c′ ≟ c
... | yes _ = ε
... | no _ = ∅
δ? DGs c σc (x · G) = x · δ? DGs c σc G
δ? DGs c σc (G ∪ G₁) = δ? DGs c σc G ∪ δ? DGs c σc G₁

-- Three important cases:

δ? {n = n} {σ = σ} {Gs = Gs} DGs c σc (G ∙ G₁) =
  δ? DGs c σc G ∙ substDG σ G₁ σc
  ∪ (ν?′ G
     (λ i → mapDec (≡→↔ (sym (lookup-map ν⟦ tabulate (λ _ → ⊥) ⊢_⟧ Gs i))) (ν?′ (lookupVAll i DGs) λ j → mapDec (≡→↔ (sym (lookup-tabulate n))) (no λ ()))) · δ? DGs c σc G₁)

δ? {n = n} DGs c σc (var i) = lookup i Γδ
-- subst (DecGram n) (sym (lookup-tabulate n)) (var i)

δ? {σ = σ} {Gs = Gs} DGs c σc (μ {G = G′} G) =
  {!~δfix!}
  -- (λ {Γ} → δunroll {G₀ = G′} G′ {Γ = Γ})
  ◃ μ {G = δ⟦ _ , _ , _ ⊢ G′ ⟧ c}
      (δ?
          -- {Γν = ν⟦ Γν ⊢ fixG G′ ⟧ ∷ Γν}
          {σ = mapVec (renameG suc) (substG (fixG G′) (lookup σ) ∷ σ)}
          {Gs = G′ ∷ mapVec (renameG suc) Gs}
          (G ∷ renamesucDGs DGs)
          c
          -- (λ { zero → ν?′ (μ G) ? ; (suc i) → Γνc i })
          (λ { zero → renameDG {G = substG (fixG G′) (lookup σ)} suc (substDG σ (μ G) σc) ; (suc i) → subst (DecGram (suc _)) (sym (lookup-map (renameG suc) σ i)) (renameDG suc (σc i)) })
          G)
δ? {n = n} {Gs = Gs} DGs c σc (_◃_ {G = G₁} {G′ = G₂} bi G) = ~δ bi ◃ δ? DGs c σc G
--  (λ {Γ} {w} →
--  {!!}
--  {!↔trans
--    (δG-correct {Γ = mapVec ⟦ {!!} ⊢_⟧ Gs}
--      (λ i → ↔trans (≡→↔ (lookup-map (ν⟦ tabulate (λ _ → ⊥) ⊢_⟧) Gs i))
--        (↔trans ((νG-correct {Γ = tabulate (λ _ _ → ⊥)} (lookup Gs i)
--          λ j → ↔trans (≡→↔ (lookup-tabulate n)) (≡→↔ (sym (cong (λ f → f []) (lookup-tabulate n {f = λ _ _ → ⊥}))))))
--          {!!}))
--      {!!}
--      {!!}
--      G₁)
--    (↔trans
--      bi
--      (↔sym
--        (δG-correct {!!} {!!} {!!} G₂)
--        ))!}
--  ) ◃ δ? DGs c σc G

δ?₀ : DecGram zero G → (c : Tok) → DecGram zero (δ⟦ [] , [] , [] ⊢ G ⟧ c)
δ?₀ G c = δ? [] c (λ ()) G

parse : DecGram zero G → (w : List Tok) → Dec (⟦ G ⟧ w)
parse G [] = ν?₀ G
parse {G = G′} G (c ∷ w) = mapDec (δG-correct (λ ()) (λ ()) (λ ()) G′) (parse (δ?₀ G c) w)


