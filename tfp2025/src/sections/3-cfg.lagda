\section{Context-free Languages}\label{sec:context-free}

\begin{code}[hide]
module 3-cfg where

open import Level using (Level)

open import 2-overview
open _↔_
\end{code}

\begin{code}[hide]
variable V V₁ V₂ V' : Set
variable k k' n m : ℕ

data Fin : ℕ → Set where
    zero : Fin (suc n)
    suc : Fin n → Fin (suc n)

∃-syntax : {A : Set} → (A → Set) → Set
∃-syntax {A} B = Σ A B

syntax ∃-syntax (λ x → A) = ∃[ x ] A
\end{code}

Regular languages can be useful for describing patterns in program text, but they are not sufficient to model the full language of a programming language.
For example, balanced brackets are a common syntactic element in programming languages. 

\begin{example}
We can boil the problem down to the following language which consists only of balanced brackets:

\begin{code}
bracketsₖ : ℕ → Lang
bracketsₖ zero _ = ⊥
bracketsₖ (suc k) w  = (w ≡ [])
                     ⊎ (∃[ u ] (w ≡ `[ ∷ [] ++ u ++ `] ∷ []) × bracketsₖ k u)
                     ⊎ (∃[ u ] ∃[ v ] (w ≡ u ++ v) × bracketsₖ k u × bracketsₖ k v)
\end{code}
\begin{code}
brackets : Lang
brackets w = ∃[ k ] bracketsₖ k w
\end{code}

\begin{remark}\label{rem:truncation}
The \af{bracketsₖ} function is truncated after \ab{k} recursive calls to ensure termination, which is required for all functions in type theory. The proper language \af{brackets} asserts that, for a string to be in the language, there must exist a \ab{k} which is large enough that the truncation becomes irrelevant for that particular string.
\end{remark}
\end{example}

\subsection{Context-free Grammars}

This language of balanced brackets is famously context-free. To support languages such as these we add variables, \ac{var}, and fixed points, \ac{μ}, to our grammars.
\begin{code}
data Gram (n : ℕ) : Set₁ where
    ∅ ε : Gram n
    char : Char → Gram n
    _·_ : Dec A → Gram n → Gram n
    _∪_ _∗_ : Gram n → Gram n → Gram n
    var : Fin n → Gram n
    μ : Gram (suc n) → Gram n
\end{code}
\begin{code}[hide]
infixr 21 _∗_
infixr 20 _∪_
\end{code}

\begin{code}[hide]
variable G G₁ G₂ : Gram n
variable Γ Γ' : Fin n → Lang

_∷>_ : {ℓ : Level} {A : Fin (suc n) → Set ℓ} → A zero → ((i : Fin n) → A (suc i)) → ((i : Fin (suc n)) → A i)
(x ∷> xs) zero = x
(x ∷> xs) (suc i) = xs i
\end{code}

\begin{code}
⟦_⟧ₖ : Gram n → (Fin n → Lang) → ℕ → Lang
\end{code}
\begin{code}[hide]
⟦ ∅ ⟧ₖ Γ _ _ = ⊥
⟦ ε ⟧ₖ Γ _ w = w ≡ []
⟦ x · G ⟧ₖ Γ k w = ⌊ x ⌋ × ⟦ G ⟧ₖ Γ k w
⟦ G₁ ∪ G₂ ⟧ₖ Γ k w = ⟦ G₁ ⟧ₖ Γ k w ⊎ ⟦ G₂ ⟧ₖ Γ k w
⟦ G₁ ∗ G₂ ⟧ₖ Γ k w = ∃[ u ] ∃[ v ] (w ≡ (u ++ v)) × ⟦ G₁ ⟧ₖ Γ k u × ⟦ G₂ ⟧ₖ Γ k v
⟦ char x ⟧ₖ Γ _ w = w ≡ (x ∷ [])
\end{code}
\begin{code}
⟦ var i ⟧ₖ Γ k w = Γ i w
⟦ μ G ⟧ₖ Γ zero w = ⊥
⟦ μ G ⟧ₖ Γ (suc k) w = ⟦ G ⟧ₖ (⟦ μ G ⟧ₖ Γ k ∷> Γ) k w
\end{code}
\begin{code}
⟦_⟧ : Gram n → (Fin n → Lang) → Lang
⟦ G ⟧ Γ w = ∃[ k ] ⟦ G ⟧ₖ Γ k w
\end{code}

\begin{example}
This allows us to write a grammar for the language of balanced brackets.
\begin{code}
bracketsG : Gram n
bracketsG = μ (ε ∪ char `[ ∗ var zero ∗ char `] ∪ var zero ∗ var zero)
\end{code}
\end{example}

\begin{lemma}
We can map over context and the fuel of the truncated semantics.
\begin{code}[hide]
max : ℕ → ℕ → ℕ
max zero k' = k'
max (suc k) zero = suc k
max (suc k) (suc k') = suc (max k k')

data _≤_ : ℕ → ℕ → Set where
    z≤m : zero ≤ m
    s≤s : n ≤ m → suc n ≤ suc m

≤refl : n ≤ n
≤refl {n = zero} = z≤m
≤refl {n = suc n} = s≤s ≤refl

n≤maxnm : (n m : ℕ) → n ≤ max n m
n≤maxnm zero m = z≤m
n≤maxnm (suc n) zero = ≤refl
n≤maxnm (suc n) (suc m) = s≤s (n≤maxnm n m)

m≤maxnm : (n m : ℕ) → m ≤ max n m
m≤maxnm n zero = z≤m
m≤maxnm zero (suc m) = ≤refl
m≤maxnm (suc n) (suc m) = s≤s (m≤maxnm n m)

\end{code}
\begin{code}
mapΓ  : (G : Gram n) (Γ Γ' : Fin n → Lang) 
      → ((i : Fin n) → {w : String} → Γ i w → Γ' i w)
      → ⟦ G ⟧ₖ Γ k w → ⟦ G ⟧ₖ Γ' k w
\end{code}
\begin{code}[hide]
mapΓ ε Γ Γ' f x = x
mapΓ (char x₁) Γ Γ' f x = x
mapΓ (x₁ · G) Γ Γ' f (x , y) = x , mapΓ G Γ Γ' f y
mapΓ (G₁ ∪ G₂) Γ Γ' f (inl x) = inl (mapΓ G₁ Γ Γ' f x)
mapΓ (G₁ ∪ G₂) Γ Γ' f (inr x) = inr (mapΓ G₂ Γ Γ' f x)
mapΓ (G₁ ∗ G₂) Γ Γ' f (u , v , refl , x , y) = u , v , refl , mapΓ G₁ Γ Γ' f x , mapΓ G₂ Γ Γ' f y
mapΓ (var i) Γ Γ' f x = f i x
mapΓ {k = suc k} (μ G) Γ Γ' f x = mapΓ G _ _ (λ { zero → mapΓ {k = k} (μ G) Γ Γ' f ; (suc i) → f i }) x

\end{code}
\begin{code}
mapk : k ≤ k' → ⟦ G ⟧ₖ Γ k w → ⟦ G ⟧ₖ Γ k' w
\end{code}
\begin{code}[hide]
mapk {G = ε} k≤k' x = x
mapk {G = char x₁} k≤k' x = x
mapk {G = x₁ · G} k≤k' (x , y) = x , mapk {G = G} k≤k' y
mapk {G = G₁ ∪ G₂} k≤k' (inl x) = inl (mapk {G = G₁} k≤k' x)
mapk {G = G₁ ∪ G₂} k≤k' (inr x) = inr (mapk {G = G₂} k≤k' x)
mapk {G = G₁ ∗ G₂} k≤k' (u , v , refl , x , y) = u , v , refl , mapk {G = G₁} k≤k' x , mapk {G = G₂} k≤k' y
mapk {G = var i} k≤k' x = x
mapk {G = μ G} (s≤s k≤k') x = mapk {G = G} k≤k' (mapΓ G _ _ (λ { zero → mapk {G = μ G} k≤k' ; (suc i) → λ z → z}) x)

weakenˡ : ⟦ G ⟧ₖ Γ k w → ⟦ G ⟧ₖ Γ (max k k') w
weakenˡ {G = G} {k = k} {k' = k'} = mapk {G = G} (n≤maxnm k k')

weakenʳ : ⟦ G ⟧ₖ Γ k' w → ⟦ G ⟧ₖ Γ (max k k') w
weakenʳ {G = G} {k' = k'} {k = k} = mapk {G = G} (m≤maxnm k k')
\end{code}
\end{lemma}

\begin{lemma}
We can map a change of variables over a grammar and we can substitute variables. This essentially shows that grammars form a relative monad.
\begin{code}
rename : (Fin n → Fin m) → Gram n → Gram m
\end{code}
\begin{code}[hide]
rename _ ∅ = ∅
rename _ ε = ε
rename _ (char c) = char c
rename f (x · G) = x · rename f G
rename f (G₁ ∪ G₂) = rename f G₁ ∪ rename f G₂
rename f (G₁ ∗ G₂) = rename f G₁ ∗ rename f G₂
rename f (var i) = var (f i)
rename f (μ G) = μ (rename (λ { zero → zero ; (suc i) → suc (f i) }) G)
\end{code}
\begin{code}
subst : Gram n → (Fin n → Gram m) → Gram m
\end{code}
\begin{code}[hide]
subst ∅ σ = ∅
subst ε σ = ε
subst (char c) σ = char c
subst (x · G) σ = x · subst G σ
subst (G ∪ G₁) σ = subst G σ ∪ subst G₁ σ
subst (G ∗ G₁) σ = subst G σ ∗ subst G₁ σ
subst (var x) σ = σ x
subst (μ G) σ = μ (subst G λ { zero → var zero ; (suc i) → rename suc (σ i) })
\end{code}
\end{lemma}

\subsection{Parsing}\label{sec:cfg-parsing}

Parsing our context-free grammar follows the same structure as the simple grammars from \cref{sec:gram-and-parsing}. Concretely, we define functions that compute the nullability, \af{ν?}, and derivatives, \af{δ?}.

\begin{example}
Let us consider the balanced bracket grammar example. We can see that it is nullable because it contains an \ac{ε} in the fixed point. It is also possible to parse the empty string by taking one iteration of the fixed point using the \ac{var}~\ac{zero}~∗~\ac{var}~\ac{zero} part and then the \ac{ε} for both recursive calls, but note that we always need to end in an empty base case. Thus, for a fixed point to be nullable, it must be nullable even if we do not consider the recursive calls.

The derivative of the balanced bracket grammar can be taken with respect to any character, but only the character \ac{`[} results in anything interesting because any string in the balanced bracket language needs to start with an opening bracket. The first thing we might try is to unroll the fixed point one step, yielding the following grammar:
\begin{code}
bracketsG₁ : Gram n
bracketsG₁ = ε ∪ char `[ ∗ bracketsG ∗ char `] ∪ bracketsG ∗ bracketsG
\end{code}
We know how to take the derivative of the first two parts, but \af{bracketsG}~\ac{∗}~\af{bracketsG} seems problematic because its derivative depends on the derivative of \af{bracketsG} itself. Luckily, we can introduce a new fixed point when describing the derivative to refer to the derivative itself.
\begin{code}
bracketsG' : Gram n
bracketsG' = μ (bracketsG ∗ char `] ∪ var zero ∗ bracketsG)
\end{code}
\end{example}

% Nullability

% TODO

\begin{code}[hide]
ν▹ : (ν (⟦ G₁ ⟧ Γ) × ν (⟦ G₂ ⟧ Γ)) ↔ ν (⟦ G₁ ∗ G₂ ⟧ Γ)
to (ν▹ {G₁ = G₁} {G₂ = G₂}) ((n , x) , (m , y)) = max n m , [] , [] , refl , weakenˡ {G = G₁} x , weakenʳ {G = G₂} y
from ν▹ (n , [] , [] , refl , x , y) = (n , x) , (n , y)

-- refold : (G : Gram (suc n)) → ⟦ G ⟧ (⟦ μ G ⟧ Γ ∷> Γ) ⇔ ⟦ μ G ⟧ Γ
-- to (refold G) x = {!!}
-- from (refold G) (suc k , x) = k , mapΓ G _ _ (λ { zero → k ,_ ; (suc i) → λ z → z }) x
\end{code}
\begin{code}
postulate νGμG→νG⊥  : ν (⟦ G ⟧ₖ (⟦ μ G ⟧ₖ Γ k ∷> Γ) k) → ν (⟦ G ⟧ₖ ((λ _ → ⊥) ∷> Γ) k)
\end{code}
\begin{code}
νG⊥↔νμG  : (Γ : Fin n → Lang) (G : Gram (suc n)) → ν (⟦ G ⟧ ((λ _ → ⊥) ∷> Γ)) ↔ ν (⟦ μ G ⟧ Γ)
\end{code}
\begin{code}[hide]
to (νG⊥↔νμG Γ G) (k , x) = suc k , mapΓ G _ _ (λ { zero → λ () ; (suc _) → λ z → z }) x
from (νG⊥↔νμG Γ G) (suc k , x) = k , νGμG→νG⊥ {G = G} x
\end{code}
\begin{code}
ν? : (G : Gram n) (Γν : (i : Fin n) → Dec (ν (Γ i))) → Dec (ν (⟦ G ⟧ Γ))
\end{code}
\begin{code}[hide]
ν? ∅ _ = no λ ()
ν? ε _ = yes (zero , refl)
ν? (char c) _ = no λ ()
ν? (x · G) Γν = map? (record { to = λ (x , n , y) → (n , x , y) ; from = λ (n , x , y) → (x , n , y) }) (x ×? ν? G Γν)
ν? (G₁ ∪ G₂) Γν = map? (record { to = λ { (inl (n , x)) → n , inl x ; (inr (n , x)) → n , inr x } ; from = λ { (n , inl x) → inl (n , x) ; (n , inr x) → inr (n , x) } }) (ν? G₁ Γν ⊎? ν? G₂ Γν)
ν? (G₁ ∗ G₂) Γν = map? (ν▹ {G₁ = G₁} {G₂ = G₂}) (ν? G₁ Γν ×? ν? G₂ Γν)
\end{code}
\begin{code}
ν? (var i) Γν = map? (record { to = zero ,_ ; from = λ (_ , x) → x }) (Γν i)
ν? {Γ = Γ} (μ G) Γν = map? (νG⊥↔νμG Γ G) (ν? G (no (λ ()) ∷> Γν))
\end{code}

% Derivatives

% TODO

We can define a derivative function. This time it is not correct by construction.
\begin{code}
δ?  : (Γ : Fin n → Lang) (Γν : (i : Fin n) → Dec (ν (Γ i))) (Γδ : Fin n → Gram m) (Γσ : Fin n → Gram m) 
    → Gram n → Char → Gram m
\end{code}
\begin{code}[hide]
δ? _ _ _ _ ∅ c = ∅
δ? _ _ _ _ ε c = ∅
δ? _ _ _ _ (char c') c with c ≟ c'
... | yes _ = ε
... | no _ = ∅
δ? Γ Γν Γδ Γσ (A · G) c = A · δ? Γ Γν Γδ Γσ G c
δ? Γ Γν Γδ Γσ (G₁ ∪ G₂) c = δ? Γ Γν Γδ Γσ G₁ c ∪ δ? Γ Γν Γδ Γσ G₂ c
δ? Γ Γν Γδ Γσ (G₁ ∗ G₂) c =  (δ? Γ Γν Γδ Γσ G₁ c ∗ subst G₂ Γσ)
                          ∪  (ν? {Γ = Γ} G₁ Γν · δ? Γ Γν Γδ Γσ G₂ c)
\end{code}
\begin{code}
δ? _ _ Γδ _ (var i) _ = Γδ i
δ? Γ Γν Γδ Γσ (μ G) c =
  μ (δ?  (⟦ μ G ⟧ Γ                      ∷> Γ)
         (ν? {Γ = Γ} (μ G) Γν            ∷> Γν)
         (var zero                       ∷> (rename suc ∘ Γδ))
         (subst (μ G) (rename suc ∘ Γσ)  ∷> (rename suc ∘ Γσ))
         G c)
\end{code}
\begin{code}[hide]

↔refl : A ↔ A
↔refl = record { to = λ x → x ; from = λ z → z }

\end{code}
\begin{code}
postulate substΓσ  : {Γσ : Fin n → Gram m} (G : Gram n)
                   → ((i : Fin n) → ⟦ Γσ i ⟧ Γ' ⇔ Γ i) → ⟦ subst G Γσ ⟧ Γ' ⇔ ⟦ G ⟧ Γ
\end{code}
\begin{code}[hide]

\end{code}
We show the correctness separately by showing the semantics of the syntactic derivative corresponds to the semantic derivative as follows:
\begin{code}
δ?↔δ : (G : Gram n) {Γ : Fin n → Lang} {Γ' : Fin m → Lang} 
       {Γν : (i : Fin n) → Dec (ν (Γ i))} {Γδ : Fin n → Gram m} {Γσ : Fin n → Gram m}
     → ((i : Fin n) → ⟦ Γσ i ⟧ Γ' ⇔ Γ i)
     → ((i : Fin n) → ⟦ Γδ i ⟧ Γ' ⇔ δ (Γ i) c)
     → ⟦ δ? Γ Γν Γδ Γσ G c ⟧ Γ' ⇔ δ (⟦ G ⟧ Γ) c
\end{code}

Sadly, we are still working on a proof of the most important part of this correspondence.
\begin{code}
postulate
  δ?↔δμ  : (G : Gram (suc n)) {Γ : Fin n → Lang} {Γ' : Fin m → Lang} 
           {Γν : (i : Fin n) → Dec (ν (Γ i))} {Γδ : Fin n → Gram m} {Γσ : Fin n → Gram m}
         → ((i : Fin n) → ⟦ Γσ i ⟧ Γ' ⇔ Γ i)
         → ((i : Fin n) → ⟦ Γδ i ⟧ Γ' ⇔ δ (Γ i) c)
         → ⟦ δ? Γ Γν Γδ Γσ (μ G) c ⟧ Γ' ⇔ δ (⟦ μ G ⟧ Γ) c
\end{code}
\begin{code}[hide]
δ?↔δ ∅ eσ eδ = ↔refl
to (δ?↔δ ε eσ eδ) ()
from (δ?↔δ ε eσ eδ) ()

to (δ?↔δ {c = c}     (char c′) eσ eδ) x with c ≟ c′
to (δ?↔δ {c = c}     (char .c) eσ eδ) (k , refl) | yes refl = k , refl
to (δ?↔δ             (char _)  eσ eδ) () | no _
to (δ?↔δ             (A · G)   eσ eδ) (k , x , y) with to (δ?↔δ G eσ eδ) (k , y)
... | k , y = k , x , y 
to (δ?↔δ             (G₁ ∪ G₂) eσ eδ) (k , inl x) with to (δ?↔δ G₁ eσ eδ) (k , x)
... | k , x = k , inl x
to (δ?↔δ             (G₁ ∪ G₂) eσ eδ) (k , inr x) with to (δ?↔δ G₂ eσ eδ) (k , x)
... | k , x = k , inr x
to (δ?↔δ {c = c}     (G₁ ∗ G₂) eσ eδ) (k , inl (u , v , refl , x , y)) with to (δ?↔δ G₁ eσ eδ) (k , x) | to (substΓσ G₂ eσ) (k , y)
... | k₁ , x | k₂ , y = max k₁ k₂ , (c ∷ u) , v , refl , weakenˡ {G = G₁} x , weakenʳ {G = G₂} y
to (δ?↔δ {c = c} (G₁ ∗ G₂) eσ eδ) (k , inr (x , y)) with x | to (δ?↔δ G₂ eσ eδ) (k , y)
... | k₁ , x | k₂ , y = max k₁ k₂ , [] , (c ∷ _) , refl , weakenˡ {G = G₁} x , weakenʳ {G = G₂} y
to (δ?↔δ           (var i)   eσ eδ) (k , x) = zero , to (eδ i) (k , x)
from (δ?↔δ {c = c} (char c′) eσ eδ) x with c ≟ c′
from (δ?↔δ {c = c} (char c)  eσ eδ) (k , refl) | yes refl = k , refl
from (δ?↔δ {c = c} (char .c) eσ eδ) (k , refl) | no ¬c≡c = k , ¬c≡c refl
from (δ?↔δ         (A · G)   eσ eδ) (k , x , y) with from (δ?↔δ G eσ eδ) (k , y)
... | k , y = k , x , y
from (δ?↔δ         (G₁ ∪ G₂) eσ eδ) (k , inl x) with from (δ?↔δ G₁ eσ eδ) (k , x)
... | k , x = k , inl x
from (δ?↔δ         (G₁ ∪ G₂) eσ eδ) (k , inr x) with from (δ?↔δ G₂ eσ eδ) (k , x)
... | k , x = k , inr x
from (δ?↔δ {c = c} (G₁ ∗ G₂) eσ eδ) (k , [] , (.c ∷ v) , refl , x , y) with from (δ?↔δ G₂ eσ eδ) (k , y)
... | k' , y = k' , inr ((k , x) , y)
from (δ?↔δ {c = c} (G₁ ∗ G₂) eσ eδ) (k , (.c ∷ u) , v , refl , x , y) with from (δ?↔δ G₁ eσ eδ) (k , x) | from (substΓσ G₂ eσ) (k , y)
... | k₁ , x | k₂ , y = max k₁ k₂ , inl (u , v , refl , weakenˡ {G = δ? _ _ _ _ G₁ c} x , weakenʳ {G = subst G₂ _} y)
from (δ?↔δ         (var i)   eσ eδ) (k , x) = from (eδ i) x

δ?↔δ (μ G) eσ eδ = δ?↔δμ G eσ eδ
\end{code}
% \begin{code}[hide]
% substGvar≡G : (G : Gram n) → subst G var ≡ G
% substGvar≡G ∅ = refl
% substGvar≡G ε = refl
% substGvar≡G (char x) = refl
% substGvar≡G (x · G) = cong (x ·_) (substGvar≡G G)
% substGvar≡G (G ∪ G₁) = cong₂ _∪_ (substGvar≡G G) (substGvar≡G G₁)
% substGvar≡G (G ∗ G₁) = cong₂ _∗_ (substGvar≡G G) (substGvar≡G G₁)
% substGvar≡G (μ G) = cong μ (trans (cong (subst G) (funext (λ { zero → refl ; (suc i) → refl }))) (substGvar≡G G))
% substGvar≡G (var _) = refl
% 
% substG⊥≡G : {σ : Fin zero → Gram zero} (G : Gram zero) → subst G σ ≡ G
% substG⊥≡G G = trans (cong (subst G) (funext (λ ()))) (substGvar≡G G)
% 
% ≡→↔ : {x y : Set} → x ≡ y → x ↔ y
% ≡→↔ refl = record { to = λ z → z ; from = λ z → z }
% \end{code}

Tying it all together, we show how to parse a string following a grammar. We only care about grammars without variables, so all the environments are empty (\as{λ}~\as{(}\as{)}).
\begin{code}
parse : (G : Gram zero) → (w : String) → Dec (⟦ G ⟧ (λ ()) w)
parse G [] = ν? G (λ ())
parse G (c ∷ cs) = map? (δ?↔δ G (λ ()) (λ ())) (parse (δ? (λ ()) (λ ()) (λ ()) (λ ()) G c) cs)
\end{code}
