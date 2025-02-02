\section{Context-free Languages}\label{sec:context-free}

\begin{code}[hide]
module 3-cfg where

open import Agda.Primitive renaming (Set to Type ; Setω to Typeω)

import Function.Properties.Equivalence as ⇔
import Data.Bool as Bool
open import Data.Bool using (Bool ; true ; false)
open import Data.Char using (Char ; _≟_)
open import Data.List as List hiding (foldl)
open import Data.Empty
open import Data.Product
open import Data.Sum as Sum
open import Data.Unit hiding (_≟_)
open import Relation.Nullary.Decidable as Dec hiding (from-yes ; from-no)
open import Level hiding (zero ; suc)
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Fin hiding (_≟_)
open import Data.Nat hiding (_*_ ; _≟_)
open import Relation.Nullary.Negation
import Data.String as String
open import Agda.Builtin.FromString

open import 2-overview as ◇
\end{code}

\subsection{Syntax}

\begin{code}
data Exp : Type₁ where
    ∅ : Exp
    ε : Exp
    `_ : (c : Char) → Exp
    _·_ : {a : Type} → Dec a → Exp → Exp
    _∪_ : Exp → Exp → Exp
    _*_ : Exp → Exp → Exp
    i : Exp
    μ : Exp → Exp -- explain later
\end{code}
\begin{code}[hide]
infix 22 `_
infixr 21 _*_
infixr 20 _∪_

variable
    n m : ℕ
    l : Lang
    e e₀ : Exp
\end{code}

Mapping syntax onto semantics:

\begin{code}
⟦_⟧₁ : Exp → Lang → Lang
\end{code}
\begin{code}
data ⟦_⟧ (e : Exp) : Lang where
    ∞ : ⟦ e ⟧₁ ⟦ e ⟧ w → ⟦ e ⟧ w
! : ⟦ e ⟧ w → ⟦ e ⟧₁ ⟦ e ⟧ w
! (∞ x) = x
\end{code}
\begin{code}
⟦ ∅ ⟧₁ _ = ◇.∅
⟦ ε ⟧₁ _ = ◇.ε
⟦ ` c ⟧₁ _ = ◇.` c
⟦ x · e ⟧₁ l = x ◇.· ⟦ e ⟧₁ l
⟦ e ∪ e₁ ⟧₁ l = ⟦ e ⟧₁ l ◇.∪ ⟦ e₁ ⟧₁ l
⟦ e * e₁ ⟧₁ l = ⟦ e ⟧₁ l ◇.* ⟦ e₁ ⟧₁ l
⟦ i ⟧₁ l = l
⟦ μ e ⟧₁ _ = ⟦ e ⟧ -- explain this later
\end{code}

\subsection{Goal}

Our goal is to define:

\begin{code}
parse : (e : Exp) (w : String) → Dec (⟦ e ⟧ w)
\end{code}

Our approach uses the decomposition of languages into $\af{ν}$ and $\af{δ}$.
\jr{Now we should explain the $\af{◇ν}$ and $\af{◇δ}$}

\begin{code}
ν : (e : Exp) → Dec (◆.◇ν ⟦ e ⟧)
δ : Char → Exp → Exp
\end{code}

The ν function can easily be written to be correct by construction, however δ must be proven correct separately as follows:

\begin{code}
δ-sound    : ⟦ δ c e ⟧ w   → ◆.◇δ c ⟦ e ⟧ w
δ-complete : ◆.◇δ c ⟦ e ⟧ w → ⟦ δ c e ⟧ w
\end{code}

The actual parsing follows the $\af{ν∘foldlδ}$ decomposition.

\begin{code}[hide]
map' : ∀{A B} → (A → B) → (B → A) → Dec A → Dec B
map' = map′
\end{code}
\begin{code}
parse e [] = ν e
parse e (c ∷ w) = map' δ-sound δ-complete (parse (δ c e) w)
\end{code}

That is the main result of this paper. The remainder of the paper concerns
the implementation of $\af{ν}$, $af{δ}$, $\af{δ-sound}$, and $\af{δ-commplete}$.

\subsection{Nullability correctness}

\begin{lemma}\label{lem:null-sub}
nullability of e substituted in e is the same as the
nullability of e by itself
\begin{code}
νe∅→νee : (e : Exp) → ◆.◇ν (⟦ e ⟧₁ ◇.∅) → ◆.◇ν (⟦ e ⟧₁ ⟦ e₀ ⟧) -- more general than we need, but easy
νee→νe∅ : (e : Exp) → ◆.◇ν (⟦ e ⟧₁ ⟦ e ⟧) → ◆.◇ν (⟦ e ⟧₁ ◇.∅)
\end{code}
\end{lemma}

Syntactic nullability (correct by construction):

\begin{code}
ν₁ : (e : Exp) → Dec (◆.◇ν (⟦ e ⟧₁ ◇.∅))
ν₁ ∅ = no λ ()
ν₁ ε = yes refl
ν₁ (` c) = no λ ()
ν₁ (x · e) = x ×-dec ν₁ e
ν₁ (e ∪ e₁) = ν₁ e ⊎-dec ν₁ e₁
ν₁ (e * e₁) = map' (λ x → [] , [] , refl , x) (λ { ([] , [] , refl , x) → x }) (ν₁ e ×-dec ν₁ e₁)
ν₁ i = no λ ()
ν₁ (μ e) = map' (∞ ∘ νe∅→νee e) (νee→νe∅ e ∘ !) (ν₁ e)
\end{code}

Using \cref{lem:null-sub} we can define $\af{ν}$ in terms of $\af{ν₁}$:
\begin{code}
ν e = map' (∞ ∘ νe∅→νee e) (νee→νe∅ e ∘ !) (ν₁ e)
\end{code}

\jr{TODO: show how ν works through examples}

The forward direction is proven using straightforward induction.

\begin{code}
νe∅→νee ε x = x
νe∅→νee (x₁ · e) (x , y) = x , νe∅→νee e y
νe∅→νee (e ∪ e₁) (inj₁ x) = inj₁ (νe∅→νee e x)
νe∅→νee (e ∪ e₁) (inj₂ y) = inj₂ (νe∅→νee e₁ y)
νe∅→νee (e * e₁) ([] , [] , refl , x , y) = [] , [] , refl , νe∅→νee e x , νe∅→νee e₁ y
νe∅→νee i ()
νe∅→νee (μ e) x = x
\end{code}

The backwards direction requires a bit more work. We use the
following lemma:

\begin{lemma}\label{lem:null-split}
If substituting e₀ into e is nullable then that must mean:
\begin{enumerate}
\item e  by itself was already nullable, or
\item e₀ by itself is nullable
\end{enumerate}

Proof:

\begin{code}
ν-split : (e : Exp) → ◆.◇ν (⟦ e ⟧₁ ⟦ e₀ ⟧) → ◆.◇ν (⟦ e ⟧₁ ◇.∅) ⊎ ◆.◇ν (⟦ e₀ ⟧₁ ◇.∅)
ν-split ε x = inj₁ x
ν-split (_ · e) (x , y) = Sum.map₁ (x ,_) (ν-split e y)
ν-split (e ∪ e₁) (inj₁ x) = Sum.map₁ inj₁ (ν-split e x)
ν-split (e ∪ e₁) (inj₂ y) = Sum.map₁ inj₂ (ν-split e₁ y)
ν-split (e * e₁) ([] , [] , refl , x , y) = lift⊎₂ (λ x y → [] , [] , refl , x , y) (ν-split e x) (ν-split e₁ y)
ν-split {e₀ = e} i (∞ x) = inj₂ (reduce (ν-split e x))
ν-split (μ e) x = inj₁ x
\end{code}
\end{lemma}

The backwards direction of \cref{lem:null-sub} is now simply a result of
\cref{lem:null-split} where both sides of the disjoint union are equal and thus
we can reduce it to a single value.

\begin{code}
νee→νe∅ e x = reduce (ν-split {e₀ = e} e x)
\end{code}

\subsection{Derivative correctness}

\jr{At this point (specifically the $\af{\un{}*\un{}}$ case of $\af{δ₁}$) we need to introduce $\ac{μ}$}

Internal/syntactic substitution:

\begin{code}
sub : Exp → Exp → Exp
sub _ ∅ = ∅
sub _ ε = ε
sub _ (` c) = ` c
sub e₀ (x · e) = x · sub e₀ e
sub e₀ (e ∪ e₁) = sub e₀ e ∪ sub e₀ e₁
sub e₀ (e * e₁) = sub e₀ e * sub e₀ e₁
sub e₀ i = e₀
sub _ (μ e) = μ e
\end{code}

We would like to be able to say \verb|⟦ sub e₀ e ⟧ ≡ ⟦ e ⟧₁ ⟦ e₀ ⟧\verb|, but
we can't because $\ab{e₀}$'s free variable would get (implicitly)
captured. $\ac{μ}$ closes off an expression and thus prevents capture.

\begin{lemma}\label{lem:sub-sem}
(Internal) syntactic substitution is the same as
(external) semantic substitution. This is the raison d'être of μ.

Proof:

\begin{code}
sub-sem' : (e : Exp) → ⟦ sub (μ e₀) e ⟧₁ l ≡ ⟦ e ⟧₁ ⟦ e₀ ⟧
sub-sem' ∅ = refl
sub-sem' ε = refl
sub-sem' (` _) = refl
sub-sem' (x · e) = cong (x ◇.·_) (sub-sem' e) 
sub-sem' (e ∪ e₁) = cong₂ ◇._∪_ (sub-sem' e) (sub-sem' e₁)
sub-sem' (e * e₁) = cong₂ ◇._*_ (sub-sem' e) (sub-sem' e₁)
sub-sem' i = refl
sub-sem' (μ _) = refl
\end{code}

We only need to use this proof in its expanded form:

\begin{code}
sub-sem : (e : Exp) → ⟦ sub (μ e₀) e ⟧₁ l w ≡ ⟦ e ⟧₁ ⟦ e₀ ⟧ w
sub-sem e = cong (λ l → l _) (sub-sem' e)
\end{code}
\end{lemma}

This is the syntactic derivative (the $\ab{e₀}$ argument stands for the whole expression):

\begin{code}
δ₁ : (c : Char) → Exp → Exp → Exp
δ₁ c _ ∅ = ∅
δ₁ c _ ε = ∅
δ₁ c _ (` c₁) = (c ≟ c₁) · ε
δ₁ c e₀ (x · e) = x · δ₁ c e₀ e
δ₁ c e₀ (e ∪ e₁) = δ₁ c e₀ e ∪ δ₁ c e₀ e₁
δ₁ c e₀ (e * e₁) = (δ₁ c e₀ e * sub (μ e₀) e₁) ∪ (Dec.map (⇔.trans (mk⇔ ! ∞) (≡→⇔ (sub-sem e))) (ν (sub (μ e₀) e)) · δ₁ c e₀ e₁)
δ₁ c e₀ i = i
δ₁ c _ (μ e) = μ (δ₁ c e e)
\end{code}

For a top-level expression the derivative is just the open $\af{δ₁}$ where $\ab{e₀}$ is $\ab{e}$ itself:

\begin{code}
δ c e = δ₁ c e e
\end{code}

\jr{todo: show how δ works through examples.}

The proofs are by induction and the \cref{lem:sub-sem}:

\begin{code}
δ-sound' : (e : Exp) → ⟦ δ₁ c e₀ e ⟧₁ ⟦ δ c e₀ ⟧ w → ◆.◇δ c (⟦ e ⟧₁ ⟦ e₀ ⟧) w
δ-sound' (` _) (refl , refl) = refl
δ-sound' (x₁ · e) (x , y) = x , δ-sound' e y
δ-sound' (e ∪ e₁) (inj₁ x) = inj₁ (δ-sound' e x)
δ-sound' (e ∪ e₁) (inj₂ y) = inj₂ (δ-sound' e₁ y)
δ-sound' {c = c} (e * e₁) (inj₁ (u , v , refl , x , y)) = c ∷ u , v , refl , δ-sound' e x , transport (sub-sem e₁) y
δ-sound' {c = c} {w = w} (e * e₁) (inj₂ (x , y)) = [] , c ∷ w , refl , x , δ-sound' e₁ y
δ-sound' {e₀ = e} i (∞ x) = ∞ (δ-sound' e x)
δ-sound' (μ e) (∞ x) = ∞ (δ-sound' e x)
\end{code}

\begin{code}
δ-sound {e = e} (∞ x) = ∞ (δ-sound' e x)
\end{code}

\begin{code}
δ-complete' : (e : Exp) → ◆.◇δ c (⟦ e ⟧₁ ⟦ e₀ ⟧) w → ⟦ δ₁ c e₀ e ⟧₁ ⟦ δ c e₀ ⟧ w
δ-complete' (` _) refl = refl , refl
δ-complete' (_ · e) (x , y) = x , δ-complete' e y
δ-complete' (e ∪ e₁) (inj₁ x) = inj₁ (δ-complete' e x)
δ-complete' (e ∪ e₁) (inj₂ y) = inj₂ (δ-complete' e₁ y)
δ-complete' (e * e₁) (c ∷ u , v , refl , x , y) = inj₁ (u , v , refl , δ-complete' e x , transport (sym (sub-sem e₁)) y)
δ-complete' (e * e₁) ([] , c ∷ w , refl , x , y) = inj₂ (x , δ-complete' e₁ y)
δ-complete' {e₀ = e} i (∞ x) = ∞ (δ-complete' e x)
δ-complete' (μ e) (∞ x) = ∞ (δ-complete' e x)
\end{code}

\begin{code}
δ-complete {e = e} (∞ x) = ∞ (δ-complete' e x)
\end{code}

That's the end of the proof.


% \begin{code}[hide]
% variable V V₁ V₂ V' : Set
% variable k k' n m : ℕ
% 
% data Fin : ℕ → Set where
%     zero : Fin (suc n)
%     suc : Fin n → Fin (suc n)
% 
% ∃-syntax : {A : Set} → (A → Set) → Set
% ∃-syntax {A} B = Σ A B
% 
% syntax ∃-syntax (λ x → A) = ∃[ x ] A
% \end{code}
% 
% Regular languages can be useful for describing patterns in program text, but they are not sufficient to model the full language of a programming language.
% For example, balanced brackets are a common syntactic element in programming languages. 
% 
% \begin{example}
% We can boil the problem down to the following language which consists only of balanced brackets:
% 
% \begin{code}
% bracketsₖ : ℕ → Lang
% bracketsₖ zero _ = ⊥
% bracketsₖ (suc k) w  = (w ≡ [])
%                      ⊎ (∃[ u ] (w ≡ `[ ∷ [] ++ u ++ `] ∷ []) × bracketsₖ k u)
%                      ⊎ (∃[ u ] ∃[ v ] (w ≡ u ++ v) × bracketsₖ k u × bracketsₖ k v)
% \end{code}
% \begin{code}
% brackets : Lang
% brackets w = ∃[ k ] bracketsₖ k w
% \end{code}
% 
% \begin{remark}\label{rem:truncation}
% The \af{bracketsₖ} function is truncated after \ab{k} recursive calls to ensure termination, which is required for all functions in Type theory. The proper language \af{brackets} asserts that, for a string to be in the language, there must exist a \ab{k} which is large enough that the truncation becomes irrelevant for that particular string.
% \end{remark}
% \end{example}
% 
% \subsection{Context-free Grammars}
% 
% This language of balanced brackets is famously context-free. To support languages such as these we add variables, \ac{var}, and fixed points, \ac{μ}, to our grammars.
% \begin{code}
% data Gram (n : ℕ) : Set₁ where
%     ∅ ε : Gram n
%     char : Char → Gram n
%     _·_ : Dec A → Gram n → Gram n
%     _∪_ _∗_ : Gram n → Gram n → Gram n
%     var : Fin n → Gram n
%     μ : Gram (suc n) → Gram n
% \end{code}
% \begin{code}[hide]
% infixr 21 _∗_
% infixr 20 _∪_
% \end{code}
% 
% % TODO: this probably needs more explanation
% 
% \begin{code}[hide]
% variable G G₁ G₂ : Gram n
% variable Γ Γ' : Fin n → Lang
% 
% _∷>_ : {ℓ : Level} {A : Fin (suc n) → Set ℓ} → A zero → ((i : Fin n) → A (suc i)) → ((i : Fin (suc n)) → A i)
% (x ∷> xs) zero = x
% (x ∷> xs) (suc i) = xs i
% \end{code}
% 
% \begin{code}
% ⟦_⟧ₖ : Gram n → (Fin n → Lang) → ℕ → Lang
% \end{code}
% \begin{code}[hide]
% ⟦ ∅ ⟧ₖ Γ _ _ = ⊥
% ⟦ ε ⟧ₖ Γ _ w = w ≡ []
% ⟦ x · G ⟧ₖ Γ k w = ⌊ x ⌋ × ⟦ G ⟧ₖ Γ k w
% ⟦ G₁ ∪ G₂ ⟧ₖ Γ k w = ⟦ G₁ ⟧ₖ Γ k w ⊎ ⟦ G₂ ⟧ₖ Γ k w
% ⟦ G₁ ∗ G₂ ⟧ₖ Γ k w = ∃[ u ] ∃[ v ] (w ≡ (u ++ v)) × ⟦ G₁ ⟧ₖ Γ k u × ⟦ G₂ ⟧ₖ Γ k v
% ⟦ char x ⟧ₖ Γ _ w = w ≡ (x ∷ [])
% \end{code}
% \begin{code}
% ⟦ var i ⟧ₖ Γ k w = Γ i w
% ⟦ μ G ⟧ₖ Γ zero w = ⊥
% ⟦ μ G ⟧ₖ Γ (suc k) w = ⟦ G ⟧ₖ (⟦ μ G ⟧ₖ Γ k ∷> Γ) k w
% \end{code}
% \begin{code}
% ⟦_⟧ : Gram n → (Fin n → Lang) → Lang
% ⟦ G ⟧ Γ w = ∃[ k ] ⟦ G ⟧ₖ Γ k w
% \end{code}
% 
% \begin{example}
% This allows us to write a grammar for the language of balanced brackets.
% \begin{code}
% bracketsG : Gram n
% bracketsG = μ (ε ∪ char `[ ∗ var zero ∗ char `] ∪ var zero ∗ var zero)
% \end{code}
% \end{example}
% 
% \begin{lemma}
% We can map over context and the fuel of the truncated semantics.
% \begin{code}[hide]
% max : ℕ → ℕ → ℕ
% max zero k' = k'
% max (suc k) zero = suc k
% max (suc k) (suc k') = suc (max k k')
% 
% data _≤_ : ℕ → ℕ → Set where
%     z≤m : zero ≤ m
%     s≤s : n ≤ m → suc n ≤ suc m
% 
% ≤refl : n ≤ n
% ≤refl {n = zero} = z≤m
% ≤refl {n = suc n} = s≤s ≤refl
% 
% n≤maxnm : (n m : ℕ) → n ≤ max n m
% n≤maxnm zero m = z≤m
% n≤maxnm (suc n) zero = ≤refl
% n≤maxnm (suc n) (suc m) = s≤s (n≤maxnm n m)
% 
% m≤maxnm : (n m : ℕ) → m ≤ max n m
% m≤maxnm n zero = z≤m
% m≤maxnm zero (suc m) = ≤refl
% m≤maxnm (suc n) (suc m) = s≤s (m≤maxnm n m)
% 
% \end{code}
% \begin{code}
% mapΓ  : (G : Gram n) (Γ Γ' : Fin n → Lang) 
%       → ((i : Fin n) → {w : String} → Γ i w → Γ' i w)
%       → ⟦ G ⟧ₖ Γ k w → ⟦ G ⟧ₖ Γ' k w
% \end{code}
% \begin{code}[hide]
% mapΓ ε Γ Γ' f x = x
% mapΓ (char x₁) Γ Γ' f x = x
% mapΓ (x₁ · G) Γ Γ' f (x , y) = x , mapΓ G Γ Γ' f y
% mapΓ (G₁ ∪ G₂) Γ Γ' f (inl x) = inl (mapΓ G₁ Γ Γ' f x)
% mapΓ (G₁ ∪ G₂) Γ Γ' f (inr x) = inr (mapΓ G₂ Γ Γ' f x)
% mapΓ (G₁ ∗ G₂) Γ Γ' f (u , v , refl , x , y) = u , v , refl , mapΓ G₁ Γ Γ' f x , mapΓ G₂ Γ Γ' f y
% mapΓ (var i) Γ Γ' f x = f i x
% mapΓ {k = suc k} (μ G) Γ Γ' f x = mapΓ G _ _ (λ { zero → mapΓ {k = k} (μ G) Γ Γ' f ; (suc i) → f i }) x
% 
% \end{code}
% \begin{code}
% mapk : k ≤ k' → ⟦ G ⟧ₖ Γ k w → ⟦ G ⟧ₖ Γ k' w
% \end{code}
% \begin{code}[hide]
% mapk {G = ε} k≤k' x = x
% mapk {G = char x₁} k≤k' x = x
% mapk {G = x₁ · G} k≤k' (x , y) = x , mapk {G = G} k≤k' y
% mapk {G = G₁ ∪ G₂} k≤k' (inl x) = inl (mapk {G = G₁} k≤k' x)
% mapk {G = G₁ ∪ G₂} k≤k' (inr x) = inr (mapk {G = G₂} k≤k' x)
% mapk {G = G₁ ∗ G₂} k≤k' (u , v , refl , x , y) = u , v , refl , mapk {G = G₁} k≤k' x , mapk {G = G₂} k≤k' y
% mapk {G = var i} k≤k' x = x
% mapk {G = μ G} (s≤s k≤k') x = mapk {G = G} k≤k' (mapΓ G _ _ (λ { zero → mapk {G = μ G} k≤k' ; (suc i) → λ z → z}) x)
% 
% weakenˡ : ⟦ G ⟧ₖ Γ k w → ⟦ G ⟧ₖ Γ (max k k') w
% weakenˡ {G = G} {k = k} {k' = k'} = mapk {G = G} (n≤maxnm k k')
% 
% weakenʳ : ⟦ G ⟧ₖ Γ k' w → ⟦ G ⟧ₖ Γ (max k k') w
% weakenʳ {G = G} {k' = k'} {k = k} = mapk {G = G} (m≤maxnm k k')
% \end{code}
% \end{lemma}
% 
% \begin{lemma}
% We can map a change of variables over a grammar and we can substitute variables. This essentially shows that grammars form a relative monad.
% \begin{code}
% rename : (Fin n → Fin m) → Gram n → Gram m
% \end{code}
% \begin{code}[hide]
% rename _ ∅ = ∅
% rename _ ε = ε
% rename _ (char c) = char c
% rename f (x · G) = x · rename f G
% rename f (G₁ ∪ G₂) = rename f G₁ ∪ rename f G₂
% rename f (G₁ ∗ G₂) = rename f G₁ ∗ rename f G₂
% rename f (var i) = var (f i)
% rename f (μ G) = μ (rename (λ { zero → zero ; (suc i) → suc (f i) }) G)
% \end{code}
% \begin{code}
% subst : Gram n → (Fin n → Gram m) → Gram m
% \end{code}
% \begin{code}[hide]
% subst ∅ σ = ∅
% subst ε σ = ε
% subst (char c) σ = char c
% subst (x · G) σ = x · subst G σ
% subst (G ∪ G₁) σ = subst G σ ∪ subst G₁ σ
% subst (G ∗ G₁) σ = subst G σ ∗ subst G₁ σ
% subst (var x) σ = σ x
% subst (μ G) σ = μ (subst G λ { zero → var zero ; (suc i) → rename suc (σ i) })
% \end{code}
% \end{lemma}
% 
% \subsection{Parsing}\label{sec:cfg-parsing}
% 
% Parsing our context-free grammar follows the same structure as the simple grammars from \cref{sec:gram-and-parsing}. Concretely, we define functions that compute the nullability, \af{ν?}, and derivatives, \af{δ?}. For this section we have taken inspiration from a blog post by Grenrus~\cite{fix-ing-regular-expressions}.
% 
% \begin{example}\label{ex:cfg-parsing}
% Let us consider the balanced bracket grammar example. We can see that it is nullable because it contains an \ac{ε} in the fixed point. It is also possible to parse the empty string by taking one iteration of the fixed point using the \ac{var}~\ac{zero}~∗~\ac{var}~\ac{zero} part and then the \ac{ε} for both recursive calls, but note that we always need to end in an empty base case. Thus, for a fixed point to be nullable, it must be nullable even if we do not consider the recursive calls.
% 
% The derivative of the balanced bracket grammar can be taken with respect to any character, but only the character \ac{`[} results in anything interesting because any string in the balanced bracket language needs to start with an opening bracket. The first thing we might try is to unroll the fixed point one step, yielding the following grammar:
% \begin{code}
% bracketsG₁ : Gram n
% bracketsG₁ = ε ∪ char `[ ∗ bracketsG ∗ char `] ∪ bracketsG ∗ bracketsG
% \end{code}
% We know how to take the derivative of the first two parts, but \af{bracketsG}~\ac{∗}~\af{bracketsG} seems problematic because its derivative depends on the derivative of \af{bracketsG} itself. Luckily, we can introduce a new fixed point when describing the derivative to refer to the derivative itself.
% \begin{code}
% bracketsG' : Gram n
% bracketsG' = μ (bracketsG ∗ char `] ∪ var zero ∗ bracketsG)
% \end{code}
% \end{example}
% 
% \subsubsection{Nullability}
% 
% Computing the nullability now requires us to deal with grammars that contain free variables, but we can make use of a context \ab{Γν} which tells us how to compute the nullability of those variables.
% 
% \begin{code}
% ν? : (G : Gram n) (Γν : (i : Fin n) → Dec (ν (Γ i))) → Dec (ν (⟦ G ⟧ Γ))
% \end{code}
% The simple cases remain the same except that \ab{Γν} now has to be passed properly to recursive calls. We skip to the two new cases: variables and fixed points.
% \begin{code}[hide]
% ν▹ : (ν (⟦ G₁ ⟧ Γ) × ν (⟦ G₂ ⟧ Γ)) ↔ ν (⟦ G₁ ∗ G₂ ⟧ Γ)
% to (ν▹ {G₁ = G₁} {G₂ = G₂}) ((n , x) , (m , y)) = max n m , [] , [] , refl , weakenˡ {G = G₁} x , weakenʳ {G = G₂} y
% from ν▹ (n , [] , [] , refl , x , y) = (n , x) , (n , y)
% 
% -- refold : (G : Gram (suc n)) → ⟦ G ⟧ (⟦ μ G ⟧ Γ ∷> Γ) ⇔ ⟦ μ G ⟧ Γ
% -- to (refold G) x = {!!}
% -- from (refold G) (suc k , x) = k , mapΓ G _ _ (λ { zero → k ,_ ; (suc i) → λ z → z }) x
% n≤sucn : n ≤ suc n
% n≤sucn {zero} = z≤m
% n≤sucn {suc n} = s≤s n≤sucn
% 
% variable i : Fin n
% \end{code}
% For both cases we need a helper. In the case of variables this helper just deals with converting between the truncated semantics and the proper semantics.
% \begin{code}
% νΓi↔ν⟦vari⟧Γ : ν (Γ i) ↔ ν (⟦ var i ⟧ Γ)
% to νΓi↔ν⟦vari⟧Γ x = zero , x
% from νΓi↔ν⟦vari⟧Γ (_ , x) = x
% \end{code}
% For the fixed point, we need to formalize the intuition from \cref{ex:cfg-parsing}. Recall that we noted how determining the nullability of a fixed point only requires unrolling it once and no more.
% \begin{code}
% νG⊥↔νμG  : ν (⟦ G ⟧ ((λ _ → ⊥) ∷> Γ)) ↔ ν (⟦ μ G ⟧ Γ)
% \end{code}
% We are still working on a proof of this property, but we have been able to reduce it to the following postulate which states that, if a grammar with free variables is nullable, either the nullability is independent of that variable, or that variable itself needs to be nullable.
% \begin{code}
% postulate νGℒ→νG⊥⊎νℒ  : ν (⟦ G ⟧ₖ (ℒ ∷> Γ) k) → ν (⟦ G ⟧ₖ ((λ _ → ⊥) ∷> Γ) k) ⊎ ν ℒ
% \end{code}
% \begin{code}[hide]
% νGμG→νG⊥  : ν (⟦ G ⟧ₖ (⟦ μ G ⟧ₖ Γ k ∷> Γ) k) → ν (⟦ G ⟧ₖ ((λ _ → ⊥) ∷> Γ) k)
% νGμG→νG⊥ {G = G} x with νGℒ→νG⊥⊎νℒ {G = G} x
% ... | inl x = x
% νGμG→νG⊥ {G = G} {k = suc k} _ | inr x = mapk {G = G} n≤sucn (νGμG→νG⊥ {G = G} {k = k} x)
% \end{code}
% \begin{code}[hide]
% to (νG⊥↔νμG {G = G}) (k , x) = suc k , mapΓ G _ _ (λ { zero → λ () ; (suc _) → λ z → z }) x
% from (νG⊥↔νμG {G = G}) (suc k , x) = k , νGμG→νG⊥ {G = G} x
% 
% \end{code}
% \begin{code}[hide]
% ν? ∅ _ = no λ ()
% ν? ε _ = yes (zero , refl)
% ν? (char c) _ = no λ ()
% ν? (x · G) Γν = map? (record { to = λ (x , n , y) → (n , x , y) ; from = λ (n , x , y) → (x , n , y) }) (x ×? ν? G Γν)
% ν? (G₁ ∪ G₂) Γν = map? (record { to = λ { (inl (n , x)) → n , inl x ; (inr (n , x)) → n , inr x } ; from = λ { (n , inl x) → inl (n , x) ; (n , inr x) → inr (n , x) } }) (ν? G₁ Γν ⊎? ν? G₂ Γν)
% ν? (G₁ ∗ G₂) Γν = map? (ν▹ {G₁ = G₁} {G₂ = G₂}) (ν? G₁ Γν ×? ν? G₂ Γν)
% \end{code}
% Using these two helpers, we can define the nullability of variables and fixed points as follows:
% \begin{code}
% ν? {Γ = Γ} (var i) Γν = map? (νΓi↔ν⟦vari⟧Γ {Γ = Γ}) (Γν i)
% ν? (μ G) Γν = map? νG⊥↔νμG (ν? G (no (λ ()) ∷> Γν))
% \end{code}
% 
% \subsubsection{Derivatives}
% 
% Computing the derivative also requires us to deal with free variables in our grammar. For derivatives, we need to keep track of four different environments:
% 
% \begin{enumerate}
% \item The language environment, \ab{Γ}, which contains the language of each variable.
% \item The nullability environment, \ab{Γν}, which tells us the nullability of all variables.
% \item The derivative environment, \ab{Γδ}, which keeps track of the derivative of each variable.
% \item The unrolling environment, \ab{Γσ}, which allows us to replace each variable by the fixed point that bound it, thus unrolling the fixed point.
% \end{enumerate}
% 
% The \af{Gram} data Type is no longer parameterized by its semantics, so we first define a syntactic derivative function \af{δ?} and afterwards prove that it corresponds to the semantic derivative.
% \begin{code}
% δ?  : (Γ : Fin n → Lang) (Γν : (i : Fin n) → Dec (ν (Γ i))) (Γδ : Fin n → Gram m) 
%       (Γσ : Fin n → Gram m) 
%     → Gram n → Char → Gram m
% \end{code}
% Again, all simple cases are the same except for passing around the environments correctly to recursive calls, so we skip to the two new cases for variables and fixed points.
% \begin{code}[hide]
% δ? _ _ _ _ ∅ c = ∅
% δ? _ _ _ _ ε c = ∅
% δ? _ _ _ _ (char c') c with c ≟ c'
% ... | yes _ = ε
% ... | no _ = ∅
% δ? Γ Γν Γδ Γσ (A · G) c = A · δ? Γ Γν Γδ Γσ G c
% δ? Γ Γν Γδ Γσ (G₁ ∪ G₂) c = δ? Γ Γν Γδ Γσ G₁ c ∪ δ? Γ Γν Γδ Γσ G₂ c
% δ? Γ Γν Γδ Γσ (G₁ ∗ G₂) c =  (δ? Γ Γν Γδ Γσ G₁ c ∗ subst G₂ Γσ)
%                           ∪  (ν? {Γ = Γ} G₁ Γν · δ? Γ Γν Γδ Γσ G₂ c)
% \end{code}
% For variables, we simply look up their derivative in the derivative environment. For fixed points, we need to show how to extend each of the four environments. Here we apply the same trick as we discovered in \cref{ex:cfg-parsing}, namely that we introduce a new fixed point which allows us to refer to the derivative itself.
% \begin{code}
% δ? _ _ Γδ _ (var i) _ = Γδ i
% δ? Γ Γν Γδ Γσ (μ G) c =
%   μ (δ?  (⟦ μ G ⟧ Γ                      ∷> Γ)
%          (ν? {Γ = Γ} (μ G) Γν            ∷> Γν)
%          (var zero                       ∷> (rename suc ∘ Γδ))
%          (subst (μ G) (rename suc ∘ Γσ)  ∷> (rename suc ∘ Γσ))
%          G c)
% \end{code}
% \begin{code}[hide]
% 
% ↔refl : A ↔ A
% ↔refl = record { to = λ x → x ; from = λ z → z }
% 
% \end{code}
% 
% We show the correctness of the syntactic derivative by showing that every string accepted by the result of taking the syntactic derivative of a grammar is also accepted by the semantic derivative of the original grammar and vice versa. The last two arguments specify that the unrolling and derivative environment actually contain what they are supposed to contain.
% \begin{code}
% δ?↔δ : (G : Gram n) {Γ : Fin n → Lang} {Γ' : Fin m → Lang} 
%        {Γν : (i : Fin n) → Dec (ν (Γ i))} {Γδ : Fin n → Gram m} {Γσ : Fin n → Gram m}
%      → ((i : Fin n) → ⟦ Γσ i ⟧ Γ' ⇔ Γ i)
%      → ((i : Fin n) → ⟦ Γδ i ⟧ Γ' ⇔ δ (Γ i) c)
%      → ⟦ δ? Γ Γν Γδ Γσ G c ⟧ Γ' ⇔ δ (⟦ G ⟧ Γ) c
% \end{code}
% We are still working on proofs for two parts of this correspondence. First, if a substitution corresponds pointwise to a change of environment, substituting all variables in a grammar also corresponds to a change of environment.
% \begin{code}
% postulate substΓσ  : {Γσ : Fin n → Gram m} (G : Gram n)
%                    → ((i : Fin n) → ⟦ Γσ i ⟧ Γ' ⇔ Γ i) → ⟦ subst G Γσ ⟧ Γ' ⇔ ⟦ G ⟧ Γ
% \end{code}
% Second, we are still working on proving the correctness of the syntactic derivative of fixed points.
% \begin{code}
% postulate
%   δ?↔δμ  : (G : Gram (suc n)) {Γ : Fin n → Lang} {Γ' : Fin m → Lang} 
%            {Γν : (i : Fin n) → Dec (ν (Γ i))} {Γδ : Fin n → Gram m} {Γσ : Fin n → Gram m}
%          → ((i : Fin n) → ⟦ Γσ i ⟧ Γ' ⇔ Γ i)
%          → ((i : Fin n) → ⟦ Γδ i ⟧ Γ' ⇔ δ (Γ i) c)
%          → ⟦ δ? Γ Γν Γδ Γσ (μ G) c ⟧ Γ' ⇔ δ (⟦ μ G ⟧ Γ) c
% \end{code}
% \begin{code}[hide]
% δ?↔δ ∅ eσ eδ = ↔refl
% to (δ?↔δ ε eσ eδ) ()
% from (δ?↔δ ε eσ eδ) ()
% 
% to (δ?↔δ {c = c}     (char c') eσ eδ) x with c ≟ c'
% to (δ?↔δ {c = c}     (char .c) eσ eδ) (k , refl) | yes refl = k , refl
% to (δ?↔δ             (char _)  eσ eδ) () | no _
% to (δ?↔δ             (A · G)   eσ eδ) (k , x , y) with to (δ?↔δ G eσ eδ) (k , y)
% ... | k , y = k , x , y 
% to (δ?↔δ             (G₁ ∪ G₂) eσ eδ) (k , inl x) with to (δ?↔δ G₁ eσ eδ) (k , x)
% ... | k , x = k , inl x
% to (δ?↔δ             (G₁ ∪ G₂) eσ eδ) (k , inr x) with to (δ?↔δ G₂ eσ eδ) (k , x)
% ... | k , x = k , inr x
% to (δ?↔δ {c = c}     (G₁ ∗ G₂) eσ eδ) (k , inl (u , v , refl , x , y)) with to (δ?↔δ G₁ eσ eδ) (k , x) | to (substΓσ G₂ eσ) (k , y)
% ... | k₁ , x | k₂ , y = max k₁ k₂ , (c ∷ u) , v , refl , weakenˡ {G = G₁} x , weakenʳ {G = G₂} y
% to (δ?↔δ {c = c} (G₁ ∗ G₂) eσ eδ) (k , inr (x , y)) with x | to (δ?↔δ G₂ eσ eδ) (k , y)
% ... | k₁ , x | k₂ , y = max k₁ k₂ , [] , (c ∷ _) , refl , weakenˡ {G = G₁} x , weakenʳ {G = G₂} y
% to (δ?↔δ           (var i)   eσ eδ) (k , x) = zero , to (eδ i) (k , x)
% from (δ?↔δ {c = c} (char c') eσ eδ) x with c ≟ c'
% from (δ?↔δ {c = c} (char c)  eσ eδ) (k , refl) | yes refl = k , refl
% from (δ?↔δ {c = c} (char .c) eσ eδ) (k , refl) | no ¬c≡c = k , ¬c≡c refl
% from (δ?↔δ         (A · G)   eσ eδ) (k , x , y) with from (δ?↔δ G eσ eδ) (k , y)
% ... | k , y = k , x , y
% from (δ?↔δ         (G₁ ∪ G₂) eσ eδ) (k , inl x) with from (δ?↔δ G₁ eσ eδ) (k , x)
% ... | k , x = k , inl x
% from (δ?↔δ         (G₁ ∪ G₂) eσ eδ) (k , inr x) with from (δ?↔δ G₂ eσ eδ) (k , x)
% ... | k , x = k , inr x
% from (δ?↔δ {c = c} (G₁ ∗ G₂) eσ eδ) (k , [] , (.c ∷ v) , refl , x , y) with from (δ?↔δ G₂ eσ eδ) (k , y)
% ... | k' , y = k' , inr ((k , x) , y)
% from (δ?↔δ {c = c} (G₁ ∗ G₂) eσ eδ) (k , (.c ∷ u) , v , refl , x , y) with from (δ?↔δ G₁ eσ eδ) (k , x) | from (substΓσ G₂ eσ) (k , y)
% ... | k₁ , x | k₂ , y = max k₁ k₂ , inl (u , v , refl , weakenˡ {G = δ? _ _ _ _ G₁ c} x , weakenʳ {G = subst G₂ _} y)
% from (δ?↔δ         (var i)   eσ eδ) (k , x) = from (eδ i) x
% 
% δ?↔δ (μ G) eσ eδ = δ?↔δμ G eσ eδ
% \end{code}
% With the exception of these two postulates, we have proven the correctness of our syntactic derivative function.
% % \begin{code}[hide]
% % substGvar≡G : (G : Gram n) → subst G var ≡ G
% % substGvar≡G ∅ = refl
% % substGvar≡G ε = refl
% % substGvar≡G (char x) = refl
% % substGvar≡G (x · G) = cong (x ·_) (substGvar≡G G)
% % substGvar≡G (G ∪ G₁) = cong₂ _∪_ (substGvar≡G G) (substGvar≡G G₁)
% % substGvar≡G (G ∗ G₁) = cong₂ _∗_ (substGvar≡G G) (substGvar≡G G₁)
% % substGvar≡G (μ G) = cong μ (trans (cong (subst G) (funext (λ { zero → refl ; (suc i) → refl }))) (substGvar≡G G))
% % substGvar≡G (var _) = refl
% % 
% % substG⊥≡G : {σ : Fin zero → Gram zero} (G : Gram zero) → subst G σ ≡ G
% % substG⊥≡G G = trans (cong (subst G) (funext (λ ()))) (substGvar≡G G)
% % 
% % ≡→↔ : {x y : Set} → x ≡ y → x ↔ y
% % ≡→↔ refl = record { to = λ z → z ; from = λ z → z }
% % \end{code}
% 
% \subsubsection{Parsing}
% 
% Tying it all together, we show how to parse a string following a grammar. We only care about grammars without variables, so all the environments are empty (\as{λ}~\as{(}\as{)}).
% \begin{code}
% parse : (G : Gram zero) → (w : String) → Dec (⟦ G ⟧ (λ ()) w)
% parse G [] = ν? G (λ ())
% parse G (c ∷ cs) = map? (δ?↔δ G (λ ()) (λ ())) (parse (δ? (λ ()) (λ ()) (λ ()) (λ ()) G c) cs)
% \end{code}
% This is a correct parser for context-free grammars.
% 