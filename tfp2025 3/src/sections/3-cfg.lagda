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
open import Data.Product as Prod
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

\subsection{Fixed Points}

\jr{Make it clear that we depart from Elliott's work at this point.}
\begin{itemize}
\item If $\ab{F}~\as{:}~\af{Type}~\as{→}~\af{Type}$ is a strictly positive functor, then we know its fixed point is well-defined.
\item So we could restrict the argument of our fixed point combinator to only accept strictly positive functors.
\item We are dealing with languages and not types directly, but luckily our definition of language is based on types and our basic combinators are strictly positive.
\item One catch is that Agda currently has no way of directly expressing that a functor is strictly positive.\footnote{There is work on implementing positivity annotations.}
\item We can still make this evident to Agda by defining a data type of descriptions such as those used in the paper "gentle art of levitation".\jr{todo: cite this}
\end{itemize}

\begin{code}[hide]
module F where
\end{code}

\begin{code}
    data Desc : Type₁ where
        ∅    : Desc
        ε    : Desc
        `_   : Char → Desc
        _∪_  : Desc → Desc → Desc
        _∗_  : Desc → Desc → Desc
        -- We need Dec if we want to be able to write parsers
        -- but for specifiction it is not really needed
        _·_  : {A : Type} → Dec A → Desc → Desc
        var  : Desc
\end{code}

\begin{code}[hide]
    infix 22 `_
    infixr 21 _∗_
    infix 21 _·_
    infixr 20 _∪_
\end{code}

We can give semantics to our descriptions in terms of languages that we defined in the previous section.\jr{todo: proper ref}

\begin{code}
    ⟦_⟧ₒ : Desc → ◇.Lang → ◇.Lang
    ⟦ ∅ ⟧ₒ        = const ◇.∅
    ⟦ ε ⟧ₒ        = const ◇.ε
    ⟦ ` c ⟧ₒ      = const (◇.` c) 
    ⟦ D₁ ∪ D₂ ⟧ₒ P  = ⟦ D₁ ⟧ₒ P ◇.∪ ⟦ D₂ ⟧ₒ P
    ⟦ D₁ ∗ D₂ ⟧ₒ P  = ⟦ D₁ ⟧ₒ P ◇.∗ ⟦ D₂ ⟧ₒ P
    ⟦ _·_ {A} _ D ⟧ₒ P  = A ◇.· ⟦ D ⟧ₒ P 
    ⟦ var ⟧ₒ P    = P
\end{code}

Using these descriptions, we can define a fixed point as follows:

\begin{code}
    data ⟦_⟧ (D : Desc) : ◇.Lang where
        step : ⟦ D ⟧ₒ ⟦ D ⟧ w → ⟦ D ⟧ w
\end{code}

So we can finally define the brackets language.\footnote{We split this definition into two because we want to separately reuse the description later.}\jr{Brackets is one example, but can we characterise the whole class of languages we can define using these descriptions?}

\begin{code}
    bracketsD = ε ∪ ` '[' ∗ var ∗ ` ']' ∪ var ∗ var
    brackets = ⟦ bracketsD ⟧
\end{code}

This representation is not modular, however. We cannot nest fixed points in
descriptions.\jr{This modularity and nesting is not clear enough.} This problem comes up naturally when considering reduction, which we discuss next.

\subsection{Reduction by Example}

As we have seen with finite languages in \cref{sec:finite-languages}, when writing parsers it is useful to consider how a language changes after one character has been parsed. We will call this \emph{reduction}. For example, we could consider what happens to our brackets languages after one opening brackets has been parsed: $\af{δ}~\aS{'['}~\af{brackets}$. In this section, we search for a description of this reduced language (the \emph{reduct}).

We can mechanically derive this new language from the brackets definition by
going over each of the disjuncts. The first disjunct, epsilon, does not play a
role because we know the string contains at least the opening bracket. The
second disjunct, brackets surrounding a self-reference, is trickier. The opening
bracket clearly matches, but it would be a mistake to say the new disjunct
should be a self-reference followed by a closing bracket.\jr{Show the code, not just words!}

Note that the self-reference in the new language would refer to the derivative
of the old language, not to the old language itself. We would like to refer to
the original bracket language, for example like this
$\af{brackets}~\ac{∗}~\ac{`}~\aS{']'}$, but we cannot nest the brackets language
into another description.

There are cases where we do want to use self-reference in the new language.
Consider the third disjunct, $\ac{var}~\ac{∗}~\ac{var}$. It is a sequence so we
expect from the finite case of \cref{sec:finite-languages} that matching one character results in
two new disjuncts: one where the first sequent matches the empty string and the
second is reduced and one where the first is reduced and the second is
unchanged.\jr{Why? That is what we saw in Section 2} In this case both sequents are self-references, so we need to know
three things: 
%
\begin{enumerate}
\item Does the original language match the empty string?
\item What is the reduct of the language? (With reduct I mean the new language that results after one character is matched.)
\item What does it mean for the language to remain the same?
\end{enumerate}
%
At first glance, the last point seems obvious, but remember that we are reducing
the language, so self-references will change meaning even if they remain
unchanged. Similarly to the previous disjunct, we want to refer to the original
brackets in this case. To resolve this issue of referring to the original brackets expression, we introduce a new combinator $\ac{μ}$, which has the meaning of locally taking a fixed point of a subexpression.
%
\begin{code}[hide]
module F2 where
\end{code}
\begin{AgdaAlign}
\vspace{\abovedisplayskip}
\AgdaNoSpaceAroundCode{}
\begin{code}
    data Desc : Type₁ where
        -- ...
\end{code}%
\begin{code}[hide]
        ∅    : Desc
        ε    : Desc
        `_   : Char → Desc
        _∪_  : Desc → Desc → Desc
        _∗_  : Desc → Desc → Desc
        -- We need Dec if we want to be able to write parsers
        -- but for specifiction it is not really needed
        _·_  : {A : Type} → Dec A → Desc → Desc
        var  : Desc
\end{code}%
\begin{code}
        μ : Desc → Desc
\end{code}
\AgdaSpaceAroundCode{}
\end{AgdaAlign}
%
\begin{code}[hide]
    variable D D₀ D₁ D₂ : Desc
    infix 22 `_
    infixr 21 _∗_
    infix 21 _·_
    infixr 20 _∪_
\end{code}
%
\begin{AgdaAlign}
\AgdaNoSpaceAroundCode{}
\begin{code}
    ⟦_⟧ₒ : Desc → ◇.Lang → ◇.Lang
    -- ...
\end{code}
\begin{code}[hide]
    data ⟦_⟧ (X : Desc) : ◇.Lang where
        step : ⟦ X ⟧ₒ ⟦ X ⟧ w → ⟦ X ⟧ w
    ⟦ ∅ ⟧ₒ        = const ◇.∅
    ⟦ ε ⟧ₒ        = const ◇.ε
    ⟦ ` c ⟧ₒ      = const (◇.` c) 
    ⟦ X ∪ Y ⟧ₒ P  = ⟦ X ⟧ₒ P ◇.∪ ⟦ Y ⟧ₒ P
    ⟦ X ∗ Y ⟧ₒ P  = ⟦ X ⟧ₒ P ◇.∗ ⟦ Y ⟧ₒ P
    ⟦ _·_ {A} _ X ⟧ₒ P  = A ◇.· ⟦ X ⟧ₒ P 
    ⟦ var ⟧ₒ P    = P
\end{code}
\begin{code}
    ⟦ μ D ⟧ₒ _    = ⟦ D ⟧
\end{code}
\AgdaSpaceAroundCode{}
\vspace{\belowdisplayskip}
\end{AgdaAlign}
\jr{How is this used in our example?}

The first question is easy to answer: yes, the first disjunct of brackets is epsilon which matches the empty string.
%
\begin{code}[hide]
    bracketsD = ε ∪ ` '[' ∗ var ∗ ` ']' ∪ var ∗ var
    brackets = ⟦ bracketsD ⟧
\end{code}
\begin{code}
    νbrackets : Dec (◇.ν brackets)
    νbrackets = yes (step (inj₁ refl))
\end{code}

The second question is where having a self-reference in the new language is useful. We can refer to the reduct of brackets by using self-reference.

This enables us to write the reduct of brackets with respect to the opening bracket.

\begin{code}
    bracketsD'  = μ bracketsD ∗ ` ']' ∪ νbrackets · var ∪ var ∗ μ bracketsD
    brackets'   = ⟦ bracketsD' ⟧
\end{code}

Conclusion:
\begin{itemize}
\item We can reuse many of the results of finite languages (\cref{sec:finite-languages}).
\item We need a new $\ac{μ}$ combinator to nest fixed points in descriptions. This is necessary to refer back to the original language before reduction.
\item Reducing a self-reference simply results in a self-reference again, because self-references in the reduct refer to the reduct.
\end{itemize}
Again, we do not want to have to do this reduction manually. Instead, we show
how to do it in general for any description in the next section.

\subsection{Parsing in General}

Our goal is to define:

\begin{code}
    parse : ∀ D → ◇.Parser ⟦ D ⟧
\end{code}

We approach this by decomposing parsing into $\af{ν}$ and $\af{δ}$.

\begin{code}
    νD : ∀ D → Dec (◇.ν ⟦ D ⟧)
    δD : Char → Desc → Desc
\end{code}

The $\af{νD}$ function can easily be written to be correct by construction, however $\af{δD}$ must be proven correct separately as follows:

\begin{code}
    δD-correct : ⟦ δD c D ⟧ ◇.⟺ ◇.δ c ⟦ D ⟧
\end{code}

The actual parsing can now be done character by character:

\begin{code}
    parse D [] = νD D
    parse D (c ∷ w) = Dec.map δD-correct (parse (δD c D) w)
\end{code}

That is the main result of this paper. The remainder of the paper concerns
the implementation of $\af{νD}$, $\af{δD}$, $\af{δD-correct}$.

\subsection{Implementation and Proof}

\begin{lemma}
The nullability of a fixed point is determined completely by a single application of the underlying functor to the empty language.
\begin{code}
    νD∅⇔νD : ◇.ν (⟦ D ⟧ₒ ◇.∅) ⇔ ◇.ν ⟦ D ⟧
    νD∅⇔νD = {!   !}
\end{code}
\end{lemma}

\begin{code}
    νD∅ : ∀ D → Dec (◇.ν (⟦ D ⟧ₒ ◇.∅))
    νD∅ ∅         = no λ ()
    νD∅ ε         = yes refl
    νD∅ (` x)     = no λ ()
    νD∅ (D ∪ D₁)  = νD∅ D ⊎-dec νD∅ D₁
    νD∅ (D ∗ D₁)  = Dec.map ◇.ν∗ (νD∅ D ×-dec νD∅ D₁)
    νD∅ (x · D)   = x ×-dec νD∅ D
    νD∅ var       = no λ ()
    νD∅ (μ D)     = Dec.map νD∅⇔νD (νD∅ D)
\end{code}
\begin{code}
    νD D = Dec.map νD∅⇔νD (νD∅ D)
\end{code}
\begin{code}
    σD : Desc → Desc → Desc
    σD ∅         D' = ∅
    σD ε         D' = ε
    σD (` c)     D' = ` c
    σD (D ∪ D₁)  D' = σD D D' ∪ σD D₁ D'
    σD (D ∗ D₁)  D' = σD D D' ∗ σD D₁ D'
    σD (x · D)   D' = x · σD D D'
    σD var       D' = D'
    σD (μ D)     D' = μ D
\end{code}
\begin{code}
    δDₒ : Desc → Char → Desc → Desc
    δDₒ D₀ c ∅         = ∅
    δDₒ D₀ c ε         = ∅
    δDₒ D₀ c (` c')    = (c ≟ c') · ε
    δDₒ D₀ c (D ∪ D₁)  = δDₒ D₀ c D ∪ δDₒ D₀ c D₁
    δDₒ D₀ c (D ∗ D₁)  = νD D · δDₒ D₀ c D₁ ∪ δDₒ D₀ c D ∗ σD D₁ D₀
    δDₒ D₀ c (x · D)   = x · δDₒ D₀ c D
    δDₒ D₀ c var       = var
    δDₒ D₀ c (μ D)     = μ (δDₒ D c D)
\end{code}
\begin{code}
    δD c D = δDₒ D c D
\end{code}
\begin{code}
    δD-correct = {!   !}
\end{code}

% \begin{code}
%     variable D D₀ : Desc
%     variable P : ◇.Lang
% 
%     νD : (D : Desc) → Dec (◇.ν ⟦ D ⟧)
%     νD D = {!   !}
% 
%     δD : ∀ c → (D : Desc) → Σ Desc (λ D' → ⟦ D' ⟧ₒ (◇.δ c ⟦ D ⟧) ◇.⟺ ◇.δ c (⟦ D ⟧ₒ ⟦ D ⟧))
%     δD _ ∅ = ∅ , ⇔.refl
%     δD _ ε = ∅ , ◇.δε
%     δD c (` c') = (c ≟ c') · ε , ◇.δ`
%     δD c (D ∪ D₁) = {!   !}
%     δD c (D ∗ D₁) = {!   !}
%     δD c (x · D) = {! !}
%     δD c var = var , ⇔.refl
% 
%     -- -- This does not work out. Consider the union case. Which split should it
%     -- -- report?  We have to choose one, but that excludes the other which could
%     -- -- be the one we actually want.
%     -- -- If the parser is required to parse the whole input, then it is
%     -- -- not possible to make the wrong choice.
%     -- Parser : ◇.Lang → Type
%     -- Parser P = (w : String) → Dec (∃[ u ] ∃[ v ] w ≡ u ++ v × P u)
% 
%     -- ⟦_⟧ₒ-parse : ∀ D → Parser (⟦ D ⟧ₒ P)
%     -- ⟦ ∅ ⟧ₒ-parse _ = no λ { (_ , _ , ()) }
%     -- ⟦ ε ⟧ₒ-parse w = yes ([] , w , refl , refl)
%     -- ⟦ ` c' ⟧ₒ-parse [] = no λ { ([] , [] , refl , ()) }
%     -- ⟦ ` c' ⟧ₒ-parse (c ∷ w) = Dec.map
%     --   (mk⇔ 
%     --     (λ { refl → c ∷ [] , w , refl , refl })
%     --     (λ { (.(c ∷ []) , .w , refl , refl) → refl }))
%     --   (c ≟ c')
%     -- ⟦ D ∪ D₁ ⟧ₒ-parse w = Dec.map {!   !} (⟦ D ⟧ₒ-parse w ×-dec ⟦ D₁ ⟧ₒ-parse w)
%     -- ⟦ D ∗ D₁ ⟧ₒ-parse = {!   !}
%     -- ⟦ x · D ⟧ₒ-parse = {!   !}
%     -- ⟦ var ⟧ₒ-parse = {!   !}
% 
%     -- ⟦_⟧ₒ-parse : ∀ D → ◇.Parser (⟦ D ⟧ₒ ⟦ D ⟧)
%     -- ⟦ ∅ ⟧ₒ-parse = ◇.∅-parse
%     -- ⟦ ε ⟧ₒ-parse = ◇.ε-parse
%     -- ⟦ ` c ⟧ₒ-parse = ◇.`-parse c
%     -- ⟦ D ∪ D₁ ⟧ₒ-parse = ⟦ D ⟧ₒ-parse ◇.∪-parse ⟦ D₁ ⟧ₒ-parse
%     -- ⟦ D ∗ D₁ ⟧ₒ-parse = ⟦ D ⟧ₒ-parse ◇.∗-parse ⟦ D₁ ⟧ₒ-parse
%     -- ⟦ x · D ⟧ₒ-parse = x ◇.·-parse ⟦ D ⟧ₒ-parse
%     -- ⟦ var ⟧ₒ-parse [] = {!   !}
%     -- ⟦ var ⟧ₒ-parse (c ∷ w) = ⟦ var ⟧ₒ-parse w
% 
%     -- ⟦_⟧-parse : ∀ D → ◇.Parser ⟦ D ⟧
%     -- ⟦ D ⟧-parse = Dec.map (mk⇔ step (λ { (step x) → x })) ∘ ⟦ D ⟧ₒ-parse
% \end{code}
% 
% % Practice for the indexed thing
% \begin{code}[hide]
%     open Equivalence using (to ; from)
% 
%     distrib : ∀{ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} 
%             → (A ⊎ C) × (B ⊎ C) → (A × B) ⊎ C
%     distrib (inj₁ x , inj₁ y) = inj₁ (x , y)
%     distrib (inj₁ _ , inj₂ y) = inj₂ y
%     distrib (inj₂ x , _) = inj₂ x
% 
%     ν⟦⟧ : ◇.ν (⟦ D ⟧ₒ ◇.∅) ⇔ ◇.ν ⟦ D ⟧
%     ν⟦⟧ {D = D} = mk⇔ (λ { x → step (go→ {D₀ = D} D x) }) λ { (step x) → reduce (go← {D₀ = D} D x) } where
% 
%       go→ : ∀ D → ◇.ν (⟦ D ⟧ₒ ◇.∅) → ◇.ν (⟦ D ⟧ₒ ⟦ D₀ ⟧)
%       go→ ε refl = refl
%       go→ (D ∪ D₁) (inj₁ x) = inj₁ (go→ D x)
%       go→ (D ∪ D₁) (inj₂ y) = inj₂ (go→ D₁ y)
%       go→ (D ∗ D₁) ([] , [] , refl , x , y) = [] , [] , refl , go→ D x , go→ D₁ y
%       go→ (A · D) (x , y) = x , go→ D y
% 
%       go← : ∀ D → ◇.ν (⟦ D ⟧ₒ ⟦ D₀ ⟧) → ◇.ν (⟦ D ⟧ₒ ◇.∅) ⊎ ◇.ν (⟦ D₀ ⟧ₒ ◇.∅)
%       go← ε refl = inj₁ refl
%       go← (D ∪ D₁) (inj₁ x) = Sum.map₁ inj₁ (go← D x)
%       go← (D ∪ D₁) (inj₂ y) = Sum.map₁ inj₂ (go← D₁ y)
%       go← (D ∗ D₁) ([] , [] , refl , x , y) = Sum.map₁ (λ x → [] , [] , refl , x) (distrib (go← D x , go← D₁ y))
%       go← (A · D) (x , y) = Sum.map₁ (x ,_) (go← D y)
%       go← {D₀ = D} var (step x) = inj₂ (reduce (go← D x))
% 
%     -- there is not a simple way to define this
%     -- δ⟦⟧ : ? ◇.⟺ ◇.δ c ⟦ D ⟧
% \end{code}
% 
% However, we often want more than just one nonterminal, so we need to generalize to indexed descriptors.
% 
% \begin{code}[hide]
% module IDesc where
%     variable I : Type
% \end{code}
% 
% \begin{code}
%     data IDesc (I : Type) : Type₁ where
%         ∅    : IDesc I
%         ε    : IDesc I
%         `_   : Char → IDesc I
%         _∪_  : IDesc I → IDesc I → IDesc I
%         _∗_  : IDesc I → IDesc I → IDesc I
%         _·_  : Type → IDesc I → IDesc I
%         var  : I → IDesc I
% \end{code}
% 
% \begin{code}
%     ⟦_⟧ₒ : IDesc I → (I → ◇.Lang) → ◇.Lang
%     ⟦ ∅ ⟧ₒ        = const ◇.∅
%     ⟦ ε ⟧ₒ        = const ◇.ε
%     ⟦ ` c ⟧ₒ      = const (◇.` c) 
%     ⟦ X ∪ Y ⟧ₒ P  = ⟦ X ⟧ₒ P ◇.∪ ⟦ Y ⟧ₒ P
%     ⟦ X ∗ Y ⟧ₒ P  = ⟦ X ⟧ₒ P ◇.∗ ⟦ Y ⟧ₒ P
%     ⟦ x · X ⟧ₒ P  = x ◇.· ⟦ X ⟧ₒ P 
%     ⟦ var i ⟧ₒ P  = P i
% \end{code}
% 
% 
% 
% \begin{code}[hide]
%     data 𝟏+_ (I : Type) : Type where
%         here : 𝟏+ I
%         there : I → 𝟏+ I
% \end{code}
% 
% \begin{code}
%     variable D D₀ : IDesc I
%     variable Γ : I → ◇.Lang
%     cons : A → (I → A) → (𝟏+ I → A)
%     cons x Γ here = x
%     cons x Γ (there i) = Γ i
%     data ⟦_⟧ (D : IDesc (𝟏+ I)) (Γ : I → ◇.Lang) : ◇.Lang where
%         step : ⟦ D ⟧ₒ (cons (⟦ D ⟧ Γ) Γ) w → ⟦ D ⟧ Γ w
% \end{code}
% 
% \begin{code}[hide]
%     distrib : ∀{ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} 
%             → (A ⊎ C) × (B ⊎ C) → (A × B) ⊎ C
%     distrib (inj₁ x , inj₁ y) = inj₁ (x , y)
%     distrib (inj₁ _ , inj₂ y) = inj₂ y
%     distrib (inj₂ x , _) = inj₂ x
% 
%     ν⟦⟧ : ◇.ν (⟦ D ⟧ₒ (cons ◇.∅ Γ)) ⇔ ◇.ν (⟦ D ⟧ Γ)
%     ν⟦⟧ {D = D} = mk⇔ (λ { x → step (go→ {D₀ = D} D x) }) λ { (step x) → reduce (go← {D₀ = D} D x) } where
% 
%       go→ : ∀ D → ◇.ν (⟦ D ⟧ₒ (cons ◇.∅ Γ)) → ◇.ν (⟦ D ⟧ₒ (cons (⟦ D₀ ⟧ Γ) Γ))
%       go→ ε refl = refl
%       go→ (D ∪ D₁) (inj₁ x) = inj₁ (go→ D x)
%       go→ (D ∪ D₁) (inj₂ y) = inj₂ (go→ D₁ y)
%       go→ (D ∗ D₁) ([] , [] , refl , x , y) = [] , [] , refl , go→ D x , go→ D₁ y
%       go→ (A · D) (x , y) = x , go→ D y
%       go→ (var (there i)) x = x
% 
%       go← : ∀ D → ◇.ν (⟦ D ⟧ₒ (cons (⟦ D₀ ⟧ Γ) Γ)) → ◇.ν (⟦ D ⟧ₒ (cons ◇.∅ Γ)) ⊎ ◇.ν (⟦ D₀ ⟧ₒ (cons ◇.∅ Γ))
%       go← ε refl = inj₁ refl
%       go← (D ∪ D₁) (inj₁ x) = Sum.map₁ inj₁ (go← D x)
%       go← (D ∪ D₁) (inj₂ y) = Sum.map₁ inj₂ (go← D₁ y)
%       go← (D ∗ D₁) ([] , [] , refl , x , y) = Sum.map₁ (λ x → [] , [] , refl , x) (distrib (go← D x , go← D₁ y))
%       go← (A · D) (x , y) = Sum.map₁ (x ,_) (go← D y)
%       go← {D₀ = D} (var here) (step x) = inj₂ (reduce (go← D x))
%       go← {D₀ = D} (var (there i)) x = inj₁ x
% 
%     data Δ (I : Type) : Type where
%         normal : I → Δ I
%         delta : I → Δ I
% 
%     δ_⟦_⟧ₒ : Char → IDesc I → (Δ I → ◇.Lang) → ◇.Lang
%     δ c ⟦ ∅ ⟧ₒ        = const ◇.∅
%     δ c ⟦ ε ⟧ₒ        = const ◇.∅
%     δ c ⟦ ` c' ⟧ₒ     = const ((c ≡ c') ◇.· ◇.ε)
%     (δ c ⟦ X ∪ Y ⟧ₒ) P  = δ c ⟦ X ⟧ₒ P ◇.∪ δ c ⟦ Y ⟧ₒ P
%     (δ c ⟦ X ∗ Y ⟧ₒ) P  = ◇.ν (⟦ X ⟧ₒ (P ∘ normal)) ◇.· (δ c ⟦ Y ⟧ₒ) P ◇.∪ (δ c ⟦ X ⟧ₒ) P ◇.∗ ⟦ Y ⟧ₒ (P ∘ normal)
%     (δ c ⟦ x · X ⟧ₒ) P  = x ◇.· δ c ⟦ X ⟧ₒ P 
%     (δ c ⟦ var i ⟧ₒ) P  = P (delta i)
% 
%     withΔ : Char → (I → ◇.Lang) → (Δ I → ◇.Lang)
%     withΔ _ Γ (normal i) = Γ i
%     withΔ c Γ (delta i) = ◇.δ c (Γ i)
% 
%     δ⟦⟧ : {I : Type} {Γ : I → ◇.Lang} {D : IDesc (𝟏+ I)} {c : Char}
%         → (δ c ⟦ D ⟧ₒ) (withΔ c (cons (⟦ D ⟧ Γ) Γ)) ◇.⟺ ◇.δ c (⟦ D ⟧ Γ)
%     δ⟦⟧ = {!   !}
% \end{code}
% 
% 
% % \subsection{Syntax}
% % 
% % \begin{code}
% % data Exp : Type₁ where
% %     ∅ : Exp
% %     ε : Exp
% %     `_ : (c : Char) → Exp
% %     _·_ : {a : Type} → Dec a → Exp → Exp
% %     _∪_ : Exp → Exp → Exp
% %     _*_ : Exp → Exp → Exp
% %     i : Exp
% %     μ : Exp → Exp -- explain later
% % \end{code}
% % \begin{code}[hide]
% % infix 22 `_
% % infixr 21 _*_
% % infixr 20 _∪_
% % 
% % variable
% %     n m : ℕ
% %     l : Lang
% %     e e₀ : Exp
% % \end{code}
% % 
% % Mapping syntax onto semantics:
% % 
% % \begin{code}
% % ⟦_⟧₁ : Exp → Lang → Lang
% % \end{code}
% % \begin{code}
% % data ⟦_⟧ (e : Exp) : Lang where
% %     ∞ : ⟦ e ⟧₁ ⟦ e ⟧ w → ⟦ e ⟧ w
% % ! : ⟦ e ⟧ w → ⟦ e ⟧₁ ⟦ e ⟧ w
% % ! (∞ x) = x
% % \end{code}
% % \begin{code}
% % ⟦ ∅ ⟧₁ _ = ◇.∅
% % ⟦ ε ⟧₁ _ = ◇.ε
% % ⟦ ` c ⟧₁ _ = ◇.` c
% % ⟦ x · e ⟧₁ l = x ◇.· ⟦ e ⟧₁ l
% % ⟦ e ∪ e₁ ⟧₁ l = ⟦ e ⟧₁ l ◇.∪ ⟦ e₁ ⟧₁ l
% % ⟦ e * e₁ ⟧₁ l = ⟦ e ⟧₁ l ◇.* ⟦ e₁ ⟧₁ l
% % ⟦ i ⟧₁ l = l
% % ⟦ μ e ⟧₁ _ = ⟦ e ⟧ -- explain this later
% % \end{code}
% % 
% % \subsection{Goal}
% % 
% % Our goal is to define:
% % 
% % \begin{code}
% % parse : (e : Exp) (w : String) → Dec (⟦ e ⟧ w)
% % \end{code}
% % 
% % Our approach uses the decomposition of languages into $\af{ν}$ and $\af{δ}$.
% % \jr{Now we should explain the $\af{◇ν}$ and $\af{◇δ}$}
% % 
% % \begin{code}
% % ν : (e : Exp) → Dec (◆.◇ν ⟦ e ⟧)
% % δ : Char → Exp → Exp
% % \end{code}
% % 
% % The ν function can easily be written to be correct by construction, however δ must be proven correct separately as follows:
% % 
% % \begin{code}
% % δ-sound    : ⟦ δ c e ⟧ w   → ◆.◇δ c ⟦ e ⟧ w
% % δ-complete : ◆.◇δ c ⟦ e ⟧ w → ⟦ δ c e ⟧ w
% % \end{code}
% % 
% % The actual parsing follows the $\af{ν∘foldlδ}$ decomposition.
% % 
% % \begin{code}[hide]
% % map' : ∀{A B} → (A → B) → (B → A) → Dec A → Dec B
% % map' = map′
% % \end{code}
% % \begin{code}
% % parse e [] = ν e
% % parse e (c ∷ w) = map' δ-sound δ-complete (parse (δ c e) w)
% % \end{code}
% % 
% % That is the main result of this paper. The remainder of the paper concerns
% % the implementation of $\af{ν}$, $af{δ}$, $\af{δ-sound}$, and $\af{δ-commplete}$.
% % 
% % \subsection{Nullability correctness}
% % 
% % \begin{lemma}\label{lem:null-sub}
% % nullability of e substituted in e is the same as the
% % nullability of e by itself
% % \begin{code}
% % νe∅→νee : (e : Exp) → ◆.◇ν (⟦ e ⟧₁ ◇.∅) → ◆.◇ν (⟦ e ⟧₁ ⟦ e₀ ⟧) -- more general than we need, but easy
% % νee→νe∅ : (e : Exp) → ◆.◇ν (⟦ e ⟧₁ ⟦ e ⟧) → ◆.◇ν (⟦ e ⟧₁ ◇.∅)
% % \end{code}
% % \end{lemma}
% % 
% % Syntactic nullability (correct by construction):
% % 
% % \begin{code}
% % ν₁ : (e : Exp) → Dec (◆.◇ν (⟦ e ⟧₁ ◇.∅))
% % ν₁ ∅ = no λ ()
% % ν₁ ε = yes refl
% % ν₁ (` c) = no λ ()
% % ν₁ (x · e) = x ×-dec ν₁ e
% % ν₁ (e ∪ e₁) = ν₁ e ⊎-dec ν₁ e₁
% % ν₁ (e * e₁) = map' (λ x → [] , [] , refl , x) (λ { ([] , [] , refl , x) → x }) (ν₁ e ×-dec ν₁ e₁)
% % ν₁ i = no λ ()
% % ν₁ (μ e) = map' (∞ ∘ νe∅→νee e) (νee→νe∅ e ∘ !) (ν₁ e)
% % \end{code}
% % 
% % Using \cref{lem:null-sub} we can define $\af{ν}$ in terms of $\af{ν₁}$:
% % \begin{code}
% % ν e = map' (∞ ∘ νe∅→νee e) (νee→νe∅ e ∘ !) (ν₁ e)
% % \end{code}
% % 
% % \jr{TODO: show how ν works through examples}
% % 
% % The forward direction is proven using straightforward induction.
% % 
% % \begin{code}
% % νe∅→νee ε x = x
% % νe∅→νee (x₁ · e) (x , y) = x , νe∅→νee e y
% % νe∅→νee (e ∪ e₁) (inj₁ x) = inj₁ (νe∅→νee e x)
% % νe∅→νee (e ∪ e₁) (inj₂ y) = inj₂ (νe∅→νee e₁ y)
% % νe∅→νee (e * e₁) ([] , [] , refl , x , y) = [] , [] , refl , νe∅→νee e x , νe∅→νee e₁ y
% % νe∅→νee i ()
% % νe∅→νee (μ e) x = x
% % \end{code}
% % 
% % The backwards direction requires a bit more work. We use the
% % following lemma:
% % 
% % \begin{lemma}\label{lem:null-split}
% % If substituting e₀ into e is nullable then that must mean:
% % \begin{enumerate}
% % \item e  by itself was already nullable, or
% % \item e₀ by itself is nullable
% % \end{enumerate}
% % 
% % Proof:
% % 
% % \begin{code}
% % ν-split : (e : Exp) → ◆.◇ν (⟦ e ⟧₁ ⟦ e₀ ⟧) → ◆.◇ν (⟦ e ⟧₁ ◇.∅) ⊎ ◆.◇ν (⟦ e₀ ⟧₁ ◇.∅)
% % ν-split ε x = inj₁ x
% % ν-split (_ · e) (x , y) = Sum.map₁ (x ,_) (ν-split e y)
% % ν-split (e ∪ e₁) (inj₁ x) = Sum.map₁ inj₁ (ν-split e x)
% % ν-split (e ∪ e₁) (inj₂ y) = Sum.map₁ inj₂ (ν-split e₁ y)
% % ν-split (e * e₁) ([] , [] , refl , x , y) = lift⊎₂ (λ x y → [] , [] , refl , x , y) (ν-split e x) (ν-split e₁ y)
% % ν-split {e₀ = e} i (∞ x) = inj₂ (reduce (ν-split e x))
% % ν-split (μ e) x = inj₁ x
% % \end{code}
% % \end{lemma}
% % 
% % The backwards direction of \cref{lem:null-sub} is now simply a result of
% % \cref{lem:null-split} where both sides of the disjoint union are equal and thus
% % we can reduce it to a single value.
% % 
% % \begin{code}
% % νee→νe∅ e x = reduce (ν-split {e₀ = e} e x)
% % \end{code}
% % 
% % \subsection{Derivative correctness}
% % 
% % \jr{At this point (specifically the $\af{\un{}*\un{}}$ case of $\af{δ₁}$) we need to introduce $\ac{μ}$}
% % 
% % Internal/syntactic substitution:
% % 
% % \begin{code}
% % sub : Exp → Exp → Exp
% % sub _ ∅ = ∅
% % sub _ ε = ε
% % sub _ (` c) = ` c
% % sub e₀ (x · e) = x · sub e₀ e
% % sub e₀ (e ∪ e₁) = sub e₀ e ∪ sub e₀ e₁
% % sub e₀ (e * e₁) = sub e₀ e * sub e₀ e₁
% % sub e₀ i = e₀
% % sub _ (μ e) = μ e
% % \end{code}
% % 
% % We would like to be able to say \verb|⟦ sub e₀ e ⟧ ≡ ⟦ e ⟧₁ ⟦ e₀ ⟧\verb|, but
% % we can't because $\ab{e₀}$'s free variable would get (implicitly)
% % captured. $\ac{μ}$ closes off an expression and thus prevents capture.
% % 
% % \begin{lemma}\label{lem:sub-sem}
% % (Internal) syntactic substitution is the same as
% % (external) semantic substitution. This is the raison d'être of μ.
% % 
% % Proof:
% % 
% % \begin{code}
% % sub-sem' : (e : Exp) → ⟦ sub (μ e₀) e ⟧₁ l ≡ ⟦ e ⟧₁ ⟦ e₀ ⟧
% % sub-sem' ∅ = refl
% % sub-sem' ε = refl
% % sub-sem' (` _) = refl
% % sub-sem' (x · e) = cong (x ◇.·_) (sub-sem' e) 
% % sub-sem' (e ∪ e₁) = cong₂ ◇._∪_ (sub-sem' e) (sub-sem' e₁)
% % sub-sem' (e * e₁) = cong₂ ◇._*_ (sub-sem' e) (sub-sem' e₁)
% % sub-sem' i = refl
% % sub-sem' (μ _) = refl
% % \end{code}
% % 
% % We only need to use this proof in its expanded form:
% % 
% % \begin{code}
% % sub-sem : (e : Exp) → ⟦ sub (μ e₀) e ⟧₁ l w ≡ ⟦ e ⟧₁ ⟦ e₀ ⟧ w
% % sub-sem e = cong (λ l → l _) (sub-sem' e)
% % \end{code}
% % \end{lemma}
% % 
% % This is the syntactic derivative (the $\ab{e₀}$ argument stands for the whole expression):
% % 
% % \begin{code}
% % δ₁ : (c : Char) → Exp → Exp → Exp
% % δ₁ c _ ∅ = ∅
% % δ₁ c _ ε = ∅
% % δ₁ c _ (` c₁) = (c ≟ c₁) · ε
% % δ₁ c e₀ (x · e) = x · δ₁ c e₀ e
% % δ₁ c e₀ (e ∪ e₁) = δ₁ c e₀ e ∪ δ₁ c e₀ e₁
% % δ₁ c e₀ (e * e₁) = (δ₁ c e₀ e * sub (μ e₀) e₁) ∪ (Dec.map (⇔.trans (mk⇔ ! ∞) (≡→⇔ (sub-sem e))) (ν (sub (μ e₀) e)) · δ₁ c e₀ e₁)
% % δ₁ c e₀ i = i
% % δ₁ c _ (μ e) = μ (δ₁ c e e)
% % \end{code}
% % 
% % For a top-level expression the derivative is just the open $\af{δ₁}$ where $\ab{e₀}$ is $\ab{e}$ itself:
% % 
% % \begin{code}
% % δ c e = δ₁ c e e
% % \end{code}
% % 
% % \jr{todo: show how δ works through examples.}
% % 
% % The proofs are by induction and the \cref{lem:sub-sem}:
% % 
% % \begin{code}
% % δ-sound' : (e : Exp) → ⟦ δ₁ c e₀ e ⟧₁ ⟦ δ c e₀ ⟧ w → ◆.◇δ c (⟦ e ⟧₁ ⟦ e₀ ⟧) w
% % δ-sound' (` _) (refl , refl) = refl
% % δ-sound' (x₁ · e) (x , y) = x , δ-sound' e y
% % δ-sound' (e ∪ e₁) (inj₁ x) = inj₁ (δ-sound' e x)
% % δ-sound' (e ∪ e₁) (inj₂ y) = inj₂ (δ-sound' e₁ y)
% % δ-sound' {c = c} (e * e₁) (inj₁ (u , v , refl , x , y)) = c ∷ u , v , refl , δ-sound' e x , transport (sub-sem e₁) y
% % δ-sound' {c = c} {w = w} (e * e₁) (inj₂ (x , y)) = [] , c ∷ w , refl , x , δ-sound' e₁ y
% % δ-sound' {e₀ = e} i (∞ x) = ∞ (δ-sound' e x)
% % δ-sound' (μ e) (∞ x) = ∞ (δ-sound' e x)
% % \end{code}
% % 
% % \begin{code}
% % δ-sound {e = e} (∞ x) = ∞ (δ-sound' e x)
% % \end{code}
% % 
% % \begin{code}
% % δ-complete' : (e : Exp) → ◆.◇δ c (⟦ e ⟧₁ ⟦ e₀ ⟧) w → ⟦ δ₁ c e₀ e ⟧₁ ⟦ δ c e₀ ⟧ w
% % δ-complete' (` _) refl = refl , refl
% % δ-complete' (_ · e) (x , y) = x , δ-complete' e y
% % δ-complete' (e ∪ e₁) (inj₁ x) = inj₁ (δ-complete' e x)
% % δ-complete' (e ∪ e₁) (inj₂ y) = inj₂ (δ-complete' e₁ y)
% % δ-complete' (e * e₁) (c ∷ u , v , refl , x , y) = inj₁ (u , v , refl , δ-complete' e x , transport (sym (sub-sem e₁)) y)
% % δ-complete' (e * e₁) ([] , c ∷ w , refl , x , y) = inj₂ (x , δ-complete' e₁ y)
% % δ-complete' {e₀ = e} i (∞ x) = ∞ (δ-complete' e x)
% % δ-complete' (μ e) (∞ x) = ∞ (δ-complete' e x)
% % \end{code}
% % 
% % \begin{code}
% % δ-complete {e = e} (∞ x) = ∞ (δ-complete' e x)
% % \end{code}
% % 
% % That's the end of the proof.
% % 
% % 
% % % \begin{code}[hide]
% % % variable V V₁ V₂ V' : Set
% % % variable k k' n m : ℕ
% % % 
% % % data Fin : ℕ → Set where
% % %     zero : Fin (suc n)
% % %     suc : Fin n → Fin (suc n)
% % % 
% % % ∃-syntax : {A : Set} → (A → Set) → Set
% % % ∃-syntax {A} B = Σ A B
% % % 
% % % syntax ∃-syntax (λ x → A) = ∃[ x ] A
% % % \end{code}
% % % 
% % % Regular languages can be useful for describing patterns in program text, but they are not sufficient to model the full language of a programming language.
% % % For example, balanced brackets are a common syntactic element in programming languages. 
% % % 
% % % \begin{example}
% % % We can boil the problem down to the following language which consists only of balanced brackets:
% % % 
% % % \begin{code}
% % % bracketsₖ : ℕ → Lang
% % % bracketsₖ zero _ = ⊥
% % % bracketsₖ (suc k) w  = (w ≡ [])
% % %                      ⊎ (∃[ u ] (w ≡ `[ ∷ [] ++ u ++ `] ∷ []) × bracketsₖ k u)
% % %                      ⊎ (∃[ u ] ∃[ v ] (w ≡ u ++ v) × bracketsₖ k u × bracketsₖ k v)
% % % \end{code}
% % % \begin{code}
% % % brackets : Lang
% % % brackets w = ∃[ k ] bracketsₖ k w
% % % \end{code}
% % % 
% % % \begin{remark}\label{rem:truncation}
% % % The \af{bracketsₖ} function is truncated after \ab{k} recursive calls to ensure termination, which is required for all functions in Type theory. The proper language \af{brackets} asserts that, for a string to be in the language, there must exist a \ab{k} which is large enough that the truncation becomes irrelevant for that particular string.
% % % \end{remark}
% % % \end{example}
% % % 
% % % \subsection{Context-free Grammars}
% % % 
% % % This language of balanced brackets is famously context-free. To support languages such as these we add variables, \ac{var}, and fixed points, \ac{μ}, to our grammars.
% % % \begin{code}
% % % data Gram (n : ℕ) : Set₁ where
% % %     ∅ ε : Gram n
% % %     char : Char → Gram n
% % %     _·_ : Dec A → Gram n → Gram n
% % %     _∪_ _∗_ : Gram n → Gram n → Gram n
% % %     var : Fin n → Gram n
% % %     μ : Gram (suc n) → Gram n
% % % \end{code}
% % % \begin{code}[hide]
% % % infixr 21 _∗_
% % % infixr 20 _∪_
% % % \end{code}
% % % 
% % % % TODO: this probably needs more explanation
% % % 
% % % \begin{code}[hide]
% % % variable G G₁ G₂ : Gram n
% % % variable Γ Γ' : Fin n → Lang
% % % 
% % % _∷>_ : {ℓ : Level} {A : Fin (suc n) → Set ℓ} → A zero → ((i : Fin n) → A (suc i)) → ((i : Fin (suc n)) → A i)
% % % (x ∷> xs) zero = x
% % % (x ∷> xs) (suc i) = xs i
% % % \end{code}
% % % 
% % % \begin{code}
% % % ⟦_⟧ₖ : Gram n → (Fin n → Lang) → ℕ → Lang
% % % \end{code}
% % % \begin{code}[hide]
% % % ⟦ ∅ ⟧ₖ Γ _ _ = ⊥
% % % ⟦ ε ⟧ₖ Γ _ w = w ≡ []
% % % ⟦ x · G ⟧ₖ Γ k w = ⌊ x ⌋ × ⟦ G ⟧ₖ Γ k w
% % % ⟦ G₁ ∪ G₂ ⟧ₖ Γ k w = ⟦ G₁ ⟧ₖ Γ k w ⊎ ⟦ G₂ ⟧ₖ Γ k w
% % % ⟦ G₁ ∗ G₂ ⟧ₖ Γ k w = ∃[ u ] ∃[ v ] (w ≡ (u ++ v)) × ⟦ G₁ ⟧ₖ Γ k u × ⟦ G₂ ⟧ₖ Γ k v
% % % ⟦ char x ⟧ₖ Γ _ w = w ≡ (x ∷ [])
% % % \end{code}
% % % \begin{code}
% % % ⟦ var i ⟧ₖ Γ k w = Γ i w
% % % ⟦ μ G ⟧ₖ Γ zero w = ⊥
% % % ⟦ μ G ⟧ₖ Γ (suc k) w = ⟦ G ⟧ₖ (⟦ μ G ⟧ₖ Γ k ∷> Γ) k w
% % % \end{code}
% % % \begin{code}
% % % ⟦_⟧ : Gram n → (Fin n → Lang) → Lang
% % % ⟦ G ⟧ Γ w = ∃[ k ] ⟦ G ⟧ₖ Γ k w
% % % \end{code}
% % % 
% % % \begin{example}
% % % This allows us to write a grammar for the language of balanced brackets.
% % % \begin{code}
% % % bracketsG : Gram n
% % % bracketsG = μ (ε ∪ char `[ ∗ var zero ∗ char `] ∪ var zero ∗ var zero)
% % % \end{code}
% % % \end{example}
% % % 
% % % \begin{lemma}
% % % We can map over context and the fuel of the truncated semantics.
% % % \begin{code}[hide]
% % % max : ℕ → ℕ → ℕ
% % % max zero k' = k'
% % % max (suc k) zero = suc k
% % % max (suc k) (suc k') = suc (max k k')
% % % 
% % % data _≤_ : ℕ → ℕ → Set where
% % %     z≤m : zero ≤ m
% % %     s≤s : n ≤ m → suc n ≤ suc m
% % % 
% % % ≤refl : n ≤ n
% % % ≤refl {n = zero} = z≤m
% % % ≤refl {n = suc n} = s≤s ≤refl
% % % 
% % % n≤maxnm : (n m : ℕ) → n ≤ max n m
% % % n≤maxnm zero m = z≤m
% % % n≤maxnm (suc n) zero = ≤refl
% % % n≤maxnm (suc n) (suc m) = s≤s (n≤maxnm n m)
% % % 
% % % m≤maxnm : (n m : ℕ) → m ≤ max n m
% % % m≤maxnm n zero = z≤m
% % % m≤maxnm zero (suc m) = ≤refl
% % % m≤maxnm (suc n) (suc m) = s≤s (m≤maxnm n m)
% % % 
% % % \end{code}
% % % \begin{code}
% % % mapΓ  : (G : Gram n) (Γ Γ' : Fin n → Lang) 
% % %       → ((i : Fin n) → {w : String} → Γ i w → Γ' i w)
% % %       → ⟦ G ⟧ₖ Γ k w → ⟦ G ⟧ₖ Γ' k w
% % % \end{code}
% % % \begin{code}[hide]
% % % mapΓ ε Γ Γ' f x = x
% % % mapΓ (char x₁) Γ Γ' f x = x
% % % mapΓ (x₁ · G) Γ Γ' f (x , y) = x , mapΓ G Γ Γ' f y
% % % mapΓ (G₁ ∪ G₂) Γ Γ' f (inl x) = inl (mapΓ G₁ Γ Γ' f x)
% % % mapΓ (G₁ ∪ G₂) Γ Γ' f (inr x) = inr (mapΓ G₂ Γ Γ' f x)
% % % mapΓ (G₁ ∗ G₂) Γ Γ' f (u , v , refl , x , y) = u , v , refl , mapΓ G₁ Γ Γ' f x , mapΓ G₂ Γ Γ' f y
% % % mapΓ (var i) Γ Γ' f x = f i x
% % % mapΓ {k = suc k} (μ G) Γ Γ' f x = mapΓ G _ _ (λ { zero → mapΓ {k = k} (μ G) Γ Γ' f ; (suc i) → f i }) x
% % % 
% % % \end{code}
% % % \begin{code}
% % % mapk : k ≤ k' → ⟦ G ⟧ₖ Γ k w → ⟦ G ⟧ₖ Γ k' w
% % % \end{code}
% % % \begin{code}[hide]
% % % mapk {G = ε} k≤k' x = x
% % % mapk {G = char x₁} k≤k' x = x
% % % mapk {G = x₁ · G} k≤k' (x , y) = x , mapk {G = G} k≤k' y
% % % mapk {G = G₁ ∪ G₂} k≤k' (inl x) = inl (mapk {G = G₁} k≤k' x)
% % % mapk {G = G₁ ∪ G₂} k≤k' (inr x) = inr (mapk {G = G₂} k≤k' x)
% % % mapk {G = G₁ ∗ G₂} k≤k' (u , v , refl , x , y) = u , v , refl , mapk {G = G₁} k≤k' x , mapk {G = G₂} k≤k' y
% % % mapk {G = var i} k≤k' x = x
% % % mapk {G = μ G} (s≤s k≤k') x = mapk {G = G} k≤k' (mapΓ G _ _ (λ { zero → mapk {G = μ G} k≤k' ; (suc i) → λ z → z}) x)
% % % 
% % % weakenˡ : ⟦ G ⟧ₖ Γ k w → ⟦ G ⟧ₖ Γ (max k k') w
% % % weakenˡ {G = G} {k = k} {k' = k'} = mapk {G = G} (n≤maxnm k k')
% % % 
% % % weakenʳ : ⟦ G ⟧ₖ Γ k' w → ⟦ G ⟧ₖ Γ (max k k') w
% % % weakenʳ {G = G} {k' = k'} {k = k} = mapk {G = G} (m≤maxnm k k')
% % % \end{code}
% % % \end{lemma}
% % % 
% % % \begin{lemma}
% % % We can map a change of variables over a grammar and we can substitute variables. This essentially shows that grammars form a relative monad.
% % % \begin{code}
% % % rename : (Fin n → Fin m) → Gram n → Gram m
% % % \end{code}
% % % \begin{code}[hide]
% % % rename _ ∅ = ∅
% % % rename _ ε = ε
% % % rename _ (char c) = char c
% % % rename f (x · G) = x · rename f G
% % % rename f (G₁ ∪ G₂) = rename f G₁ ∪ rename f G₂
% % % rename f (G₁ ∗ G₂) = rename f G₁ ∗ rename f G₂
% % % rename f (var i) = var (f i)
% % % rename f (μ G) = μ (rename (λ { zero → zero ; (suc i) → suc (f i) }) G)
% % % \end{code}
% % % \begin{code}
% % % subst : Gram n → (Fin n → Gram m) → Gram m
% % % \end{code}
% % % \begin{code}[hide]
% % % subst ∅ σ = ∅
% % % subst ε σ = ε
% % % subst (char c) σ = char c
% % % subst (x · G) σ = x · subst G σ
% % % subst (G ∪ G₁) σ = subst G σ ∪ subst G₁ σ
% % % subst (G ∗ G₁) σ = subst G σ ∗ subst G₁ σ
% % % subst (var x) σ = σ x
% % % subst (μ G) σ = μ (subst G λ { zero → var zero ; (suc i) → rename suc (σ i) })
% % % \end{code}
% % % \end{lemma}
% % % 
% % % \subsection{Parsing}\label{sec:cfg-parsing}
% % % 
% % % Parsing our context-free grammar follows the same structure as the simple grammars from \cref{sec:gram-and-parsing}. Concretely, we define functions that compute the nullability, \af{ν?}, and derivatives, \af{δ?}. For this section we have taken inspiration from a blog post by Grenrus~\cite{fix-ing-regular-expressions}.
% % % 
% % % \begin{example}\label{ex:cfg-parsing}
% % % Let us consider the balanced bracket grammar example. We can see that it is nullable because it contains an \ac{ε} in the fixed point. It is also possible to parse the empty string by taking one iteration of the fixed point using the \ac{var}~\ac{zero}~∗~\ac{var}~\ac{zero} part and then the \ac{ε} for both recursive calls, but note that we always need to end in an empty base case. Thus, for a fixed point to be nullable, it must be nullable even if we do not consider the recursive calls.
% % % 
% % % The derivative of the balanced bracket grammar can be taken with respect to any character, but only the character \ac{`[} results in anything interesting because any string in the balanced bracket language needs to start with an opening bracket. The first thing we might try is to unroll the fixed point one step, yielding the following grammar:
% % % \begin{code}
% % % bracketsG₁ : Gram n
% % % bracketsG₁ = ε ∪ char `[ ∗ bracketsG ∗ char `] ∪ bracketsG ∗ bracketsG
% % % \end{code}
% % % We know how to take the derivative of the first two parts, but \af{bracketsG}~\ac{∗}~\af{bracketsG} seems problematic because its derivative depends on the derivative of \af{bracketsG} itself. Luckily, we can introduce a new fixed point when describing the derivative to refer to the derivative itself.
% % % \begin{code}
% % % bracketsG' : Gram n
% % % bracketsG' = μ (bracketsG ∗ char `] ∪ var zero ∗ bracketsG)
% % % \end{code}
% % % \end{example}
% % % 
% % % \subsubsection{Nullability}
% % % 
% % % Computing the nullability now requires us to deal with grammars that contain free variables, but we can make use of a context \ab{Γν} which tells us how to compute the nullability of those variables.
% % % 
% % % \begin{code}
% % % ν? : (G : Gram n) (Γν : (i : Fin n) → Dec (ν (Γ i))) → Dec (ν (⟦ G ⟧ Γ))
% % % \end{code}
% % % The simple cases remain the same except that \ab{Γν} now has to be passed properly to recursive calls. We skip to the two new cases: variables and fixed points.
% % % \begin{code}[hide]
% % % ν▹ : (ν (⟦ G₁ ⟧ Γ) × ν (⟦ G₂ ⟧ Γ)) ↔ ν (⟦ G₁ ∗ G₂ ⟧ Γ)
% % % to (ν▹ {G₁ = G₁} {G₂ = G₂}) ((n , x) , (m , y)) = max n m , [] , [] , refl , weakenˡ {G = G₁} x , weakenʳ {G = G₂} y
% % % from ν▹ (n , [] , [] , refl , x , y) = (n , x) , (n , y)
% % % 
% % % -- refold : (G : Gram (suc n)) → ⟦ G ⟧ (⟦ μ G ⟧ Γ ∷> Γ) ⇔ ⟦ μ G ⟧ Γ
% % % -- to (refold G) x = {!!}
% % % -- from (refold G) (suc k , x) = k , mapΓ G _ _ (λ { zero → k ,_ ; (suc i) → λ z → z }) x
% % % n≤sucn : n ≤ suc n
% % % n≤sucn {zero} = z≤m
% % % n≤sucn {suc n} = s≤s n≤sucn
% % % 
% % % variable i : Fin n
% % % \end{code}
% % % For both cases we need a helper. In the case of variables this helper just deals with converting between the truncated semantics and the proper semantics.
% % % \begin{code}
% % % νΓi↔ν⟦vari⟧Γ : ν (Γ i) ↔ ν (⟦ var i ⟧ Γ)
% % % to νΓi↔ν⟦vari⟧Γ x = zero , x
% % % from νΓi↔ν⟦vari⟧Γ (_ , x) = x
% % % \end{code}
% % % For the fixed point, we need to formalize the intuition from \cref{ex:cfg-parsing}. Recall that we noted how determining the nullability of a fixed point only requires unrolling it once and no more.
% % % \begin{code}
% % % νG⊥↔νμG  : ν (⟦ G ⟧ ((λ _ → ⊥) ∷> Γ)) ↔ ν (⟦ μ G ⟧ Γ)
% % % \end{code}
% % % We are still working on a proof of this property, but we have been able to reduce it to the following postulate which states that, if a grammar with free variables is nullable, either the nullability is independent of that variable, or that variable itself needs to be nullable.
% % % \begin{code}
% % % postulate νGℒ→νG⊥⊎νℒ  : ν (⟦ G ⟧ₖ (ℒ ∷> Γ) k) → ν (⟦ G ⟧ₖ ((λ _ → ⊥) ∷> Γ) k) ⊎ ν ℒ
% % % \end{code}
% % % \begin{code}[hide]
% % % νGμG→νG⊥  : ν (⟦ G ⟧ₖ (⟦ μ G ⟧ₖ Γ k ∷> Γ) k) → ν (⟦ G ⟧ₖ ((λ _ → ⊥) ∷> Γ) k)
% % % νGμG→νG⊥ {G = G} x with νGℒ→νG⊥⊎νℒ {G = G} x
% % % ... | inl x = x
% % % νGμG→νG⊥ {G = G} {k = suc k} _ | inr x = mapk {G = G} n≤sucn (νGμG→νG⊥ {G = G} {k = k} x)
% % % \end{code}
% % % \begin{code}[hide]
% % % to (νG⊥↔νμG {G = G}) (k , x) = suc k , mapΓ G _ _ (λ { zero → λ () ; (suc _) → λ z → z }) x
% % % from (νG⊥↔νμG {G = G}) (suc k , x) = k , νGμG→νG⊥ {G = G} x
% % % 
% % % \end{code}
% % % \begin{code}[hide]
% % % ν? ∅ _ = no λ ()
% % % ν? ε _ = yes (zero , refl)
% % % ν? (char c) _ = no λ ()
% % % ν? (x · G) Γν = map? (record { to = λ (x , n , y) → (n , x , y) ; from = λ (n , x , y) → (x , n , y) }) (x ×? ν? G Γν)
% % % ν? (G₁ ∪ G₂) Γν = map? (record { to = λ { (inl (n , x)) → n , inl x ; (inr (n , x)) → n , inr x } ; from = λ { (n , inl x) → inl (n , x) ; (n , inr x) → inr (n , x) } }) (ν? G₁ Γν ⊎? ν? G₂ Γν)
% % % ν? (G₁ ∗ G₂) Γν = map? (ν▹ {G₁ = G₁} {G₂ = G₂}) (ν? G₁ Γν ×? ν? G₂ Γν)
% % % \end{code}
% % % Using these two helpers, we can define the nullability of variables and fixed points as follows:
% % % \begin{code}
% % % ν? {Γ = Γ} (var i) Γν = map? (νΓi↔ν⟦vari⟧Γ {Γ = Γ}) (Γν i)
% % % ν? (μ G) Γν = map? νG⊥↔νμG (ν? G (no (λ ()) ∷> Γν))
% % % \end{code}
% % % 
% % % \subsubsection{Derivatives}
% % % 
% % % Computing the derivative also requires us to deal with free variables in our grammar. For derivatives, we need to keep track of four different environments:
% % % 
% % % \begin{enumerate}
% % % \item The language environment, \ab{Γ}, which contains the language of each variable.
% % % \item The nullability environment, \ab{Γν}, which tells us the nullability of all variables.
% % % \item The derivative environment, \ab{Γδ}, which keeps track of the derivative of each variable.
% % % \item The unrolling environment, \ab{Γσ}, which allows us to replace each variable by the fixed point that bound it, thus unrolling the fixed point.
% % % \end{enumerate}
% % % 
% % % The \af{Gram} data Type is no longer parameterized by its semantics, so we first define a syntactic derivative function \af{δ?} and afterwards prove that it corresponds to the semantic derivative.
% % % \begin{code}
% % % δ?  : (Γ : Fin n → Lang) (Γν : (i : Fin n) → Dec (ν (Γ i))) (Γδ : Fin n → Gram m) 
% % %       (Γσ : Fin n → Gram m) 
% % %     → Gram n → Char → Gram m
% % % \end{code}
% % % Again, all simple cases are the same except for passing around the environments correctly to recursive calls, so we skip to the two new cases for variables and fixed points.
% % % \begin{code}[hide]
% % % δ? _ _ _ _ ∅ c = ∅
% % % δ? _ _ _ _ ε c = ∅
% % % δ? _ _ _ _ (char c') c with c ≟ c'
% % % ... | yes _ = ε
% % % ... | no _ = ∅
% % % δ? Γ Γν Γδ Γσ (A · G) c = A · δ? Γ Γν Γδ Γσ G c
% % % δ? Γ Γν Γδ Γσ (G₁ ∪ G₂) c = δ? Γ Γν Γδ Γσ G₁ c ∪ δ? Γ Γν Γδ Γσ G₂ c
% % % δ? Γ Γν Γδ Γσ (G₁ ∗ G₂) c =  (δ? Γ Γν Γδ Γσ G₁ c ∗ subst G₂ Γσ)
% % %                           ∪  (ν? {Γ = Γ} G₁ Γν · δ? Γ Γν Γδ Γσ G₂ c)
% % % \end{code}
% % % For variables, we simply look up their derivative in the derivative environment. For fixed points, we need to show how to extend each of the four environments. Here we apply the same trick as we discovered in \cref{ex:cfg-parsing}, namely that we introduce a new fixed point which allows us to refer to the derivative itself.
% % % \begin{code}
% % % δ? _ _ Γδ _ (var i) _ = Γδ i
% % % δ? Γ Γν Γδ Γσ (μ G) c =
% % %   μ (δ?  (⟦ μ G ⟧ Γ                      ∷> Γ)
% % %          (ν? {Γ = Γ} (μ G) Γν            ∷> Γν)
% % %          (var zero                       ∷> (rename suc ∘ Γδ))
% % %          (subst (μ G) (rename suc ∘ Γσ)  ∷> (rename suc ∘ Γσ))
% % %          G c)
% % % \end{code}
% % % \begin{code}[hide]
% % % 
% % % ↔refl : A ↔ A
% % % ↔refl = record { to = λ x → x ; from = λ z → z }
% % % 
% % % \end{code}
% % % 
% % % We show the correctness of the syntactic derivative by showing that every string accepted by the result of taking the syntactic derivative of a grammar is also accepted by the semantic derivative of the original grammar and vice versa. The last two arguments specify that the unrolling and derivative environment actually contain what they are supposed to contain.
% % % \begin{code}
% % % δ?↔δ : (G : Gram n) {Γ : Fin n → Lang} {Γ' : Fin m → Lang} 
% % %        {Γν : (i : Fin n) → Dec (ν (Γ i))} {Γδ : Fin n → Gram m} {Γσ : Fin n → Gram m}
% % %      → ((i : Fin n) → ⟦ Γσ i ⟧ Γ' ⇔ Γ i)
% % %      → ((i : Fin n) → ⟦ Γδ i ⟧ Γ' ⇔ δ (Γ i) c)
% % %      → ⟦ δ? Γ Γν Γδ Γσ G c ⟧ Γ' ⇔ δ (⟦ G ⟧ Γ) c
% % % \end{code}
% % % We are still working on proofs for two parts of this correspondence. First, if a substitution corresponds pointwise to a change of environment, substituting all variables in a grammar also corresponds to a change of environment.
% % % \begin{code}
% % % postulate substΓσ  : {Γσ : Fin n → Gram m} (G : Gram n)
% % %                    → ((i : Fin n) → ⟦ Γσ i ⟧ Γ' ⇔ Γ i) → ⟦ subst G Γσ ⟧ Γ' ⇔ ⟦ G ⟧ Γ
% % % \end{code}
% % % Second, we are still working on proving the correctness of the syntactic derivative of fixed points.
% % % \begin{code}
% % % postulate
% % %   δ?↔δμ  : (G : Gram (suc n)) {Γ : Fin n → Lang} {Γ' : Fin m → Lang} 
% % %            {Γν : (i : Fin n) → Dec (ν (Γ i))} {Γδ : Fin n → Gram m} {Γσ : Fin n → Gram m}
% % %          → ((i : Fin n) → ⟦ Γσ i ⟧ Γ' ⇔ Γ i)
% % %          → ((i : Fin n) → ⟦ Γδ i ⟧ Γ' ⇔ δ (Γ i) c)
% % %          → ⟦ δ? Γ Γν Γδ Γσ (μ G) c ⟧ Γ' ⇔ δ (⟦ μ G ⟧ Γ) c
% % % \end{code}
% % % \begin{code}[hide]
% % % δ?↔δ ∅ eσ eδ = ↔refl
% % % to (δ?↔δ ε eσ eδ) ()
% % % from (δ?↔δ ε eσ eδ) ()
% % % 
% % % to (δ?↔δ {c = c}     (char c') eσ eδ) x with c ≟ c'
% % % to (δ?↔δ {c = c}     (char .c) eσ eδ) (k , refl) | yes refl = k , refl
% % % to (δ?↔δ             (char _)  eσ eδ) () | no _
% % % to (δ?↔δ             (A · G)   eσ eδ) (k , x , y) with to (δ?↔δ G eσ eδ) (k , y)
% % % ... | k , y = k , x , y 
% % % to (δ?↔δ             (G₁ ∪ G₂) eσ eδ) (k , inl x) with to (δ?↔δ G₁ eσ eδ) (k , x)
% % % ... | k , x = k , inl x
% % % to (δ?↔δ             (G₁ ∪ G₂) eσ eδ) (k , inr x) with to (δ?↔δ G₂ eσ eδ) (k , x)
% % % ... | k , x = k , inr x
% % % to (δ?↔δ {c = c}     (G₁ ∗ G₂) eσ eδ) (k , inl (u , v , refl , x , y)) with to (δ?↔δ G₁ eσ eδ) (k , x) | to (substΓσ G₂ eσ) (k , y)
% % % ... | k₁ , x | k₂ , y = max k₁ k₂ , (c ∷ u) , v , refl , weakenˡ {G = G₁} x , weakenʳ {G = G₂} y
% % % to (δ?↔δ {c = c} (G₁ ∗ G₂) eσ eδ) (k , inr (x , y)) with x | to (δ?↔δ G₂ eσ eδ) (k , y)
% % % ... | k₁ , x | k₂ , y = max k₁ k₂ , [] , (c ∷ _) , refl , weakenˡ {G = G₁} x , weakenʳ {G = G₂} y
% % % to (δ?↔δ           (var i)   eσ eδ) (k , x) = zero , to (eδ i) (k , x)
% % % from (δ?↔δ {c = c} (char c') eσ eδ) x with c ≟ c'
% % % from (δ?↔δ {c = c} (char c)  eσ eδ) (k , refl) | yes refl = k , refl
% % % from (δ?↔δ {c = c} (char .c) eσ eδ) (k , refl) | no ¬c≡c = k , ¬c≡c refl
% % % from (δ?↔δ         (A · G)   eσ eδ) (k , x , y) with from (δ?↔δ G eσ eδ) (k , y)
% % % ... | k , y = k , x , y
% % % from (δ?↔δ         (G₁ ∪ G₂) eσ eδ) (k , inl x) with from (δ?↔δ G₁ eσ eδ) (k , x)
% % % ... | k , x = k , inl x
% % % from (δ?↔δ         (G₁ ∪ G₂) eσ eδ) (k , inr x) with from (δ?↔δ G₂ eσ eδ) (k , x)
% % % ... | k , x = k , inr x
% % % from (δ?↔δ {c = c} (G₁ ∗ G₂) eσ eδ) (k , [] , (.c ∷ v) , refl , x , y) with from (δ?↔δ G₂ eσ eδ) (k , y)
% % % ... | k' , y = k' , inr ((k , x) , y)
% % % from (δ?↔δ {c = c} (G₁ ∗ G₂) eσ eδ) (k , (.c ∷ u) , v , refl , x , y) with from (δ?↔δ G₁ eσ eδ) (k , x) | from (substΓσ G₂ eσ) (k , y)
% % % ... | k₁ , x | k₂ , y = max k₁ k₂ , inl (u , v , refl , weakenˡ {G = δ? _ _ _ _ G₁ c} x , weakenʳ {G = subst G₂ _} y)
% % % from (δ?↔δ         (var i)   eσ eδ) (k , x) = from (eδ i) x
% % % 
% % % δ?↔δ (μ G) eσ eδ = δ?↔δμ G eσ eδ
% % % \end{code}
% % % With the exception of these two postulates, we have proven the correctness of our syntactic derivative function.
% % % % \begin{code}[hide]
% % % % substGvar≡G : (G : Gram n) → subst G var ≡ G
% % % % substGvar≡G ∅ = refl
% % % % substGvar≡G ε = refl
% % % % substGvar≡G (char x) = refl
% % % % substGvar≡G (x · G) = cong (x ·_) (substGvar≡G G)
% % % % substGvar≡G (G ∪ G₁) = cong₂ _∪_ (substGvar≡G G) (substGvar≡G G₁)
% % % % substGvar≡G (G ∗ G₁) = cong₂ _∗_ (substGvar≡G G) (substGvar≡G G₁)
% % % % substGvar≡G (μ G) = cong μ (trans (cong (subst G) (funext (λ { zero → refl ; (suc i) → refl }))) (substGvar≡G G))
% % % % substGvar≡G (var _) = refl
% % % % 
% % % % substG⊥≡G : {σ : Fin zero → Gram zero} (G : Gram zero) → subst G σ ≡ G
% % % % substG⊥≡G G = trans (cong (subst G) (funext (λ ()))) (substGvar≡G G)
% % % % 
% % % % ≡→↔ : {x y : Set} → x ≡ y → x ↔ y
% % % % ≡→↔ refl = record { to = λ z → z ; from = λ z → z }
% % % % \end{code}
% % % 
% % % \subsubsection{Parsing}
% % % 
% % % Tying it all together, we show how to parse a string following a grammar. We only care about grammars without variables, so all the environments are empty (\as{λ}~\as{(}\as{)}).
% % % \begin{code}
% % % parse : (G : Gram zero) → (w : String) → Dec (⟦ G ⟧ (λ ()) w)
% % % parse G [] = ν? G (λ ())
% % % parse G (c ∷ cs) = map? (δ?↔δ G (λ ()) (λ ())) (parse (δ? (λ ()) (λ ()) (λ ()) (λ ()) G c) cs)
% % % \end{code}
% % % This is a correct parser for context-free grammars.
% % % 