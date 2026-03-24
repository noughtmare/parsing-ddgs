\begin{code}[hide]
module 2-overview where

open import Agda.Primitive using (Level)

\end{code}

\section{Languages}

In this section, we summarize the basic definitions from previous work by Elliot~\cite{conal-languages}. We leave out details and proofs in some places and refer the interested reader to his work.

\begin{code}[hide]
Type₁ : Set₂
Type₁ = Set₁

Type : Type₁
Type = Set

variable A B : Set

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

record _×_ (A : Set) (B : Set) : Set where
    constructor _,_
    field
        π₁ : A
        π₂ : B
infixr 20 _×_

data _⊎_ (A : Set) (B : Set) : Set where
    inl : A → A ⊎ B
    inr : B → A ⊎ B
infixr 20 _⊎_

record _↔_ (A : Set) (B : Set) : Set where
    field
        to : A → B
        from : B → A
open _↔_

data _≡_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set where
    refl : x ≡ x
infix 10 _≡_

data ⊤ : Set where
    tt : ⊤

data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

data Char : Set where
    `a : Char
    `b : Char
    `c : Char
    `0 : Char
    `1 : Char
    `[ : Char
    `] : Char
-- ...

data String : Set where
    [] : String
    _∷_ : Char → String → String
infixr 20 _∷_

variable c : Char
         w : String

_++_ : String → String → String
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
infixr 20 _++_

record Σ (A : Set) (B : A → Set) : Set where
    constructor _,_
    field
        π₁ : A
        π₂ : B π₁
infixr 20 _,_
\end{code}

\subsection{Languages}

We define languages as being functions from strings to types.\footnote{We use \af{Type} as a synonym for Agda's \af{Set} to avoid confusion.}
\begin{code}[hide]
Lang : Set₁
\end{code}
\begin{code}
Lang = String → Type
\end{code}
The result type can be thought of as the type of proofs that the string is in the language.
\begin{remark}
Note that a language may admit multiple different proofs for the same string. That is an important difference between the type theoretic approach and the more common set theoretic approach, which models languages as sets of strings.
\end{remark}
This is a broad definition of what a language is; it includes languages that are outside the class of context-free languages. 
\begin{example}\label{ex:non-context-free}
The language $a^n b^n c^n$ can be specified as follows:
\begin{code}[hide]
repeat : ℕ → Char → String
repeat zero _ = []
repeat (suc n) c = c ∷ repeat n c
\end{code}
\begin{code}
abc : Lang
abc w = Σ ℕ λ n → w ≡ (repeat n `a ++ repeat n `b ++ repeat n `c)
\end{code}
We can show that the string $aabbcc$ is in this language by choosing $n$ to be $2$, from which the required equality follows by reflexivity after normalization:
\begin{code}
aabbcc : abc (`a ∷ `a ∷ `b ∷ `b ∷ `c ∷ `c ∷ [])
aabbcc = suc (suc zero) , refl
\end{code}
\end{example}
\cref{ex:non-context-free} shows that it is possible to specify languages and prove that certain strings are in those languages, but for practical applications we do not want to be burdened with writing such proofs ourselves. The compiler should be able to decide whether or not your program is valid by itself.
\begin{code}[hide]
variable ℒ ℒ₁ ℒ₂ : Lang

_⇔_ : Lang → Lang → Set
ℒ₁ ⇔ ℒ₂ = {w : String} → ℒ₁ w ↔ ℒ₂ w
\end{code}

\subsection{Nullability and Derivatives}

To facilitate proving the inclusion of strings in a language, we start by decomposing the problem. A string is either empty or a character followed by the tail of the string. We can decompose the problem of string inclusion along the same dimensions. First, we define nullability $ν$ as the inclusion of the empty string in a language as follows:
\begin{code}
ν : Lang → Type
ν ℒ = ℒ []
\end{code}
Second, we define the derivative $δ$ of a language $ℒ$ with respect to the character $c$ to be all the suffixes of the words in $ℒ$ which start with the $c$.
\begin{code}
δ : Lang → Char → Lang
δ ℒ c = λ w → ℒ (c ∷ w)
\end{code}
\begin{code}[hide]
foldl : {ℓ : Level} {A : Set ℓ} → (A → Char → A) → A → String → A
foldl k z [] = z
foldl k z (x ∷ xs) = foldl k (k z x) xs

trans : {ℓ : Level} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {x y : A} (P : A → B) → x ≡ y → P x ≡ P y
cong _ refl = refl

cong₂ : {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} {x y : A} {a b : B} (P : A → B → C) → x ≡ y → a ≡ b → P x a ≡ P y b
cong₂ _ refl refl = refl

id : {ℓ : Level} {A : Set ℓ} → A → A
id x = x

_∘_ : {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)
\end{code}
The relevance of these definitions is shown by \cref{thm:nullability-after-derivatives}.
\begin{theorem}\label{thm:nullability-after-derivatives}
Nullability after repeated derivatives fully captures what a language is. Formally, we state this as follows:
\begin{code}[hide]
ν∘foldlδℒ≡ℒ :
\end{code}
\begin{code}
  ν ∘ foldl δ ℒ ≡ ℒ
\end{code}
\begin{code}[hide]
ν∘foldlδℒ≡ℒ′ : (ℒ : Lang) (w : String) → ν (foldl δ ℒ w) ≡ ℒ w
ν∘foldlδℒ≡ℒ′ ℒ [] = refl
ν∘foldlδℒ≡ℒ′ ℒ (c ∷ w) = ν∘foldlδℒ≡ℒ′ (δ ℒ c) w

postulate funext : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {P Q : A → B} → ((x : A) → P x ≡ Q x) → P ≡ Q

ν∘foldlδℒ≡ℒ {ℒ = ℒ} = funext (ν∘foldlδℒ≡ℒ′ ℒ)
\end{code}
\end{theorem}

\subsection{Decidability}

From our type theoretic perspective, parsing a string is the same thing as producing an element of the result type of a language for that given input string, or showing that no such element can exist. In Agda, we encode this using the following \af{Dec} data type which is parameterized by a type \ab{A} and contains a constructor \ac{yes} for when you can produce an element of \ab{A} or \ac{no} if you can show that no such element exists.
\begin{code}
data Dec (A : Type) : Type where
    yes : A → Dec A
    no : (A → ⊥) → Dec A
\end{code}
Sometimes we want to change the parameter type of a \af{Dec}. For that we need to provide conversion functions between the old and the new type in both ways.
\begin{code}
map? : (A ↔ B) → Dec A → Dec B
map? f (yes x) = yes (to f x)
map? f (no ¬A) = no λ x → ¬A (from f x)
\end{code}
\begin{code}[hide]
⌊_⌋ : Dec A → Type
⌊_⌋ {A} _ = A

_×?_ : Dec A → Dec B → Dec (A × B)
yes x ×? yes y = yes (x , y)
yes _ ×? no ¬y = no λ (_ , y) → ¬y y
no ¬x ×? _ = no λ (x , _) → ¬x x

_⊎?_ : Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎? y = yes (inl x)
no x ⊎? yes y = yes (inr y)
no ¬x ⊎? no ¬y = no λ where
    (inl x) → ¬x x
    (inr y) → ¬y y

_≟_ : (c : Char) → (c′ : Char) → Dec (c ≡ c′)
`a ≟ `a = yes refl
`a ≟ `b = no λ ()
`a ≟ `c = no λ ()
`a ≟ `0 = no λ ()
`a ≟ `1 = no λ ()
`b ≟ `a = no λ ()
`b ≟ `b = yes refl
`b ≟ `c = no λ ()
`b ≟ `0 = no λ ()
`b ≟ `1 = no λ ()
`c ≟ `a = no λ ()
`c ≟ `b = no λ ()
`c ≟ `c = yes refl
`c ≟ `0 = no λ ()
`c ≟ `1 = no λ ()
`0 ≟ `a = no λ ()
`0 ≟ `b = no λ ()
`0 ≟ `c = no λ ()
`0 ≟ `0 = yes refl
`0 ≟ `1 = no λ ()
`1 ≟ `a = no λ ()
`1 ≟ `b = no λ ()
`1 ≟ `c = no λ ()
`1 ≟ `0 = no λ ()
`1 ≟ `1 = yes refl
`a ≟ `[ = no λ ()
`a ≟ `] = no λ ()
`b ≟ `[ = no λ ()
`b ≟ `] = no λ ()
`c ≟ `[ = no λ ()
`c ≟ `] = no λ ()
`0 ≟ `[ = no λ ()
`0 ≟ `] = no λ ()
`1 ≟ `[ = no λ ()
`1 ≟ `] = no λ ()
`[ ≟ `a = no λ ()
`[ ≟ `b = no λ ()
`[ ≟ `c = no λ ()
`[ ≟ `0 = no λ ()
`[ ≟ `1 = no λ ()
`[ ≟ `[ = yes refl
`[ ≟ `] = no λ ()
`] ≟ `a = no λ ()
`] ≟ `b = no λ ()
`] ≟ `c = no λ ()
`] ≟ `0 = no λ ()
`] ≟ `1 = no λ ()
`] ≟ `[ = no λ ()
`] ≟ `] = yes refl

\end{code}

\subsection{Grammars and Parsing}\label{sec:gram-and-parsing}

We have seen in \cref{ex:non-context-free} that our definition of language is very general, comprising even context-sensitive languages. Parsing such languages automatically poses a significant challenge. Hence, we side-step this problem by restricting the scope of our parsers to a smaller well-defined subset of languages. In this subsection, we consider a subset of regular languages without Kleene star (i.e., closure under concatenation). In \cref{sec:context-free}, we extend this class of languages to include fixed points which subsume the Kleene star.

\begin{code}[hide]
module Simple where
\end{code}
\begin{code}
    data Gram : Lang → Type₁ where
        ∅     :                       Gram (λ _ → ⊥)
        ε     :                       Gram (λ w → w ≡ [])
        char  : (c : Char)         →  Gram (λ w → w ≡ c ∷ [])
        _·_   : Dec A → Gram ℒ     →  Gram (λ w → A × ℒ w)
        _∪_   : Gram ℒ₁ → Gram ℒ₂  →  Gram (λ w → ℒ₁ w ⊎ ℒ₂ w)
        _∗_   : Gram ℒ₁ → Gram ℒ₂
              → Gram (λ w → Σ String λ u → Σ String λ v → (w ≡ u ++ v) × ℒ₁ u × ℒ₂ v)
        _◃_   : (ℒ₁ ⇔ ℒ₂) → Gram ℒ₁ → Gram ℒ₂
\end{code}
\begin{code}[hide]
    variable G G₁ G₂ : Gram ℒ
\end{code}
\begin{remark}
The \af{Gram} data type is parameterized by its language. This ties the constructors directly to their semantics.
\end{remark}

By recursion over this data type of grammars, we can define a decision procedure for nullability and derivative function; both are correct by construction.
\begin{code}
    ν? : Gram ℒ → Dec (ν ℒ)
    δ? : Gram ℒ → (c : Char) → Gram (δ ℒ c)
\end{code}
\begin{code}[hide]
    ν∗ : (ν ℒ₁ × ν ℒ₂) ↔ Σ String λ u → Σ String λ v → ([] ≡ (u ++ v)) × ℒ₁ u × ℒ₂ v
    to ν∗ (x , y) = [] , [] , refl , x , y
    from ν∗ ([] , [] , refl , x , y) = x , y

    ν? ∅ = no λ ()
    ν? ε = yes refl
    ν? (char c) = no λ ()
    ν? (x · G) = x ×? ν? G
    ν? (G₁ ∪ G₂) = ν? G₁ ⊎? ν? G₂
    ν? (G₁ ∗ G₂) = map? ν∗ (ν? G₁ ×? ν? G₂)
    ν? (f ◃ G₂) = map? f (ν? G₂)
\end{code}
\begin{code}[hide]
    δ? ∅ c = ∅
    δ? ε c = record { to = λ () ; from = λ () } ◃ ∅
    δ? (char c′) c with c ≟ c′
    ... | yes refl = (λ { {[]} → record { to = λ _ → refl ; from = λ _ → refl } ; {_ ∷ _} → record { to = λ () ; from = λ () }}) ◃ ε
    ... | no ¬c≡c′ = (λ { {[]} → record { to = λ () ; from = λ { refl → ¬c≡c′ refl }} ; {_ ∷ _} → record { to = λ () ; from = λ () }}) ◃ ∅
    δ? (A · G) c = A · δ? G c
    δ? (G₁ ∪ G₂) c = δ? G₁ c ∪ δ? G₂ c
    δ? (G₁ ∗ G₂) c = (record { to = λ { (inl (u , v , refl , x , y)) → (c ∷ u) , v , refl , x , y ; (inr (x , y)) → [] , (c ∷ _) , refl , x , y } ; from = λ { ([] , _ , refl , x , y) → inr (x , y) ; ((_ ∷ u) , v , refl , x , y) → inl (u , v , refl , x , y) } } ) ◃ ((δ? G₁ c ∗ G₂) ∪ (ν? G₁ · δ? G₂ c))
    δ? (f ◃ G₂) c = f ◃ δ? G₂ c

    -- δ?↔δ : ⟦ δ? c G ⟧ w ↔ δ c ⟦ G ⟧ w
\end{code}
\begin{code}[hide]
    -- to (δ?↔δ {c} {G = ` c′}) x with c ≟ c′
    -- to (δ?↔δ {c} {` .c}) refl | yes refl = refl
    -- to (δ?↔δ {_} {` _}) () | no _
    -- to (δ?↔δ {G = A · G}) (x , y) = x , to δ?↔δ y
    -- to (δ?↔δ {G = G₁ ∪ G₂}) (inl x) = inl (to δ?↔δ x)
    -- to (δ?↔δ {G = G₁ ∪ G₂}) (inr x) = inr (to δ?↔δ x)
    -- to (δ?↔δ {c} {G = G₁ ▹ G₂}) (inl (u , v , refl , x , y)) = (c ∷ u) , v , refl , to δ?↔δ x , y
    -- to (δ?↔δ {c} {G = G₁ ▹ G₂} {w}) (inr (π₁ , π₂)) = [] , (c ∷ w) , refl , π₁ , to δ?↔δ π₂
    -- from (δ?↔δ {c} {G = ` c′}) x with c ≟ c′
    -- from (δ?↔δ {c} {` c}) refl | yes refl = refl
    -- from (δ?↔δ {c} {` .c}) refl | no ¬c≡c = ¬c≡c refl
    -- from (δ?↔δ {G = A · G}) (π₁ , π₂) = π₁ , from δ?↔δ π₂
    -- from (δ?↔δ {G = G ∪ G₁}) (inl x) = inl (from δ?↔δ x)
    -- from (δ?↔δ {G = G ∪ G₁}) (inr x) = inr (from δ?↔δ x)
    -- from (δ?↔δ {c} {G = G ▹ G₁}) ([] , (.c ∷ v) , refl , x , y) = inr (x , from δ?↔δ y)
    -- from (δ?↔δ {c} {G = G ▹ G₁}) ((.c ∷ u) , v , refl , x , y) = inl (u , v , refl , from δ?↔δ x , y)
    transport : {ℓ₁ : Level} {A : Set ℓ₁} {B : Set ℓ₁} → A ≡ B → A → B
    transport refl x = x
\end{code}
Together, decidable nullability and the derivative function can be combined to decide whether any string is in the language described by a grammar.
\begin{code}
    parse : Gram ℒ → (w : String) → Dec (ℒ w)
    parse G [] = ν? G
    parse G (c ∷ w) = parse (δ? G c) w
\end{code}
Thus, we have defined a parser for our simple grammars.

% A language is a set of strings $\mathbb{2}^{(\af{List}~\af{Token})}$.
% 
% 
% \begin{code}[hide]
% Lang : Set₁
% \end{code}
% \begin{code}
% Lang = List Token → Set
% \end{code}
% 
% This type has a very rich structure. It forms an ... algebra with union and intersection and a semiring with union and sequential composition.
% 
% \begin{code}
% ∅ : Lang
% ∅ _ = ⊥
% \end{code}
% 
% Going beyond work by Elliot, we can try to define context-free grammars.
% Unfortunately, we quickly run into issues due to nontermination. It is not easy
% to show that a grammar defined in this way is well-founded. To solve this issue
% we can use guarded type theory, in our case provided by guarded cubical Agda.
% This allows us to define arbitrary fixed points of languages.
% 
% \begin{code}
% fueled : (Lang → Lang) → ℕ → Lang
% fueled f 0 = ∅
% fueled f (suc n) = f (fueled f n)
% \end{code}
% 
% \begin{code}
% fix : (Lang → Lang) → Lang
% fix f w = ∃[ n ] fueled f n w
% \end{code}
