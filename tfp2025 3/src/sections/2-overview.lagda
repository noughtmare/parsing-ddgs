\begin{code}[hide]
-- Cannot be safe because we postulate funext
-- {-# OPTIONS --safe #-}
module 2-overview where

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
open import Relation.Nullary.Reflects using (ofʸ ; ofⁿ)
open import Level hiding (zero ; suc)
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Fin hiding (_≟_)
open import Data.Nat hiding (_≟_)
open import Relation.Nullary.Negation
import Data.String as String
open import Agda.Builtin.FromString

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
    c c' : Char
    w : String
\end{code}

\section{Finite Languages}\label{sec:finite-languages}

In this section, we introduce background information, namely how we define languages, basic language combinators, and parsers. Our exposition follows Elliott~\cite{conal-languages}. In \cref{sec:context-free}, we extend these concepts to context free languages.

\subsection{Languages}

We define languages as being functions from strings to types.\footnote{We use \af{Type} as a synonym for Agda's \af{Set} to avoid confusion with set-theoretic sets.}
\begin{code}[hide]
module ◇ where
    Lang : Type₁
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
    abc w = Σ[ n ∈ ℕ ] w ≡ repeat n 'a' ++ repeat n 'b' ++ repeat n 'c'
\end{code}
We can show that the string $aabbcc$ is in this language by choosing $n$ to be $2$, from which the required equality follows by reflexivity after normalization:
\begin{code}
    aabbcc : abc "aabbcc"
    aabbcc = 2 , refl
\end{code}
\end{example}
\cref{ex:non-context-free} shows that it is possible to specify languages and prove that certain strings are in those languages, but for practical applications we do not want to be burdened with writing such proofs ourselves.
In other words, we want a parser which can determine by itself whether a string is in the language or not.

Unfortunately, we cannot hope to write a parser for arbitrary languages defined in this way. A language could be defined, for example, such that the inclusion of a particular string is predicated on whether or not the Collatz conjecture holds.
Therefore, we need to restrict ourselves to a subset of languages.
Next, we explore basic language combinators for this purpose.

\subsection{Basic Language Combinators}

Let's start with a simple example: POSIX file system permissions. These are usually summarized using the characters `r', `w', and `x' if the permissions are granted, or `-' in place of the corresponding character if the permission is denied. For example the string ``r-x'' indicates that read and execute permissions are granted, but the write permission is denied. The full language can be expressed using the following grammar:

\begin{grammar}
<permissions>  ::= <read> <write> <execute>

<read>         ::= - | r

<write>        ::= - | w

<execute>      ::= - | x
\end{grammar}

\begin{code}[hide]
    variable ℒ ℒ₁ ℒ₂ : Lang
\end{code}

\begin{figure}
\begin{minipage}{.63\textwidth}
\begin{code}
    `_ : Char → Lang
    (` c) w = w ≡ c ∷ []
\end{code}
\begin{code}
    _∪_ : Lang → Lang → Lang
    (P ∪ Q) w = P w ⊎ Q w
\end{code}
\begin{code}
    _∗_ : Lang → Lang → Lang
    (P ∗ Q) w = ∃[ u ] ∃[ v ] w ≡ u ++ v × P u × Q v
\end{code}
\end{minipage}
\begin{minipage}{.36\textwidth}
\begin{code}
    ∅ : Lang
    ∅ _ = ⊥
\end{code}
\begin{code}
    ε : Lang
    ε w = w ≡ []
\end{code}
\begin{code}
    _·_ : Type → Lang → Lang
    (A · P) w = A × P w 
\end{code}
\end{minipage}
\begin{code}[hide]
    infix 22 `_
    infixr 21 _∗_
    infix 21 _·_
    infixr 20 _∪_
\end{code}
\caption{Basic language combinators.}\label{fig:combinators}
\end{figure}

This grammar uses three important features: sequencing, choice, and matching
character literals. We can define these features as combinators on languages in
Agda as shown in the left column of \cref{fig:combinators}. Using these
combinators we can define our permissions language as follows:
%
\begin{code}[hide]
    permissions read write execute : Lang
\end{code}
\begin{code}
    permissions  = read ∗ write ∗ execute
    read         = ` '-' ∪ ` 'r'
    write        = ` '-' ∪ ` 'w'
    execute      = ` '-' ∪ ` 'x'
\end{code}

The right column of \cref{fig:combinators} lists combinators whose purpose will become clear when we discuss how to write parsers for this simple language in the next section.

\subsection{Parsers}

We want to write a program which can prove for us that a given string is in a language. What should this program return for strings that are not in the language? We want to make sure our program does find a proof if it exists, so if it does not exist then we want a proof that the string is not in the language. We can capture this using a type called \af{Dec} from the Agda standard library. It can be defined as follows:

\begin{code}
    data ◂Dec (A : Type) : Type where
        ◂yes : A → ◂Dec A
        ◂no : ¬ A → ◂Dec A
\end{code}

A parser for a language, then, is a program which can tell us whether any given string is in the language or not.

\begin{code}
    Parser : Lang → Set
    Parser P = (w : String) → Dec (P w)
\end{code}

\begin{remark}
Readers familiar with Haskell might see similarity between this type and the type \verb|String -> Maybe a|, which is one way to implement parser combinators (although usually the return type is \verb|Maybe (a, String)| giving parsers the freedom to consume only a prefix of the input string and return the rest). The differences are that the result of our $\af{Parser}$ type depends on the language specification and input string, and that a failure carries with it a proof that the string cannot be part of the language. This allows us to separate the specification of our language from the implementation while ensuring correctness.
\end{remark}

\begin{remark}
Note that the \af{Dec} type only requires our parsers to produce a single
result; it does not have to exhaustively list all possible ways to parse the
input string. In Haskell, one might write \verb|String -> [(a, String)]|\cite{monadic-parsing}, which allows a parser to return
multiple results but does nothing to ensure that it correctly produces all
possible results. We could imagine requiring that the result type is in
bijection with a finite or countably infinite set. However, that would introduce
too many complications in our proofs. In practice, furthermore, we want our
parsers to only give us a single result. Hence, our effort would be better spent
in proving that our languages are unambiguous, meaning there is at most one
valid way to parse each input string. Thus, in this paper, we use $\af{Dec}$.
\end{remark}

To construct a parser for our permissions language, we start by defining parsers for each of the language combinators. Let us start by considering the character combinator. If the given string is empty or has more than one character, it can never be in a language formed by one character. If the string does consist of only one character, then it is in the language if that character is the same as from the language specification. In Agda, we can write such a parser for characters as follows:

\begin{code}
    ◂`-parse_ : (x : Char) → Parser (` x)
    (◂`-parse _) [] = no λ ()
    (◂`-parse x) (c ∷ []) = Dec.map (mk⇔ (λ { refl → refl }) (λ { refl → refl })) (c ≟ x)
    (◂`-parse _) (_ ∷ _ ∷ _) = no λ ()
\end{code}

This is a correct implementation of a parser for languages that consist of a single character, but the implementation seems ad hoc and it is hard to read, especially considering this is one of the simpler combinators.

Following the approach of parsing with derivatives, we can factor this parser into two cases: the empty string case and the case with at least one character.  We call the former nullability and denote it with the greek character $ν$, and we call the latter derivative and denote it with the greek character $δ$. 

Crucially, nullability deals only with (decidable) types, and derivatives deal only with languages. This clearly separates the level of abstraction between both cases. 

Returning to our character parser, a single character language is not nullable. On the level of types we express this as $\af{⊥}$, the uninhabited type, which is trivially decidable as $\ac{no}~\as{λ}~\as{()}$.

The derivative of a single character language depends on whether the character of the derivative is the same as the character of the language. We might be tempted to define this condition externally in Agda, but that would break the abstraction of derivatives only dealing with languages. Instead, we are pushed toward defining a combinator, \af{\un{}·\un{}}, which allows us to express this condintional on the level of languages. If the condition holds then there is still a second condition which is that the remainder of the string needs to be empty. We use the epsilon language, $\af{ε}$, for that purpose.
To conclude, the derivative of the character language $\af{`}~\ab{c'}$ with respect to the character $\ab{c}$ is $\as{(}\ab{c}~\af{≟}~\ab{c'}\as{)}~\af{·}~\af{ε}$ as shown in \cref{fig:null-delta}.

\begin{code}[hide]
    variable L P Q : Lang
\end{code}

\begin{code}[hide]
    ⊥-dec : Dec ⊥
    ⊥-dec = no λ ()

    ⊤-dec : Dec ⊤
    ⊤-dec = yes tt
\end{code}

\begin{figure}
\begin{minipage}{0.45\textwidth}
\begin{code}[hide]
    ν : {ℓ : Level} {P : String → Type ℓ} → ((w : String) → P w) → P []
    _◂⇔_ : Set → Set → Set
\end{code}
\begin{code}
    ν P = P []
\end{code}
\begin{code}
    A ◂⇔ B = (A → B) × (B → A) 
\end{code}
\begin{code}
    ν∅  : ⊥            ⇔ ν ∅
    νε  : ⊤            ⇔ ν ε
    ν·  : (A × ν P)    ⇔ ν (A · P)
    ν`  : ⊥            ⇔ ν (` c')
    ν∪  : (ν P ⊎ ν Q)  ⇔ ν (P ∪ Q)
    ν∗  : (ν P × ν Q)  ⇔ ν (P ∗ Q)

\end{code}
\end{minipage}
\begin{minipage}{0.54\textwidth}
\begin{code}[hide]
    δ : {ℓ : Level} {P : String → Type ℓ} (c : Char) → ((w : String) → P w) → ((w : String) → P (c ∷ w))
    _⟺_ : Lang → Lang → Set
\end{code}
\begin{code}
    (δ c P) w = P (c ∷ w)
\end{code}
\begin{code}
    P ⟺ Q = ∀ {w} → P w ⇔ Q w
\end{code}
\begin{code}
    δ∅  : ∅                ⟺ δ c ∅
    δε  : ∅                ⟺ δ c ε
    δ·  : (A · δ c P)      ⟺ δ c (A · P)
    δ`  : ((c ≡ c') · ε)   ⟺ δ c (` c')
    δ∪  : (δ c P ∪ δ c Q)  ⟺ δ c (P ∪ Q)
    δ∗  : (ν P · δ c Q ∪ δ c P ∗ Q)
                           ⟺ δ c (P ∗ Q)
\end{code}
\end{minipage}
\caption{Nullability, derivatives, and how they relate to the basic combinators.}\label{fig:null-delta}
\end{figure}

\begin{code}[hide]
    ν∅ = ⇔.refl
    δ∅ = ⇔.refl
\end{code}

\begin{code}[hide]
    ∅-parse : Parser ∅
    ∅-parse []       = Dec.map ν∅ ⊥-dec
    ∅-parse (c ∷ w)  = Dec.map (δ∅ {c} {w}) (∅-parse w)

    νε = mk⇔ (λ { tt → refl }) (λ { refl → tt })
    δε = mk⇔ (λ ()) (λ ())

    ε-parse : Parser ε
    ε-parse []       = Dec.map νε ⊤-dec
    ε-parse (_ ∷ w)  = Dec.map δε (∅-parse w)

    ν· = ⇔.refl
    δ· = ⇔.refl

    _·-parse_ : (x : Dec A) → Parser P → Parser (A · P)
    _·-parse_ {P = P} x φ []       = Dec.map (ν· {P = P}) (x ×-dec (ν φ))
    _·-parse_ {P = P} x φ (c ∷ w)  = Dec.map (δ· {P = P}) ((x ·-parse (δ c φ)) w)

    ν` = mk⇔ (λ ()) (λ ())
    δ` = mk⇔ (λ { (refl , refl) → refl }) (λ { refl → refl , refl })
\end{code}


Furthermore, \cref{fig:null-delta} shows the nullability and derivatives of all basic combinators using simple and self-contained equivalances.
The implementation of parsers for our basic combinators follow completely from the decomposition into nullability and derivatives and these equivalances.
For example, we can rewrite our character parser as follows:
%
\begin{code}
    `-parse_ : (c' : Char) → Parser (` c')
    (`-parse _) []        = Dec.map ν` ⊥-dec
    (`-parse c') (c ∷ w)  = Dec.map δ` (((c ≟ c') ·-parse ε-parse) w)
\end{code}

Parsers for the other basic combinators are equally straightforward and can be found in our source code artifact.\jr{todo: reference this nicely}

\begin{code}[hide]
    ν∪ = ⇔.refl
    δ∪ = ⇔.refl
\end{code}

\begin{code}[hide]
    -- To make this work properly we have to do some ugly implicit parameter manipulation
    _∪-parse_ : Parser P → Parser Q → Parser (P ∪ Q)
    _∪-parse_ {P} {Q} φ ψ []       = Dec.map (ν∪ {P} {Q}) (ν φ ⊎-dec ν ψ)
    _∪-parse_ {P} {Q} φ ψ (c ∷ w)  = Dec.map (δ∪ {c} {P} {Q}) ((δ c φ ∪-parse δ c ψ) w)
    module _ {P Q : Lang} where
        ◂ν∪  : (ν P ⊎ ν Q)  ⇔ ν (P ∪ Q)
        ◂ν∪ = ν∪ {P} {Q}
        ◂δ∪  : (δ c P ∪ δ c Q)  ⟺ δ c (P ∪ Q)
        ◂δ∪ = δ∪ {_} {P} {Q}
\end{code}
\begin{code}[hide]
        _◂∪-parse_ : Parser P → Parser Q → Parser (P ∪ Q)
        (φ ◂∪-parse ψ) []       = Dec.map ◂ν∪ (ν φ ⊎-dec ν ψ)
        (φ ◂∪-parse ψ) (c ∷ w)  = Dec.map ◂δ∪ ((δ c φ ∪-parse δ c ψ) w)
\end{code}

\begin{code}[hide]
    ν∗ = mk⇔ (λ x → [] , [] , refl , x) (λ { ([] , [] , refl , x) → x })
    δ∗ = mk⇔ 
        (λ where 
          (inj₁ x) → [] , _ , refl , x
          (inj₂ (u , v , refl , x)) → _ ∷ u , v , refl , x)
        (λ where 
          ([] , _ , refl , x) → inj₁ x
          (_ ∷ u , v , refl , x) → inj₂ (u , v , refl , x))
\end{code}

\begin{code}[hide]
    map′-id-id : {x : Dec A} → Dec.map′ id id x ≡ x
    map′-id-id {x = yes _} = refl
    map′-id-id {x = no _} = refl
    ∪-parse-rewrite : ∀{φ : Parser P} {ψ : Parser Q} → (φ ∪-parse ψ) w ≡ (φ w ⊎-dec ψ w)
    ∪-parse-rewrite {w = []} = map′-id-id
    ∪-parse-rewrite {w = x ∷ w} = trans map′-id-id (∪-parse-rewrite {w = w})
\end{code}

\begin{code}[hide]
    infix 22 `-parse_
    infixr 21 _∗-parse_
    infix 21 _·-parse_
    infixr 20 _∪-parse_
    -- To convince Agda this terminates, we need to use the identity:
    -- (φ ∪-parse ψ) w ≡ φ w ⊎-dec ψ w
    -- That is easy to prove (see ∪-parse-rewrite above), but convincing Agda to use this is a bit difficult
    _∗-parse_ : Parser P → Parser Q → Parser (P ∗ Q)
    (φ ∗-parse ψ) []       = Dec.map ν∗ (ν φ ×-dec ν ψ)
    (φ ∗-parse ψ) (c ∷ w)  = Dec.map δ∗ ((ν φ ·-parse δ c ψ) w ⊎-dec (δ c φ ∗-parse ψ) w)
    -- So we just use the TERMINATING pragma for the code that we show in the paper.
    {-# TERMINATING #-}
\end{code}
\begin{code}[hide]
    _◂∗-parse_ : Parser P → Parser Q → Parser (P ∗ Q)
    (φ ◂∗-parse ψ) []       = Dec.map ν∗ (ν φ ×-dec ν ψ)
    (φ ◂∗-parse ψ) (c ∷ w)  = Dec.map δ∗ ((ν φ ·-parse δ c ψ ∪-parse δ c φ ∗-parse ψ) w)
\end{code}

The parser for our full permissions language can now be implemented by simply
mapping each of the language combinators onto their respective parser
combinators.
%
\begin{code}[hide]
    permissions-parse : Parser permissions
    read-parse : Parser read
    write-parse : Parser write
    execute-parse : Parser execute
\end{code}
\begin{code}
    permissions-parse  = read-parse ∗-parse (write-parse ∗-parse execute-parse) 
    read-parse         = (`-parse '-') ∪-parse (`-parse 'r')
    write-parse        = (`-parse '-') ∪-parse (`-parse 'w')
    execute-parse      = (`-parse '-') ∪-parse (`-parse 'x')
\end{code}
%
This allows us to generate a parser for any language that is defined using the basic combinators from \cref{fig:combinators}. We mechanize this result later in \cref{sec:parsing-in-general}, but we first consider extending the expressivity of our combinators.

\subsection{Infinite Languages}

This permissions language is very simple. In particular, it is finite. In practice, many languages are inifinite, for which the basic combinators will not suffice. For example, file paths can be arbitrarily long on most systems.
Elliott~\cite{conal-languages} defines a Kleene star combinator which enables him to specify regular languages such as file paths.

However, we want to go one step further, speficying and parsing context-free languages. Most practical programming languages are at least context-free, if not more complicated. An essential feature of many languages is the ability to recognize balanced brackets. A minimal example language with balanced brackets is the following:
%
\begin{grammar}
<brackets> ::= ε | [ <brackets> ] | <brackets> <brackets>
\end{grammar}
%
This is the language of all strings which consist of balanced square brackets. 
Many practical programming languages include some form of balanced brackets. Furthermore, this language is well known to be context-free and not regular. Thus, we need more powerful combinators.

\jr{todo: flesh out this outline}
We could try to naively transcribe the brackets grammar using our basic combinators, but Agda will justifiably complain that it is not terminating. Here we have added a NON_TERMINATING pragma to make Agda to accept it any way, but this is obviously not the proper way to define our brackets language.
%
\begin{code}
    {-# NON_TERMINATING #-}
    brackets = ε ∪ ` '[' ∗ brackets ∗ ` ']' ∪ brackets ∗ brackets
\end{code}
%
We need to find a different way to encode this recursive relation.

\begin{code}
    postulate μ : (Lang → Lang) → Lang
    bracketsμ = μ (λ P → ε ∪ ` '[' ∗ P ∗ ` ']' ∪ P ∗ P)
\end{code}

\begin{itemize}
\item $\af{μ}$, with that exact type, cannot be implemented
\item The Lang → Lang function needs to be restricted
\end{itemize}
\jr{Can we give a concrete example of how Lang → Lang is too general?}

\endinput

% % For starters, we define some structure on this definition of language in
% % \cref{fig:combinators}. First, Languages form a semiring, with union
% % $\af{\un{}∪\un{}}$, concatenation $\af{\un{}∗\un{}}$, the empty language
% % $\af{∅}$ which is the unit of union, and the language which only includes the
% % empty string $\af{ε}$ which is the unit of concatenation. Furthermore the
% % $\af{`\un}$ combinator defines a language which contains exactly the string
% % consisting of a single given character. Finally, the scalar multiplication
% % $\af{\un{}·\un{}}$ combinator injects an Agda type into a language. The purpose
% % of this combinator will become clearer in later sections\jr{mention specific sections}.
% 
% % \subsection{Decidability}
% 
% % From our type theoretic perspective, parsing a string is the same thing as producing an element of the result type of a language for that given input string, or showing that no such element can exist. In Agda, we encode this using the following \af{Dec} data type which is parameterized by a type \ab{A} and contains a constructor \ac{yes} for when you can produce an element of \ab{A} or \ac{no} if you can show that no such element exists.
% % \begin{code}
% % data Dec (A : Type) : Type where
%     % yes : A → Dec A
%     % no : (A → ⊥) → Dec A
% % \end{code}
% % Sometimes we want to change the parameter type of a \af{Dec}. For that we need to provide conversion functions between the old and the new type in both ways.
% % \begin{code}
% % map? : (A ↔ B) → Dec A → Dec B
% % map? f (yes x) = yes (to f x)
% % map? f (no ¬A) = no λ x → ¬A (from f x)
% % \end{code}
% % \begin{code}[hide]
% % ⌊_⌋ : Dec A → Type
% % ⌊_⌋ {A} _ = A
% 
% % _×?_ : Dec A → Dec B → Dec (A × B)
% % yes x ×? yes y = yes (x , y)
% % yes _ ×? no ¬y = no λ (_ , y) → ¬y y
% % no ¬x ×? _ = no λ (x , _) → ¬x x
% 
% % _⊎?_ : Dec A → Dec B → Dec (A ⊎ B)
% % yes x ⊎? y = yes (inl x)
% % no x ⊎? yes y = yes (inr y)
% % no ¬x ⊎? no ¬y = no λ where
%     % (inl x) → ¬x x
%     % (inr y) → ¬y y
% 
% % _≟_ : (c : Char) → (c′ : Char) → Dec (c ≡ c′)
% % `a ≟ `a = yes refl
% % `a ≟ `b = no λ ()
% % `a ≟ `c = no λ ()
% % `a ≟ `0 = no λ ()
% % `a ≟ `1 = no λ ()
% % `b ≟ `a = no λ ()
% % `b ≟ `b = yes refl
% % `b ≟ `c = no λ ()
% % `b ≟ `0 = no λ ()
% % `b ≟ `1 = no λ ()
% % `c ≟ `a = no λ ()
% % `c ≟ `b = no λ ()
% % `c ≟ `c = yes refl
% % `c ≟ `0 = no λ ()
% % `c ≟ `1 = no λ ()
% % `0 ≟ `a = no λ ()
% % `0 ≟ `b = no λ ()
% % `0 ≟ `c = no λ ()
% % `0 ≟ `0 = yes refl
% % `0 ≟ `1 = no λ ()
% % `1 ≟ `a = no λ ()
% % `1 ≟ `b = no λ ()
% % `1 ≟ `c = no λ ()
% % `1 ≟ `0 = no λ ()
% % `1 ≟ `1 = yes refl
% % `a ≟ `[ = no λ ()
% % `a ≟ `] = no λ ()
% % `b ≟ `[ = no λ ()
% % `b ≟ `] = no λ ()
% % `c ≟ `[ = no λ ()
% % `c ≟ `] = no λ ()
% % `0 ≟ `[ = no λ ()
% % `0 ≟ `] = no λ ()
% % `1 ≟ `[ = no λ ()
% % `1 ≟ `] = no λ ()
% % `[ ≟ `a = no λ ()
% % `[ ≟ `b = no λ ()
% % `[ ≟ `c = no λ ()
% % `[ ≟ `0 = no λ ()
% % `[ ≟ `1 = no λ ()
% % `[ ≟ `[ = yes refl
% % `[ ≟ `] = no λ ()
% % `] ≟ `a = no λ ()
% % `] ≟ `b = no λ ()
% % `] ≟ `c = no λ ()
% % `] ≟ `0 = no λ ()
% % `] ≟ `1 = no λ ()
% % `] ≟ `[ = no λ ()
% % `] ≟ `] = yes refl
% 
% % \end{code}
% 
% \subsection{Grammars}\label{sec:gram-and-parsing}
% 
% We have seen in \cref{ex:non-context-free} that our definition of language is very general, comprising even context-sensitive languages. Parsing such languages automatically poses a significant challenge. Hence, we side-step this problem by restricting the scope of our parsers to a smaller well-defined subset of languages. In this subsection, we consider a subset of regular languages without Kleene star (i.e., closure under concatenation). In \cref{sec:context-free}, we extend this class of languages to include fixed points which subsume the Kleene star.
% 
% \begin{code}[hide]
% module ◆ where
% \end{code}
% \begin{code}
%     data Exp : Type₁ where
%         ∅ : Exp
%         ε : Exp
%         `_ : (c : Char) → Exp
%         _·_ : {A : Type} → Dec A → Exp → Exp
%         _∪_ : Exp → Exp → Exp
%         _∗_ : Exp → Exp → Exp
% \end{code}
% 
% This syntax maps directly onto the semantics we defined in \cref{fig:combinators}.
% 
% \begin{code}[hide]
%     typeOfDec : {A : Type} → Dec A → Type
%     typeOfDec {A} _ = A
% \end{code}
% \begin{code}
%     ⟦_⟧ : Exp → Lang
%     ⟦ ∅ ⟧ = ◇.∅
%     ⟦ ε ⟧ = ◇.ε
%     ⟦ ` c ⟧ = ◇.` c
%     ⟦ x · e ⟧ = typeOfDec x ◇.· ⟦ e ⟧
%     ⟦ e ∪ e₁ ⟧ = ⟦ e ⟧ ◇.∪ ⟦ e₁ ⟧
%     ⟦ e ∗ e₁ ⟧ = ⟦ e ⟧ ◇.∗ ⟦ e₁ ⟧
% \end{code}
% 
% \subsection{Parsing}
% 
% To facilitate proving the inclusion of strings in a language, we start by decomposing the problem. A string is either empty or a character followed by the tail of the string. We can decompose the problem of string inclusion along the same dimensions. First, we define nullability $ν$ as the inclusion of the empty string in a language as follows:
% \begin{code}
%     ◇ν : Lang → Type
%     ◇ν ℒ = ℒ []
% \end{code}
% Second, we define the derivative $δ$ of a language $ℒ$ with respect to the character $c$ to be all the suffixes of the words in $ℒ$ which start with the $c$.
% \begin{code}
%     ◇δ : Char → Lang → Lang
%     ◇δ c ℒ = λ w → ℒ (c ∷ w)
% \end{code}
% The relevance of these definitions is shown by \cref{thm:nullability-after-derivatives}.
% \begin{theorem}\label{thm:nullability-after-derivatives}
% Nullability after repeated derivatives fully captures what a language is. Formally, we state this as follows:
% \begin{code}[hide]
%     ν∘foldlδℒ≡ℒ :
% \end{code}
% \begin{code}
%         ◇ν ∘ foldl ◇δ ℒ ≡ ℒ
% \end{code}
% \begin{code}[hide]
%     ν∘foldlδℒ≡ℒ′ : (ℒ : Lang) (w : String) → ◇ν (foldl ◇δ ℒ w) ≡ ℒ w
%     ν∘foldlδℒ≡ℒ′ ℒ [] = refl
%     ν∘foldlδℒ≡ℒ′ ℒ (c ∷ w) = ν∘foldlδℒ≡ℒ′ (◇δ c ℒ) w
% 
%     postulate funext : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {P Q : A → B} → ((x : A) → P x ≡ Q x) → P ≡ Q
% 
%     ν∘foldlδℒ≡ℒ {ℒ = ℒ} = funext (ν∘foldlδℒ≡ℒ′ ℒ)
% \end{code}
% \end{theorem}
% 
% \begin{code}
%     ν : (e : Exp) → Dec (◇ν ⟦ e ⟧)
%     δ : Char → Exp → Exp
%     δ-sound : ∀ e → ⟦ δ c e ⟧ w → ◇δ c ⟦ e ⟧ w
%     δ-complete : ∀ e → ◇δ c ⟦ e ⟧ w → ⟦ δ c e ⟧ w
% \end{code}
% 
% \begin{code}[hide]
%     map' : ∀{A B} → (A → B) → (B → A) → Dec A → Dec B
%     map' = map′
% \end{code}
% \begin{code}
%     parse : (e : Exp) (w : String) → Dec (⟦ e ⟧ w)
%     parse e [] = ν e
%     parse e (c ∷ w) = map' (δ-sound e) (δ-complete e) (parse (δ c e) w)
% \end{code}
% 
% \subsection{Nullability}
% 
% \begin{lemma}
% Two languages, $\ab{ℒ₁}$ and $\ab{ℒ₂}$, are nullable if and only if their concatenation, $\ab{ℒ₁}~\af{◇.∗}~\ab{ℒ₂}$, is nullable. 
% \begin{code}
%     ν∗ : (◇ν ℒ₁ × ◇ν ℒ₂) ⇔ ◇ν (ℒ₁ ◇.∗ ℒ₂)
% \end{code}
% \begin{code}[hide]
%     ν∗ = mk⇔ (λ x → [] , [] , refl , x) λ { ([] , [] , refl , x) → x }
% \end{code}
% \end{lemma}
% 
% \begin{code}
%     ν ∅ = no λ ()
%     ν ε = yes refl
%     ν (` c) = no λ ()
%     ν (x · e) = x ×-dec ν e 
%     ν (e ∪ e₁) = ν e ⊎-dec ν e₁
%     ν (e ∗ e₁) = Dec.map ν∗ (ν e ×-dec ν e₁)
% \end{code}
% 
% \subsection{Derivation}
% 
% \begin{code}
%     δ c ∅ = ∅
%     δ c ε = ∅
%     δ c (` c₁) = (c ≟ c₁) · ε -- a bit interesting
%     δ c (x · e) = x · δ c e
%     δ c (e ∪ e₁) = δ c e ∪ δ c e₁
%     δ c (e ∗ e₁) = (δ c e ∗ e₁) ∪ (ν e · δ c e₁) -- interesting
% \end{code}
% 
% The proofs are very straightforward:
% 
% \begin{code}
%     δ-sound (` c) (refl , refl) = refl
%     δ-sound (x₁ · e) (x , y) = x , δ-sound e y
%     δ-sound (e ∪ e₁) (inj₁ x) = inj₁ (δ-sound e x)
%     δ-sound (e ∪ e₁) (inj₂ y) = inj₂ (δ-sound e₁ y)
%     δ-sound (e ∗ e₁) (inj₁ (u , v , refl , x , y)) = _ ∷ u , v , refl , δ-sound e x , y
%     δ-sound (e ∗ e₁) (inj₂ (x , y)) = [] , _ , refl , x , δ-sound e₁ y
% \end{code}
% 
% \begin{code}
%     δ-complete (` c) refl = refl , refl
%     δ-complete (x₁ · e) (x , y) = x , δ-complete e y
%     δ-complete (e ∪ e₁) (inj₁ x) = inj₁ (δ-complete e x)
%     δ-complete (e ∪ e₁) (inj₂ y) = inj₂ (δ-complete e₁ y)
%     δ-complete (e ∗ e₁) (_ ∷ _ , _ , refl , x , y) = inj₁ (_ , _ , refl , δ-complete e x , y)
%     δ-complete (e ∗ e₁) ([] , _ , refl , x , y) = inj₂ (x , δ-complete e₁ y)
% \end{code}
% 
% % \begin{code}[hide]
% % module Simple where
% % \end{code}
% % \begin{code}
% %     data Gram : Lang → Type₁ where
% %         ∅     :                       Gram (λ _ → ⊥)
% %         ε     :                       Gram (λ w → w ≡ [])
% %         char  : (c : Char)         →  Gram (λ w → w ≡ c ∷ [])
% %         _·_   : Dec A → Gram ℒ     →  Gram (λ w → A × ℒ w)
% %         _∪_   : Gram ℒ₁ → Gram ℒ₂  →  Gram (λ w → ℒ₁ w ⊎ ℒ₂ w)
% %         _∗_   : Gram ℒ₁ → Gram ℒ₂
% %               → Gram (λ w → Σ String λ u → Σ String λ v → (w ≡ u ++ v) × ℒ₁ u × ℒ₂ v)
% %         _◃_   : (ℒ₁ ⇔ ℒ₂) → Gram ℒ₁ → Gram ℒ₂
% % \end{code}
% % \begin{code}[hide]
% %     variable G G₁ G₂ : Gram ℒ
% % \end{code}
% % \begin{remark}
% % The \af{Gram} data type is parameterized by its language. This ties the constructors directly to their semantics.
% % \end{remark}
% % 
% % By recursion over this data type of grammars, we can define a decision procedure for nullability and derivative function; both are correct by construction.
% % \begin{code}
% %     ν? : Gram ℒ → Dec (ν ℒ)
% %     δ? : Gram ℒ → (c : Char) → Gram (δ ℒ c)
% % \end{code}
% % \begin{code}[hide]
% %     ν∗ : (ν ℒ₁ × ν ℒ₂) ↔ Σ String λ u → Σ String λ v → ([] ≡ (u ++ v)) × ℒ₁ u × ℒ₂ v
% %     to ν∗ (x , y) = [] , [] , refl , x , y
% %     from ν∗ ([] , [] , refl , x , y) = x , y
% % 
% %     ν? ∅ = no λ ()
% %     ν? ε = yes refl
% %     ν? (char c) = no λ ()
% %     ν? (x · G) = x ×? ν? G
% %     ν? (G₁ ∪ G₂) = ν? G₁ ⊎? ν? G₂
% %     ν? (G₁ ∗ G₂) = map? ν∗ (ν? G₁ ×? ν? G₂)
% %     ν? (f ◃ G₂) = map? f (ν? G₂)
% % \end{code}
% % \begin{code}[hide]
% %     δ? ∅ c = ∅
% %     δ? ε c = record { to = λ () ; from = λ () } ◃ ∅
% %     δ? (char c′) c with c ≟ c′
% %     ... | yes refl = (λ { {[]} → record { to = λ _ → refl ; from = λ _ → refl } ; {_ ∷ _} → record { to = λ () ; from = λ () }}) ◃ ε
% %     ... | no ¬c≡c′ = (λ { {[]} → record { to = λ () ; from = λ { refl → ¬c≡c′ refl }} ; {_ ∷ _} → record { to = λ () ; from = λ () }}) ◃ ∅
% %     δ? (A · G) c = A · δ? G c
% %     δ? (G₁ ∪ G₂) c = δ? G₁ c ∪ δ? G₂ c
% %     δ? (G₁ ∗ G₂) c = (record { to = λ { (inl (u , v , refl , x , y)) → (c ∷ u) , v , refl , x , y ; (inr (x , y)) → [] , (c ∷ _) , refl , x , y } ; from = λ { ([] , _ , refl , x , y) → inr (x , y) ; ((_ ∷ u) , v , refl , x , y) → inl (u , v , refl , x , y) } } ) ◃ ((δ? G₁ c ∗ G₂) ∪ (ν? G₁ · δ? G₂ c))
% %     δ? (f ◃ G₂) c = f ◃ δ? G₂ c
% % 
% %     -- δ?↔δ : ⟦ δ? c G ⟧ w ↔ δ c ⟦ G ⟧ w
% % \end{code}
% % \begin{code}[hide]
% %     -- to (δ?↔δ {c} {G = ` c′}) x with c ≟ c′
% %     -- to (δ?↔δ {c} {` .c}) refl | yes refl = refl
% %     -- to (δ?↔δ {_} {` _}) () | no _
% %     -- to (δ?↔δ {G = A · G}) (x , y) = x , to δ?↔δ y
% %     -- to (δ?↔δ {G = G₁ ∪ G₂}) (inl x) = inl (to δ?↔δ x)
% %     -- to (δ?↔δ {G = G₁ ∪ G₂}) (inr x) = inr (to δ?↔δ x)
% %     -- to (δ?↔δ {c} {G = G₁ ▹ G₂}) (inl (u , v , refl , x , y)) = (c ∷ u) , v , refl , to δ?↔δ x , y
% %     -- to (δ?↔δ {c} {G = G₁ ▹ G₂} {w}) (inr (π₁ , π₂)) = [] , (c ∷ w) , refl , π₁ , to δ?↔δ π₂
% %     -- from (δ?↔δ {c} {G = ` c′}) x with c ≟ c′
% %     -- from (δ?↔δ {c} {` c}) refl | yes refl = refl
% %     -- from (δ?↔δ {c} {` .c}) refl | no ¬c≡c = ¬c≡c refl
% %     -- from (δ?↔δ {G = A · G}) (π₁ , π₂) = π₁ , from δ?↔δ π₂
% %     -- from (δ?↔δ {G = G ∪ G₁}) (inl x) = inl (from δ?↔δ x)
% %     -- from (δ?↔δ {G = G ∪ G₁}) (inr x) = inr (from δ?↔δ x)
% %     -- from (δ?↔δ {c} {G = G ▹ G₁}) ([] , (.c ∷ v) , refl , x , y) = inr (x , from δ?↔δ y)
% %     -- from (δ?↔δ {c} {G = G ▹ G₁}) ((.c ∷ u) , v , refl , x , y) = inl (u , v , refl , from δ?↔δ x , y)
% %     transport : {ℓ₁ : Level} {A : Set ℓ₁} {B : Set ℓ₁} → A ≡ B → A → B
% %     transport refl x = x
% % \end{code}
% % Together, decidable nullability and the derivative function can be combined to decide whether any string is in the language described by a grammar.
% % \begin{code}
% %     parse : Gram ℒ → (w : String) → Dec (ℒ w)
% %     parse G [] = ν? G
% %     parse G (c ∷ w) = parse (δ? G c) w
% % \end{code}
% % Thus, we have defined a parser for our simple grammars.
% 
% % A language is a set of strings $\mathbb{2}^{(\af{List}~\af{Token})}$.
% % 
% % 
% % \begin{code}[hide]
% % Lang : Set₁
% % \end{code}
% % \begin{code}
% % Lang = List Token → Set
% % \end{code}
% % 
% % This type has a very rich structure. It forms an ... algebra with union and intersection and a semiring with union and sequential composition.
% % 
% % \begin{code}
% % ∅ : Lang
% % ∅ _ = ⊥
% % \end{code}
% % 
% % Going beyond work by Elliott, we can try to define context-free grammars.
% % Unfortunately, we quickly run into issues due to nontermination. It is not easy
% % to show that a grammar defined in this way is well-founded. To solve this issue
% % we can use guarded type theory, in our case provided by guarded cubical Agda.
% % This allows us to define arbitrary fixed points of languages.
% % 
% % \begin{code}
% % fueled : (Lang → Lang) → ℕ → Lang
% % fueled f 0 = ∅
% % fueled f (suc n) = f (fueled f n)
% % \end{code}
% % 
% % \begin{code}
% % fix : (Lang → Lang) → Lang
% % fix f w = ∃[ n ] fueled f n w
% % \end{code}
% 