{-# OPTIONS --guardedness #-}

open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Sum
open import Data.Product

Type : Set₁
Type = Set

data Tok : Type where

data String : Type where
  [] : String
  _∷_ : Tok → String → String

postulate _++_ : (_ _ : String) → String

mutual
    data Gram : Type where
        ∅    : Gram
        ε    : Gram
        char : (c : Tok) → Gram
        _∪_  : (G₁ G₂ : Gram) → Gram
        _▸_  : (G₁ G₂ : Gram) → Gram
        ∞    : (∞G : ∞Gram) → Gram

    record ∞Gram : Type where
        coinductive
        field ! : Gram

open ∞Gram

variable w : String

⟦_⟧ : Gram → String → Type

data ∞⟦_⟧ (∞G : ∞Gram) (w : String) : Type where
  ∞ : ⟦ ∞G .! ⟧ w → ∞⟦ ∞G ⟧ w

⟦ ∅ ⟧ w = ⊥
⟦ ε ⟧ w = w ≡ [] 
⟦ char c ⟧ w = w ≡ (c ∷ [])
⟦ G₁ ∪ G₂ ⟧ w = ⟦ G₁ ⟧ w ⊎ ⟦ G₂ ⟧ w 
⟦ G₁ ▸ G₂ ⟧ w = ∃ λ u → ∃ λ v → (w ≡ u ++ v) × ⟦ G₁ ⟧ u × ⟦ G₂ ⟧ v
⟦ ∞ ∞G ⟧ w = ∞⟦ ∞G ⟧ w
