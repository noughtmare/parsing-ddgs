{-# OPTIONS --guardedness #-}

open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Data.Nat
open import Data.Fin

Type₁ : Set₂
Type₁ = Set₁

Type : Set₁
Type = Set

data Tok : Type where

data String : Type where
  [] : String
  _∷_ : Tok → String → String

postulate _++_ : (_ _ : String) → String

data Gram (n : ℕ) : Type where
    ∅    : Gram n
    ε    : Gram n
    char : (c : Tok) → Gram n
    _∪_  : (G₁ G₂ : Gram n) → Gram n
    _▸_  : (G₁ G₂ : Gram n) → Gram n
    var  : Fin n → Gram n
    μ    : Gram (suc n) → Gram n

variable w : String
         n : ℕ

data Env : ℕ → Type₁ where
  [] : Env zero
  _∷_ : (String → Type) → Env n → Env (suc n)

lookup : Fin n → Env n → String → Type
lookup zero (x ∷ Γ) = x
lookup (suc i) (x ∷ Γ) = lookup i Γ

⟦_⊢_⟧ : Env n → Gram n → String → Type

data ▹⟦_⊢_⟧ (Γ : Env n) (G : Gram (suc n)) (w : String) : Type where
  ▹ : ⟦ {!!} ∷ Γ ⊢ G ⟧ w → ▹⟦ Γ ⊢ G ⟧ w

⟦ Γ ⊢ ∅ ⟧ w = ⊥
⟦ Γ ⊢ ε ⟧ w = w ≡ [] 
⟦ Γ ⊢ char c ⟧ w = w ≡ (c ∷ [])
⟦ Γ ⊢ G₁ ∪ G₂ ⟧ w = ⟦ Γ ⊢ G₁ ⟧ w ⊎ ⟦ Γ ⊢ G₂ ⟧ w 
⟦ Γ ⊢ G₁ ▸ G₂ ⟧ w = ∃ λ u → ∃ λ v → (w ≡ u ++ v) × ⟦ Γ ⊢ G₁ ⟧ u × ⟦ Γ ⊢ G₂ ⟧ v
⟦ Γ ⊢ var i ⟧ w = lookup i Γ w
⟦ Γ ⊢ μ G ⟧ w = ▹⟦ Γ ⊢ G ⟧ w
