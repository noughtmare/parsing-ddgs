{-# OPTIONS --guardedness --safe #-}

module Lang where

open import Agda.Primitive using (Level ; _⊔_)
open import Prelude

Lang : Set₁
Lang = List T.Tok → Set

ν : Lang → Set
ν ℒ = ℒ []

δ : T.Tok → Lang → Lang
(δ c ℒ) w = ℒ (c ∷ w)
