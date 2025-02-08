open import Data.Char using (Char)

data Ob : Set where
  𝟏     : Ob
  _×_   : Ob → Ob → Ob
  -- _⇒_   : Ob → Ob → Ob
  Lang  : Ob

variable A B C : Ob

data K : Ob → Ob → Set where

  -- ev       : K (A ⇒ (B × A)) B
  -- curry    : K (A × B) C → K A (B ⇒ C)
  -- uncurry  : K A (B ⇒ C) → K (A × B) C

  -- fork     : K A B → K A C → K A (B × C)
  exl      : K (A × B) A
  exr      : K (A × B) B

  -- id       : K A A
  compose  : K B C → K A B → K A C

  ∅        : K A Lang
  ε        : K A Lang
  _∪_      : K A Lang → K A Lang → K A Lang
  _∗_      : K A Lang → K A Lang → K A Lang
  `_       : Char → K A Lang
  μ        : K (Lang × A) Lang → K A Lang

-- const : K 𝟏 (A ⇒ (B ⇒ A))
-- const = curry (compose (curry exl) exr)

expr : K 𝟏 Lang
expr = μ ((` 'x') ∪ (exl ∗ ((` '+') ∗ exl)))

-- mutual recursion of expressions and statements
lang : K 𝟏 Lang
lang
  = μ ((` 'x')
    ∪ ((exl ∗ ((` '+') ∗ exl))
    ∪ ((` '{') ∗ (μ (((` '!') ∗ compose exl exr)
                    ∪ (exl ∗ ((` ';') ∗ exl)))
               ∗ (` '}')))))
