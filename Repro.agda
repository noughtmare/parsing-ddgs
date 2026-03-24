postulate A : Set

variable P : A → Set

postulate π-id : (x : A) → P x → P x

postulate foo : A → Set
postulate π-foo : (x : A) → foo x

bar : (x : A) → foo x
bar x = π-id x (π-foo x)
