One of the goals of this project is extending Conal Elliot's work on defining
regular languages in Agda to cover also context-free languages.
A simple way to accomplish that is to add a fixed point combinator to his
language constructions.
It has been conjectured and informally shown that this gives the system at least
as much power as context-free languages require (perhaps there is even related
work that contains an actual proof?).

Unfortunately, defining a fixed point in Agda --- and in mathematics in general
--- is not straightforward because such fixed points must be shown to be
well-founded (is that the right terminology?). 
We cannot, as we might naively attempt, define the fixed point as follows:
```agda
fix : (Lang -> Lang) -> Lang
fix f w = f (fix f w) w
```
Agda rejects this definition outright, but even in mathematics in general, this
function is not well defined if `f` is, for example, the identity function (I
want to stress that this is not an Agda-specific issue).

There are several approaches 



Definitions of ν and δ:

> ν L := ε ∈ L
> w ∈ δₐ L := (a ∷ w) ∈ L

Definition of μ:

> μₓ L = L[x := μₓ L]

Properties necessary for decidable parsing:

> ν (μₓ L) = ν (L[x := ∅])

> δₐ Γ x := y where [x := y] ∈ Γ
> δₐ Γ (μₓ L) = μₖ ((δₐ [x := k, Γ] L)[x := μₓ L])

The rest of the properties are the same as in Conal's work (except that the Γ needs to be propagated properly through his δ properties).