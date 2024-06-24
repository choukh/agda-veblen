# Veblen Function in Agda

## Features

- --without-K and --safe
- Ready for googology function such as fast growing hierarchy
- Literate agda script (but in Chinese) and [html5 rendering](https://choukh.github.io/agda-veblen/NonWellFormed.html)

## Contents

### [Ordinal.lagda.md](https://github.com/choukh/agda-veblen/blob/main/src/NonWellFormed/Ordinal.lagda.md)

- Inductive definition of Brouwer ordinal
- Inductive definition of non-strict order `_≤_`
- Equality `_≈_` and strict order `_<_` are defined by `_≤_`
- Partial ordering of `_≤_` and strict ordering of `_<_` is proved
- No total ordering, but that's fine

### [WellFormed.lagda.md](https://github.com/choukh/agda-veblen/blob/main/src/NonWellFormed/WellFormed.lagda.md)

- Well formed (WF) ordinals are those constructed hereditarily by strictly increasing sequence
- WF of finite ordinals and `ω` is proved

### [Function.lagda.md](https://github.com/choukh/agda-veblen/blob/main/src/NonWellFormed/Function.lagda.md)

- Common properties of ordinal functions are defined
- Definition of normal function is adapted for constructive setup

### [Recursion.lagda.md](https://github.com/choukh/agda-veblen/blob/main/src/NonWellFormed/Recursion.lagda.md)

- General form of ordianl recursive function is defined and its properties are proved

### [Arithmetic.lagda.md](https://github.com/choukh/agda-veblen/blob/main/src/NonWellFormed/Arithmetic.lagda.md)

- `_+_`, `_*_` and `_^_` are defined by recursion and their WF preserving properties are proved
- Association law, distribution law, etc

### [Tetration.lagda.md](https://github.com/choukh/agda-veblen/blob/main/src/NonWellFormed/Tetration.lagda.md)

- We show that tetration is no-go since `α ^^ suc ω ≈ α ^^ ω` and, moreover, `α ^^ β ≈ α ^^ ω` forall `β ≥ ω`

### [Fixpoint.lagda.md](https://github.com/choukh/agda-veblen/blob/main/src/NonWellFormed/Fixpoint.lagda.md)

- Infinite iteration `_⋱_` is defined
- If `F` is normal then `F ⋱ α` is a fixed point not less than `α`
- Recursion of `F ⋱_ ∘ suc` is the fixed point yielding function of `F`, written `F ′`
- We proved that higher order function `_′` is normal-preserving and wf-preserving-preserving

### [Fixpoint.Lower.lagda.md](https://github.com/choukh/agda-veblen/blob/main/src/NonWellFormed/Fixpoint/Lower.lagda.md)

- Trivial examples of fixed point

### [Epsilon.lagda.md](https://github.com/choukh/agda-veblen/blob/main/src/NonWellFormed/Epsilon.lagda.md)

- ε function is defined as `(ω ^_) ′`
- We have `ε (suc α) ≡ ω ^^[ suc (ε α) ] ω` forall `α`
- ζ is defined as `ε ′` and η as `ζ ′`
- `ε`, `ζ`, `η`, ... are all normal and WF preserving

### [Epsilon.Alternative.lagda.md](https://github.com/choukh/agda-veblen/blob/main/src/NonWellFormed/Epsilon/Alternative.lagda.md)

- We proved `ε (suc α) ≈ ε α ^^ ω` forall WF `α`

### [VeblenFunction.lagda.md](https://github.com/choukh/agda-veblen/blob/main/src/NonWellFormed/VeblenFunction.lagda.md)

- Veblen function `φ α β` is defined
- We show that `φ` is normal, monotonic, congruence and wf-preserving
- Γ₀ is defined as `(λ α → φ α zero) ⋱ zero`

There is also a well formed version of most of the above in [src/WellFormed](https://github.com/choukh/agda-veblen/blob/main/src/WellFormed). From Γ₀ on, there will be only the well formed version.

## License

[AGPL-3.0](https://github.com/choukh/agda-veblen/blob/main/LICENSE)
