# Large veblen ordinal in Agda

## Features

- Solely relies on agda-stdlib 1.7.1
- --without-K and --safe
- Up to large veblen ordinal
- Ready for googology function such as fast growing hierarchy
- Literate agda script (but in Chinese) and [html5 rendering](https://choukh.github.io/agda-lvo/Everything.html)

## Contents

### [Ordinal.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/Ordinal.lagda.md)

- Inductive definition of Brouwer ordinal
- Inductive definition of non-strict order `_≤_`
- Equality `_≈_` and strict order `_<_` are defined by `_≤_`
- Partial ordering of `_≤_` and strict ordering of `_<_` is proved
- No total ordering, but that's fine

### [Ordinal.WellFormed.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/Ordinal/WellFormed.lagda.md)

- Well formed (WF) ordinals are those constructed hereditarily by strictly increasing sequence
- WF of finite ordinals and `ω` is proved

### [Ordinal.Function.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/Ordinal/Function.lagda.md)

- Common properties of ordinal functions are defined
- Definition of normal function is adapted for constructive setup

### [Ordinal.Recursion.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/Ordinal/Recursion.lagda.md)

- General form of ordianl recursive function is defined and its properties are proved

### [Ordinal.Arithmetic.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/Ordinal/Arithmetic.lagda.md)

- `_+_`, `_*_` and `_^_` are defined by recursion and their WF preserving properties are proved
- Association law, distribution law, etc

### [Ordinal.Tetration.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/Ordinal/Tetration.lagda.md)

- We show that tetration is no-go since `α ^^ suc ω ≈ α ^^ ω` and, moreover, `α ^^ β ≈ α ^^ ω` forall `β ≥ ω`

### [Veblen.Fixpoint.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/Veblen/Fixpoint.lagda.md)

- Infinite iteration `ω-rec` is defined
- If `f` is normal then `ω-rec f from α` is a fixed point not less than `α`
- Recursion of `ω-rec f from (suc _)` is the fixed point yielding function of `f`, written `f′`
- We proved that higher order function `_′` is normal-preserving and wf-preserving-preserving

### [Veblen.Fixpoint.Lower.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/Veblen/Fixpoint.Lower.lagda.md)

- Trivial examples of fixed point

### Veblen.Epsilon.lagda.md

(TODO)

### Veblen.Function.lagda.md

(TODO)

### Veblen.Extended.lagda.md

(TODO)

### Veblen.OmegaAry.lagda.md

(TODO)

### Veblen.Transfinite.lagda.md

(TODO)

## License

[AGPL-3.0](https://github.com/choukh/agda-lvo/blob/main/LICENSE)
