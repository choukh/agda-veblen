# Large veblen ordinal in Agda

## Features

- Solely relies on agda-stdlib 1.7.1
- --without-K and --safe
- Up to large veblen ordinal
- Ready for googology function such as fast growing hierarchy
- Literate agda script (but in Chinese)

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

### Ordinal.Arithmetic.lagda.md

(TODO)

### Ordinal.Tetration.lagda.md

(TODO)

### Veblen.Fixpoint.lagda.md

(TODO)

### Veblen.EpsilonNumbers.lagda.md

(TODO)

### Veblen.Function.lagda.md

(TODO)

### Veblen.Extended.lagda.md

(TODO)

### Veblen.OmegaAry.lagda.md

(TODO)

### Veblen.Transfinite.lagda.md

(TODO)
