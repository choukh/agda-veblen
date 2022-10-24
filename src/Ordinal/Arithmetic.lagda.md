---
title: Agda大序数(5) 序数算术
zhihu-tags: Agda, 序数, 大数数学
---

# Agda大序数(5) 序数算术

> 交流Q群: 893531731  
> 总目录: [Everything.html](https://choukh.github.io/agda-lvo/Everything.html)  
> 本文源码: [Ordinal/Arithmetic.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/Ordinal/Arithmetic.lagda.md)  
> 高亮渲染: [Ordinal.Arithmetic.html](https://choukh.github.io/agda-lvo/Ordinal.Arithmetic.html)  
> 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

**(本章施工中)**

```agda
{-# OPTIONS --without-K --safe #-}

module Ordinal.Arithmetic where
```

本章在内容上延续前四章.

```agda
open import Ordinal
open import Ordinal.WellFormed using (wellFormed)
open import Ordinal.Function
open import Ordinal.Recursion
```

```agda
open import Data.Nat as ℕ using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
```

```agda
infixl 6 _+_
infixl 7 _*_
infixl 8 _^_

_+_ : Ord → Ord → Ord
α + β = rec suc from α by β

_*_ : Ord → Ord → Ord
α * β = rec (_+ α) from zero by β

_^_ : Ord → Ord → Ord
α ^ β = rec (_* α) from (suc zero) by β
```

```agda
_ : ∀ {α} → α + zero ≡ α
_ = refl

_ : ∀ {α} → α + suc zero ≡ suc α
_ = refl

_ : ∀ {α β} → α + suc β ≡ suc (α + β)
_ = refl
```