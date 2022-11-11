---
title: Agda大序数(8*) ε的另一种表示
zhihu-tags: Agda, 序数, 大数数学
zhihu-url: https://zhuanlan.zhihu.com/p/582661842
---

# Agda大序数(8*) ε的另一种表示

> 交流Q群: 893531731  
> 总目录: [Everything.html](https://choukh.github.io/agda-lvo/Everything.html)  
> 本文源码: [Veblen/Epsilon/Alternative.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/Veblen/Epsilon/Alternative.lagda.md)  
> 高亮渲染: [Veblen.Epsilon.Alternative.html](https://choukh.github.io/agda-lvo/Veblen.Epsilon.Alternative.html)  
> 如果你在知乎看到本文: 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

```agda
{-# OPTIONS --without-K --safe --experimental-lossy-unification #-}

module Veblen.Epsilon.Alternative where
```

## 前置

```agda
open import Ordinal
open Ordinal.≤-Reasoning
open import Ordinal.WellFormed using (wellFormed; ⌜_⌝; ω)
open import Ordinal.Arithmetic
open import Ordinal.Tetration using (_^^[_]_)
open import Veblen.Epsilon using (ε; ε-fp; ω≥1)

open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
```

## ε的另一种表示

我们一般化 `ε` 的下标.

```agda
private variable
  α : Ord
```

首先, 观察 `ω ^^[ suc (ε α) ] ⌜ n ⌝` 的前几层有

$${ε_α}^+ = {ε_α}^+$$

```agda
_ : ω ^^[ suc (ε α) ] ⌜ 0 ⌝ ≡ suc (ε α)
_ = refl
```

$$ω^{{ε_α}^+} = ε_α × ω$$

```agda
ω^^[sε]1 : ω ^^[ suc (ε α) ] ⌜ 1 ⌝ ≈ ε α * ω
ω^^[sε]1 {α} =                begin-equality
  ω ^ ε α * ω                 ≈⟨ *-congʳ {ω} (ε-fp α) ⟩
  ε α * ω                     ∎
```

$$ω^{ω^{{ε_α}^+}} = {ε_α}^ω$$

```agda
ω^^[sε]2 : ω ^^[ suc (ε α) ] ⌜ 2 ⌝ ≈ ε α ^ ω
ω^^[sε]2 {α} =                begin-equality
  ω ^ ω ^^[ suc (ε α) ] ⌜ 1 ⌝ ≈⟨ ^-congˡ ω≥1 ω^^[sε]1 ⟩
  ω ^ (ε α * ω)               ≈˘⟨ ^-*-assoc _ _ _ ⟩
  ω ^ ε α ^ ω                 ≈⟨ ^-congʳ {ω} (ε-fp α) ⟩
  ε α ^ ω                     ∎
```

$$ω^{ω^{ω^{{ε_α}^+}}} = {ε_α}^{{ε_α}^ω}$$

$$ω^{ω^{ω^{.^{.^{{ε_α}^+}}}}} = {ε_α}^{{ε_α}^{.^{.^ω}}}$$
