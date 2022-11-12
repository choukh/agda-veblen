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
open import Ordinal.WellFormed using (wellFormed; ⌜_⌝; ω; n<ω; n≤ω)
open import Ordinal.Arithmetic
open import Ordinal.Tetration using (_^^[_]_)
open import Veblen.Fixpoint.Lower using (π; π-fp; π≈)
open import Veblen.Epsilon using (ε; ε-normal; ε-fp)

open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
```

## ε的另一种表示

首先是一些准备工作. 我们一般化 `ε` 的下标, 并声明 `εα>1` 实例.

```agda
private variable
  α : Ord

instance
  εα>1 : ε α > ⌜ 1 ⌝
  εα>1 {α} =  begin-strict
    ⌜ 1 ⌝     <⟨ n<ω ⟩
    ω         ≈˘⟨ ^-identityʳ _ ⟩
    ω ^ ⌜ 1 ⌝ ≤⟨ ≤f⇒≤l {n = 2} ≤-refl ⟩
    ε ⌜ 0 ⌝   ≤⟨ proj₁ ε-normal z≤ ⟩
    ε α       ∎
```

观察序列 `ω ^^[ suc (ε α) ] ⌜_⌝` 的前几项有

$${ε_α}^+ = {ε_α}^+$$

```agda
_ : ω ^^[ suc (ε α) ] ⌜ 0 ⌝ ≡ suc (ε α)
_ = refl
```
&nbsp;

$$ω^{{ε_α}^+} = ε_α × ω$$

```agda
ω^^[sε]1 : ω ^^[ suc (ε α) ] ⌜ 1 ⌝ ≈ ε α * ω
ω^^[sε]1 {α} =  begin-equality
  ω ^ ε α * ω   ≈⟨ *-congʳ {ω} (ε-fp α) ⟩
  ε α * ω       ∎
```
&nbsp;

$$ω^{ω^{{ε_α}^+}} = {ε_α}^ω$$

```agda
ω^^[sε]2 : ω ^^[ suc (ε α) ] ⌜ 2 ⌝ ≈ ε α ^ ω
ω^^[sε]2 {α} =                begin-equality
  ω ^ ω ^^[ suc (ε α) ] ⌜ 1 ⌝ ≈⟨ ^-congˡ ⦃ n≤ω ⦄ ω^^[sε]1 ⟩
  ω ^ (ε α * ω)               ≈˘⟨ ^-*-assoc _ _ _ ⟩
  (ω ^ ε α) ^ ω               ≈⟨ ^-congʳ {ω} (ε-fp α) ⟩
  ε α ^ ω                     ∎
```
&nbsp;

$$ω^{ω^{ω^{{ε_α}^+}}} = {ε_α}^{{ε_α}^ω}$$

```agda
ω^^[sε]3 : ω ^^[ suc (ε α) ] ⌜ 3 ⌝ ≈ ε α ^ (ε α ^ ω)
ω^^[sε]3 {α} =                begin-equality
  ω ^ ω ^^[ suc (ε α) ] ⌜ 2 ⌝ ≈⟨ ^-congˡ ⦃ n≤ω ⦄ (begin-equality
      ω ^^[ suc (ε α) ] ⌜ 2 ⌝ ≈⟨ ω^^[sε]2 ⟩
      ε α ^ ω                 ≈˘⟨ π₁ ⟩
      π ⌜ 1 ⌝                 ≈˘⟨ π-fp _ ⟩
      ε α * π ⌜ 1 ⌝           ∎) ⟩
  ω ^ (ε α * π ⌜ 1 ⌝)         ≈˘⟨ ^-*-assoc _ _ _ ⟩
  (ω ^ ε α) ^ π ⌜ 1 ⌝         ≈⟨ ^-congʳ {π ⌜ 1 ⌝} (ε-fp α) ⟩
  ε α ^ π ⌜ 1 ⌝               ≈⟨ ^-congˡ π₁ ⟩
  ε α ^ (ε α ^ ω)             ∎ where
    π₁ =                      begin-equality
      π ⌜ 1 ⌝                 ≈⟨ π≈ _ ⟩
      ε α ^ ω * ⌜ 1 ⌝         ≈⟨ *-identityʳ _ ⟩
      ε α ^ ω                 ∎
```
&nbsp;

$$ω^{ω^{ω^{.^{.^{{ε_α}^+}}}}} = {ε_α}^{{ε_α}^{.^{.^ω}}}$$
 