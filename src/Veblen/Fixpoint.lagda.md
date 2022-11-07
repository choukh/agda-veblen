---
title: Agda大序数(6) 序数嵌入的不动点
zhihu-tags: Agda, 序数, 大数数学
---

# Agda大序数(6) 序数嵌入的不动点

> 交流Q群: 893531731  
> 总目录: [Everything.html](https://choukh.github.io/agda-lvo/Everything.html)  
> 本文源码: [Veblen/Fixpoint.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/Veblen/Fixpoint.lagda.md)  
> 高亮渲染: [Veblen.Fixpoint.html](https://choukh.github.io/agda-lvo/Veblen.Fixpoint.html)  
> 如果你在知乎看到本文: 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

**(本章施工中)**

```agda
{-# OPTIONS --without-K --safe #-}

module Veblen.Fixpoint where
```

## 前置

本章建立序数嵌入的不动点理论, 需要开头四章作为前置.

```agda
open import Ordinal
open Ordinal.≤-Reasoning
open import Ordinal.WellFormed
open import Ordinal.Function
open import Ordinal.Recursion
```

以下是标准库依赖.

```agda
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
```

## 不动点

我们说序数 `α` 是序数函数 `F` 的不动点, 当且仅当 `F α ≈ α`.

```agda
_isFixpointOf_ : Ord → (Ord → Ord) → Set
α isFixpointOf F = F α ≈ α
```

我们说 `rec F from α₀ by ω` 是 `F` 从 `α₀` 开始的无穷递归, 记作 `ω-rec F from α₀`.

```agda
ω-rec_from_ : (Ord → Ord) → Ord → Ord
ω-rec F from α₀ = rec F from α₀ by ω
```

由超限递归的相关引理立即可知无穷递归保持函数的弱增长性和 ≤-单调性.

```agda
module _ {F : Ord → Ord} where

  ω-rec-pres-incr-≤ : ≤-increasing F → ≤-increasing (ω-rec F from_)
  ω-rec-pres-incr-≤ ≤-incr = rec-from-incr-≤ ω ≤-incr

  ω-rec-pres-mono-≤ : ≤-monotonic F → ≤-monotonic (ω-rec F from_)
  ω-rec-pres-mono-≤ ≤-mono = rec-from-mono-≤ ω ≤-mono
```

现在, 固定一个序数嵌入 `F`.

```agda
module _ (F : Ord → Ord) (nml@(≤-mono , <-mono , lim-ct) : normal F) where
```

**引理** `F` 的从任意初始值开始的无穷递归都是 `F` 的不动点.

```agda
  ω-rec-fp : ∀ α₀ → (ω-rec F from α₀) isFixpointOf F
  ω-rec-fp α₀ =                            begin-equality
    F (ω-rec F from α₀)                    ≈⟨ lim-ct _ ⟩
    lim (λ n → F (rec F from α₀ by ⌜ n ⌝)) ≈⟨ l≤ (λ n → ≤f⇒≤l {n = suc n} ≤-refl)
                                            , l≤ (λ n → ≤f⇒≤l {n = n} (normal⇒≤-incr nml _)) ⟩
    ω-rec F from α₀                        ∎
```

**引理** `ω-rec F from_` 弱增长.  
**证明** 用 `normal⇒≤-incr` 消掉 `ω-rec-pres-incr-≤` 的前提即可. ∎

```agda
  ω-rec-incr-≤ : ≤-increasing (ω-rec F from_)
  ω-rec-incr-≤ = ω-rec-pres-incr-≤ (normal⇒≤-incr nml)
```

**注意** 上述引理说明存在 `F` 的任意大的不动点.

## 最小不动点

`F` 的从零开始的无穷递归是 `F` 最小不动点.

```agda
  _₀ : (Ord → Ord) → Ord
  F ₀ = ω-rec F from zero

  ₀-fp : (F ₀) isFixpointOf F
  ₀-fp = ω-rec-fp zero

  ₀-min : ∀ {α} → α isFixpointOf F → F ₀ ≤ α
  ₀-min {α} fp = l≤ helper where
    helper : ∀ n → (rec F from zero by ⌜ n ⌝) ≤ α
    helper zero = z≤
    helper (suc n) =              begin
      rec F from zero by ⌜ suc n ⌝ ≤⟨ ≤-mono (helper n) ⟩
      F α                          ≈⟨ fp ⟩
      α                            ∎
```
