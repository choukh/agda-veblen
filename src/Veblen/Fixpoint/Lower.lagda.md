---
title: Agda大序数(7*) 低级不动点
zhihu-tags: Agda, 序数, 大数数学
zhihu-url: https://zhuanlan.zhihu.com/p/581675452
---

# Agda大序数(7*) 低级不动点

> 交流Q群: 893531731  
> 总目录: [Everything.html](https://choukh.github.io/agda-lvo/Everything.html)  
> 本文源码: [Veblen/Fixpoint/Lower.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/Veblen/Fixpoint/Lower.lagda.md)  
> 高亮渲染: [Veblen.Fixpoint.Lower.html](https://choukh.github.io/agda-lvo/Veblen.Fixpoint.Lower.html)  
> 如果你在知乎看到本文: 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

本章是关于不动点的一些平凡的例子, 与主线无关, 可以跳过.

```agda
{-# OPTIONS --without-K --safe --experimental-lossy-unification #-}
```

## 前置

```agda
open import Ordinal
open Ordinal.≤-Reasoning
open import Ordinal.WellFormed
open import Ordinal.Function
open import Ordinal.Recursion
open import Ordinal.Arithmetic
open import Veblen.Fixpoint

open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
```

本章的所有内容都是参数化到某序数 `ξ` 上的.

```agda
module Veblen.Fixpoint.Lower (ξ : Ord) where
```

## 加法不动点

我们知道 `+_` 是序数嵌入, 因此存在 `+_` 的不动点, 第 `α` 个这样的不动点记作 `σ α`.

```agda
σ : Ord → Ord
σ = (ξ +_) ′

σ-fp : ∀ α → (σ α) isFixpointOf (ξ +_)
σ-fp α = ′-fp (+-normal ξ) α
```

`+_` 的最小不动点可以表示为序数乘法. 非形式地, `σ ⌜ 0 ⌝` ≈ $... + ξ + ξ$ ≈ $ξ * ω$.

```agda
σ₀ : σ ⌜ 0 ⌝ ≈ ξ * ω
σ₀ = l≈l helper where
  helper : ∀ {n} → rec _+_ ξ from ⌜ 0 ⌝ by ⌜ n ⌝ ≈ ξ * ⌜ n ⌝
  helper {zero}  = ≈-refl
  helper {suc n} =                      begin-equality
    ξ + (rec _+_ ξ from ⌜ 0 ⌝ by ⌜ n ⌝) ≈⟨ +-congˡ helper ⟩
    ξ + ξ * ⌜ n ⌝                       ≈⟨ +-assoc-n ξ n ⟩
    ξ * ⌜ n ⌝ + ξ                       ≡⟨⟩
    ξ * suc ⌜ n ⌝                       ∎
```

`σ α` 的下一个不动点就是 `σ α` 的后继.

```agda
σₛ : ∀ α → σ (suc α) ≈ suc (σ α)
σₛ α = l≤ helper , <⇒s≤ (<-mono <s) where
  helper : ∀ n → rec _+_ ξ from suc (σ α) by ⌜ n ⌝ ≤ suc (σ α)
  helper zero    = ≤-refl
  helper (suc n) =                           begin
    ξ + (rec _+_ ξ from suc (σ α) by ⌜ n ⌝)  ≤⟨ +-monoʳ-≤ ξ (helper n) ⟩
    ξ + suc (σ α)                            ≡⟨⟩
    suc (ξ + σ α)                            ≤⟨ s≤s (proj₁ (σ-fp α)) ⟩
    suc (σ α)                                ∎
  <-mono = proj₁ (proj₂ (′-normal (+-normal ξ)))
```

于是 `σ` 可以完全用序数算术表示.

```agda
σ≈ : ∀ α → σ α ≈ ξ * ω + α
σ≈ zero    = σ₀
σ≈ (suc α) =      begin-equality
  σ (suc α)       ≈⟨ σₛ α ⟩
  suc (σ α)       ≈⟨ s≈s (σ≈ α) ⟩
  suc (ξ * ω + α) ≡⟨⟩
  ξ * ω + suc α   ∎
σ≈ (lim f) = l≈l (σ≈ _)
```

## 乘法不动点

同样地, 由于 `*_` 是序数嵌入, 因此存在 `*_` 的不动点, 我们记作 `π`. 与加法不动点不同的是 `ξ` 要求大于 1, 不然每个序数都是平凡的不动点.

```agda
module _ (ξ>1 : ξ > ⌜ 1 ⌝) where

  π : Ord → Ord
  π = (ξ *_) ′

  π-fp : ∀ α → (π α) isFixpointOf (ξ *_)
  π-fp α = ′-fp (*-normal ξ (<-trans <s ξ>1)) α
```

乘法的最小不动点是平凡的零.

```agda
  π₀ : π ⌜ 0 ⌝ ≈ ⌜ 0 ⌝
  π₀ = l≤ helper , z≤ where
    helper : ∀ n → rec _*_ ξ from ⌜ 0 ⌝ by ⌜ n ⌝ ≤ ⌜ 0 ⌝
    helper zero    = ≤-refl
    helper (suc n) =                      begin
      ξ * (rec _*_ ξ from ⌜ 0 ⌝ by ⌜ n ⌝) ≤⟨ *-monoʳ-≤ ξ (helper n) ⟩
      ξ * ⌜ 0 ⌝                           ≡⟨⟩
      ⌜ 0 ⌝                               ∎
```

因此我们还要额外考察 `π ⌜ 1 ⌝`.

## 幂运算不动点

同样地, 由于 `^_` 是序数嵌入, 因此存在 `^_` 的不动点, 它就是著名的ε数, 我们将在下一章介绍. 与 `σ` 和 `π` 不同的是 ε 不存在算术表示, 因此它更具意义.
