---
title: Agda大序数(7*) 低阶不动点
zhihu-tags: Agda, 序数, 大数数学
zhihu-url: https://zhuanlan.zhihu.com/p/582065361
---

# Agda大序数(7*) 低阶不动点

> 交流Q群: 893531731  
> 目录: [NonWellFormed.html](https://choukh.github.io/agda-lvo/NonWellFormed.html)  
> 本文源码: [Fixpoint/Lower.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/NonWellFormed/Fixpoint/Lower.lagda.md)  
> 高亮渲染: [Fixpoint.Lower.html](https://choukh.github.io/agda-lvo/NonWellFormed.Fixpoint.Lower.html)  

本章是关于不动点的一些平凡的例子, 与主线无关, 可以跳过.

```agda
{-# OPTIONS --without-K --safe --experimental-lossy-unification #-}
```

## 前置

```agda
open import NonWellFormed.Ordinal
open NonWellFormed.Ordinal.≤-Reasoning
open import NonWellFormed.WellFormed
open import NonWellFormed.Function
open import NonWellFormed.Recursion
open import NonWellFormed.Arithmetic
open import NonWellFormed.Fixpoint

open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
```

本章的所有内容都是参数化到某序数 `ξ` 上的.

```agda
module NonWellFormed.Fixpoint.Lower {ξ : Ord} where
```

## 加法不动点

我们知道 `+_` 是序数嵌入, 因此存在 `+_` 的不动点, 我们记作 `σ`.

```agda
σ : Ord → Ord
σ = (ξ +_) ′

σ-fp : ∀ α → (σ α) isFixpointOf (ξ +_)
σ-fp α = ′-fp (+-normal ξ) α
```

`+_` 的最小不动点可以表示为序数乘法. 非形式地, `σ zero` ≈ $... + ξ + ξ$ ≈ $ξ * ω$.

```agda
σ₀ : σ zero ≈ ξ * ω
σ₀ = l≈l helper where
  helper : ∀ {n} → rec _+_ ξ from zero by ⌜ n ⌝ ≈ ξ * ⌜ n ⌝
  helper {zero}  = ≈-refl
  helper {suc n} =                        begin-equality
    ξ + (rec (ξ +_) from zero by ⌜ n ⌝)   ≈⟨ +-congˡ helper ⟩
    ξ + ξ * ⌜ n ⌝                         ≈⟨ +-assoc-n ξ n ⟩
    ξ * ⌜ n ⌝ + ξ                         ≡⟨⟩
    ξ * suc ⌜ n ⌝                         ∎
```

`σ α` 的下一个不动点就是 `σ α` 的后继.

```agda
σ⋱ₛ : ∀ α → σ (suc α) ≈ suc (σ α)
σ⋱ₛ α = l≤ helper , <⇒s≤ (<-mono <s) where
  helper : ∀ n → rec (ξ +_) from suc (σ α) by ⌜ n ⌝ ≤ suc (σ α)
  helper zero    = ≤-refl
  helper (suc n) =                           begin
    ξ + (rec (ξ +_) from suc (σ α) by ⌜ n ⌝) ≤⟨ +-monoʳ-≤ ξ (helper n) ⟩
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
  σ (suc α)       ≈⟨ σ⋱ₛ α ⟩
  suc (σ α)       ≈⟨ s≈s (σ≈ α) ⟩
  suc (ξ * ω + α) ≡⟨⟩
  ξ * ω + suc α   ∎
σ≈ (lim f) = l≈l (σ≈ _)
```

## 乘法不动点

与加法不动点不同的是乘法要求 `ξ` 大于 1, 不然每个序数都是平凡的不动点.

```agda
module _ ⦃ ξ>1 : ξ > ⌜ 1 ⌝ ⦄ where

  instance
    ξ>0 : ξ > zero
    ξ>0 = <-trans <s ξ>1

    ξ≥1 : ξ ≥ ⌜ 1 ⌝
    ξ≥1 = <⇒≤ ξ>1

  ξ*-normal : normal (ξ *_)
  ξ*-normal = *-normal ξ
```

由于 `*_` 是序数嵌入, 因此存在 `*_` 的不动点, 我们记作 `π`.

```agda
  π : Ord → Ord
  π = (ξ *_) ′

  π-fp : ∀ α → (π α) isFixpointOf (ξ *_)
  π-fp α = ′-fp ξ*-normal α
```

此外, 由序数算术定律, 可以证明 `ξ ^ ω` 也是 `ξ *_` 的不动点.

```agda
  ξ^ω-fp : (ξ ^ ω) isFixpointOf (ξ *_)
  ξ^ω-fp =                    begin-equality
    lim (λ n → ξ * ξ ^ ⌜ n ⌝) ≈⟨ l≈l (*-assoc-n ξ _) ⟩
    lim (λ n → ξ ^ ⌜ suc n ⌝) ≈˘⟨ l≈ls (^-monoʳ-≤ ξ ≤s) ⟩
    lim (λ n → ξ ^ ⌜ n ⌝)     ∎
```

我们接下来将建立 `π` 与 `ξ ^ ω` 的联系. 首先, 乘法的最小不动点是平凡的零.

```agda
  π₀ : π zero ≈ zero
  π₀ = l≤ helper , z≤ where
    helper : ∀ n → rec _*_ ξ from zero by ⌜ n ⌝ ≤ zero
    helper zero    = ≤-refl
    helper (suc n) =                     begin
      ξ * (rec _*_ ξ from zero by ⌜ n ⌝) ≤⟨ *-monoʳ-≤ ξ (helper n) ⟩
      ξ * zero                           ≡⟨⟩
      zero                               ∎
```

因此我们还要额外考察 `π ⌜ 1 ⌝`.

```agda
  π₁ : π ⌜ 1 ⌝ ≈ ξ ^ ω
  π₁ = ⋱ₛ-suc ξ*-normal _ _ π₀<ξ^ω ξ^ω-fp , l≤ ξ^n≤π₁ where
    π₀<ξ^ω =              begin-strict
      π zero              ≈⟨ π₀ ⟩
      zero                <⟨ <s ⟩
      ξ ^ zero            ≤⟨ f≤l {n = 0} ⟩
      ξ ^ ω               ∎
    ξ^n≤π₁ : ∀ n → ξ ^ ⌜ n ⌝ ≤ π ⌜ 1 ⌝
    ξ^n≤π₁ zero    =      begin
      ⌜ 1 ⌝               ≤⟨ s≤s (proj₂ π₀) ⟩
      suc ((ξ *_) ⋱ zero) ≤⟨ f≤l {n = 0} ⟩
      π ⌜ 1 ⌝             ∎
    ξ^n≤π₁ (suc n) =      begin
      ξ ^ suc ⌜ n ⌝       ≡⟨⟩
      ξ ^ ⌜ n ⌝ * ξ       ≈˘⟨ *-assoc-n ξ n ⟩
      ξ * ξ ^ ⌜ n ⌝       ≤⟨ *-monoʳ-≤ ξ (ξ^n≤π₁ n) ⟩
      ξ * π ⌜ 1 ⌝         ≈⟨ π-fp ⌜ 1 ⌝ ⟩
      π ⌜ 1 ⌝             ∎
```

然后, `π α` 的下一个不动点是 `π α` 与 `π ⌜ 1 ⌝` 的和.

```agda
  π⋱ₛ : ∀ α → π (suc α) ≈ π α + ξ ^ ω
  π⋱ₛ α = ⋱ₛ-suc ξ*-normal _ _ πα<πα+ξ^ω πα+ξ^ω-fp , l≤ helper where
    πα<πα+ξ^ω = +-incrʳ-< _ ^>0 _
    πα+ξ^ω-fp =               begin-equality
      ξ * (π α + ξ ^ ω)       ≈⟨ *-distribˡ-+ ξ _ _ ⟩
      ξ * π α + ξ * ξ ^ ω     ≈⟨ +-congˡ ξ^ω-fp ⟩
      ξ * π α + ξ ^ ω         ≈⟨ +-congʳ {ξ ^ ω} (π-fp α) ⟩
      π α + ξ ^ ω             ∎
    helper : ∀ n → π α + ξ ^ ⌜ n ⌝ ≤ π (suc α)
    helper zero =             begin
      π α + ξ ^ zero          ≈⟨ +-congˡ {π α} ≈-refl ⟩
      suc (π α)               ≤⟨ <⇒s≤ (<-mono <s) ⟩
      π (suc α)               ∎
      where <-mono = proj₁ (proj₂ (′-normal ξ*-normal))
    helper (suc n) =          begin
      π α + ξ ^ ⌜ suc n ⌝     ≈˘⟨ +-congˡ (*-assoc-n ξ n) ⟩
      π α + ξ * ξ ^ ⌜ n ⌝     ≈˘⟨ +-congʳ (π-fp α) ⟩
      ξ * π α + ξ * ξ ^ ⌜ n ⌝ ≈˘⟨ *-distribˡ-+ ξ _ _ ⟩
      ξ * (π α + ξ ^ ⌜ n ⌝)   ≤⟨ *-monoʳ-≤ ξ (helper n) ⟩
      ξ * π (suc α)           ≈⟨ π-fp (suc α) ⟩
      π (suc α)               ∎
```

于是 `π` 也可以用序数算术表示.

```agda
  π≈ : ∀ α → π α ≈ ξ ^ ω * α
  π≈ zero    = π₀
  π≈ (suc α) =        begin-equality
    π (suc α)         ≈⟨ π⋱ₛ α ⟩
    π α + ξ ^ ω       ≈⟨ +-congʳ {ξ ^ ω} (π≈ α) ⟩
    ξ ^ ω * α + ξ ^ ω ≡⟨⟩
    ξ ^ ω * suc α     ∎
  π≈ (lim x) = l≈l (π≈ _)
```

## 幂运算不动点

同样地, 由于 `^_` 是序数嵌入, 因此存在 `^_` 的不动点, 它就是著名的 ε 数, 我们将在下一章介绍. 与 `σ` 和 `π` 不同的是 ε 不存在自下而上的算术表示, 因此它更具意义.
