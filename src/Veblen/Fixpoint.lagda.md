---
title: Agda大序数(7) 序数嵌入的不动点
zhihu-tags: Agda, 序数, 大数数学
zhihu-url: https://zhuanlan.zhihu.com/p/581675452
---

# Agda大序数(7) 序数嵌入的不动点

> 交流Q群: 893531731  
> 总目录: [Everything.html](https://choukh.github.io/agda-lvo/Everything.html)  
> 本文源码: [Veblen/Fixpoint.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/Veblen/Fixpoint.lagda.md)  
> 高亮渲染: [Veblen.Fixpoint.html](https://choukh.github.io/agda-lvo/Veblen.Fixpoint.html)  
> 如果你在知乎看到本文: 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

```agda
{-# OPTIONS --without-K --safe --experimental-lossy-unification #-}

module Veblen.Fixpoint where
```

## 前置

本章考察序数嵌入的不动点, 需要开头四章作为前置.

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
open import Data.Nat.Properties as ℕ using (m≤n⇒m<n∨m≡n)
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as Eq using (refl)
```

## 定义

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

我们先统一给出以下定义, 在下一小节再说明它们的合理性.

- 我们说 `F` 的从零开始的无穷递归是 `F` 的最小不动点, 记作 `F ₀`
- 我们说 `F` 的从 `suc α` 开始的无穷递归是 `F` 于 `α` 的后继不动点, 记作 `(F ₛ) α`
- 我们说 `F ₛ` 的从 `F ₀` 开始的递归是 `F` 的不动点枚举函数, 记作 `F ′`

```agda
_₀ : (Ord → Ord) → Ord
F ₀ = ω-rec F from zero

_ₛ : (Ord → Ord) → Ord → Ord
F ₛ = ω-rec F from_ ∘ suc

_′ : (Ord → Ord) → Ord → Ord
F ′ = rec (F ₛ) from (F ₀) by_
```

## 无穷递归

由超限递归的相关引理立即可知无穷递归保持函数的弱增长性和 ≤-单调性.

```agda
module _ {F : Ord → Ord} where

  ω-rec-pres-incr-≤ : ≤-increasing F → ≤-increasing (ω-rec F from_)
  ω-rec-pres-incr-≤ ≤-incr = rec-from-incr-≤ ω ≤-incr

  ω-rec-pres-mono-≤ : ≤-monotonic F → ≤-monotonic (ω-rec F from_)
  ω-rec-pres-mono-≤ ≤-mono = rec-from-mono-≤ ω ≤-mono
```

## 不动点

现在, 给定一个序数嵌入 `F`.

```agda
module _ {F : Ord → Ord} (nml@(≤-mono , <-mono , lim-ct) : normal F) where
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

**引理** `F` 的从零开始的无穷递归是 `F` 的最小不动点.

```agda
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

现在, 假设 `F` 在零处增长.

```agda
  module _ (z-incr : zero-increasing F) where
```

**引理** `F` 的从零开始的有穷递归是递归次数的单调序列.

```agda
    ₀-mono-n : monotonic (rec F from zero by_ ∘ ⌜_⌝)
    ₀-mono-n {m} {suc n} (ℕ.s≤s m≤n) with m≤n⇒m<n∨m≡n m≤n
    ... | inj₁ m<n =                begin-strict
      rec F from zero by ⌜ m ⌝      <⟨ ₀-mono-n m<n ⟩
      rec F from zero by ⌜ n ⌝      ≤⟨ normal⇒≤-incr nml _ ⟩
      rec F from zero by ⌜ suc n ⌝  ∎
    ... | inj₂ refl = helper m where
      helper : ∀ m → rec F from zero by ⌜ m ⌝ < rec F from zero by ⌜ suc m ⌝
      helper zero    = z-incr
      helper (suc m) = <-mono (helper m)
```

**引理** 如果 `F` 保良构, 那么 `F ₀` 良构.

```agda
    ₀-wf : wf-preserving F → wellFormed (F ₀)
    ₀-wf wfp = helper , ₀-mono-n where
      helper : ∀ {n} → wellFormed (rec F from zero by ⌜ n ⌝)
      helper {zero}  = tt
      helper {suc n} = wfp helper
```

**事实** 如果 `F` 还在良构后继处增长, 那么 `F` 的最小不动点严格大于 `F` 在有限序数处的值.

```agda
    ₀-transcendent : suc-increasing F → ∀ n → F ⌜ n ⌝ < F ₀
    ₀-transcendent s-incr n =             begin-strict
      F ⌜ n ⌝                             <⟨ <-mono <s ⟩
      F ⌜ suc n ⌝                         ≤⟨ ≤-mono (helper n) ⟩
      rec F from zero by ⌜ suc (suc n) ⌝  ≤⟨ f≤l ⟩
      F ₀                                 ∎ where
        helper : ∀ n → suc ⌜ n ⌝ ≤ F (rec F from zero by ⌜ n ⌝)
        helper zero    = <⇒s≤ z-incr
        helper (suc n) = begin
          ⌜ suc (suc n) ⌝                   ≤⟨ <⇒s≤ (s-incr ⌜ n ⌝-wellFormed) ⟩
          F ⌜ suc n ⌝                       ≤⟨ ≤-mono (helper n) ⟩
          F (F (rec F from zero by ⌜ n ⌝))  ∎
```

## 后继不动点

**引理** `F` 的从 `suc α` 开始的无穷递归是 `F` 的大于 `α` 的最小不动点, 叫做 `F` 于 `α` 的后继不动点.

```agda
  ₛ-fp : ∀ α → (F ₛ) α isFixpointOf F
  ₛ-fp α = ω-rec-fp (suc α)

  ₛ-incr-< : <-increasing (F ₛ)
  ₛ-incr-< α = s≤⇒< (ω-rec-incr-≤ (suc α))

  ₛ-suc : ∀ α β → α < β → β isFixpointOf F → (F ₛ) α ≤ β
  ₛ-suc α β α<β fp = l≤ helper where
    helper : ∀ n → rec F from suc α by ⌜ n ⌝ ≤ β
    helper zero = <⇒s≤ α<β
    helper (suc n)                  = begin
        F (rec F from suc α by ⌜ n ⌝) ≤⟨ ≤-mono (helper n) ⟩
        F β                           ≈⟨ fp ⟩
        β                             ∎
```

**引理** `F ₛ_` ≤-单调.

```agda
  ₛ-mono-≤ : ≤-monotonic (F ₛ)
  ₛ-mono-≤ α≤β = ω-rec-pres-mono-≤ ≤-mono (s≤s α≤β)
```

现在, 假设 `F` 在良构后继处增长.

```agda
  module _ (s-incr : suc-increasing F) where
```

**引理** `F` 的从 `suc α` 开始的有穷递归是递归次数的单调序列.

```agda
    ₛ-mono-n : ∀ {α} → wellFormed α → monotonic (rec F from suc α by_ ∘ ⌜_⌝)
    ₛ-mono-n {α} wfα {m} {suc n} (ℕ.s≤s m≤n) with m≤n⇒m<n∨m≡n m≤n
    ... | inj₁ m<n =                begin-strict
      rec F from suc α by ⌜ m ⌝      <⟨ ₛ-mono-n wfα m<n ⟩
      rec F from suc α by ⌜ n ⌝      ≤⟨ normal⇒≤-incr nml _ ⟩
      rec F from suc α by ⌜ suc n ⌝  ∎
    ... | inj₂ refl = helper m where
      helper : ∀ m → rec F from suc α by ⌜ m ⌝ < rec F from suc α by ⌜ suc m ⌝
      helper zero    = s-incr wfα
      helper (suc m) = <-mono (helper m)
```

**引理** `_ₛ_` 保持保良构性.

```agda
    ₛ-wfp : wf-preserving F → wf-preserving (F ₛ)
    ₛ-wfp wfp {α} wfα = helper , ₛ-mono-n wfα where
      helper : ∀ {n} → wellFormed (rec F from suc α by ⌜ n ⌝)
      helper {zero}  = wfα
      helper {suc n} = wfp helper
```

## 不动点的枚举

**引理** `F ₛ` 的从 `F ₀` 开始的递归是 `F` 的不动点枚举函数.

```agda
  ′-fp : ∀ α → (F ′) α isFixpointOf F
  ′-fp zero    = ₀-fp
  ′-fp (suc α) = ₛ-fp _
  ′-fp (lim f) =                begin-equality
    F ((F ′) (lim f))           ≈⟨ lim-ct _ ⟩
    lim (λ n → F ((F ′) (f n))) ≈⟨ l≈l (′-fp (f _)) ⟩
    (F ′) (lim f)               ∎
```

我们接下来证明高阶函数 `_′` 保持序数函数的一系列性质.

**定理** `_′` 保持序数嵌入.

```agda
  ′-normal : normal (F ′)
  ′-normal = rec-by-mono-≤ ₛ-mono-≤ (<⇒≤-incr ₛ-incr-<)
           , rec-by-mono-< ₛ-mono-≤ ₛ-incr-<
           , λ _ → ≈-refl
```

**注意** 这意味着 `_′` 也可以一直迭代下去, 得到高阶不动点.

**定理** `_′` 保持保良构性.

```agda
  ′-wfp : zero-increasing F → suc-increasing F → wf-preserving F → wf-preserving (F ′)
  ′-wfp z-incr s-incr wfp = rec-wfp (₀-wf z-incr wfp) ₛ-mono-≤ ₛ-incr-< (ₛ-wfp s-incr wfp)
```

**推论** `_′` 的迭代保持序数嵌入.

```agda
′′-normal : ∀ {F} → normal (F ′) → normal (F ′ ′)
′′-normal = ′-normal
```

**引理** `_′` 保持零处增长性.

```agda
′-zero-incr : ∀ {F} → zero-increasing F → zero-increasing (F ′)
′-zero-incr z-incr = <f⇒<l {n = 1} z-incr
```

**引理** `_′` 保持良构后继处增长性.

```agda
′-suc-incr : ∀ {F} → normal F → suc-increasing F → suc-increasing (F ′)
′-suc-incr {F} nml s-incr {α} wfα = begin-strict
  suc α                             <⟨ s-incr wfα ⟩
  rec F from suc α by ⌜ 1 ⌝         ≤⟨ f≤l ⟩
  (F ₛ) α                           ≤⟨ ₛ-mono-≤ nml (rec-by-incr-≤ (ₛ-mono-≤ nml) (ₛ-incr-< nml) α) ⟩
  (F ′) (suc α)                     ∎
```

**推论** `_′` 的迭代保持保良构性.

```agda
′′-wfp : ∀ F → normal F → zero-increasing F → suc-increasing F
  → wf-preserving (F ′) → wf-preserving (F ′ ′)
′′-wfp F nml z-incr s-incr = ′-wfp {F ′} (′-normal nml) (′-zero-incr z-incr) (′-suc-incr nml s-incr)
```

**定理** `_′` 保持函数外延 `≈ᶠ`.

```agda
′-pres-≈ᶠ : ∀ {F G} → normal F → normal G → F ≈ᶠ G → (F ′) ≈ᶠ (G ′)
′-pres-≈ᶠ {F} {G} nmlF nmlG F≈ᶠG {zero}  = l≈l helper where
  helper : ∀ {n} → rec F from zero by ⌜ n ⌝ ≈ rec G from zero by ⌜ n ⌝
  helper {zero}  = ≈-refl
  helper {suc n} = begin-equality
    F (rec F from zero by ⌜ n ⌝) ≈⟨ ≤-inc⇒cong (proj₁ nmlF) helper ⟩
    F (rec G from zero by ⌜ n ⌝) ≈⟨ F≈ᶠG ⟩
    G (rec G from zero by ⌜ n ⌝) ∎
′-pres-≈ᶠ {F} {G} nmlF nmlG F≈ᶠG {suc α} = l≈l helper where
  helper : ∀ {n} → rec F from suc ((F ′) α) by ⌜ n ⌝ ≈ rec G from suc ((G ′) α) by ⌜ n ⌝
  helper {zero}  = s≈s (′-pres-≈ᶠ nmlF nmlG F≈ᶠG)
  helper {suc n} = begin-equality
    F (rec F from suc ((F ′) α) by ⌜ n ⌝) ≈⟨ ≤-inc⇒cong (proj₁ nmlF) helper ⟩
    F (rec G from suc ((G ′) α) by ⌜ n ⌝) ≈⟨ F≈ᶠG ⟩
    G (rec G from suc ((G ′) α) by ⌜ n ⌝) ∎
′-pres-≈ᶠ {F} {G} nmlF nmlG F≈ᶠG {lim f} = l≈l (′-pres-≈ᶠ nmlF nmlG F≈ᶠG)
```
