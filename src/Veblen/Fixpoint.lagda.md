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
{-# OPTIONS --no-qualified-instances #-}

module Veblen.Fixpoint where
```

## 前置

本章考察序数嵌入的不动点, 需要开头四章作为前置.

```agda
open import Ordinal
open Ordinal.≤-Reasoning
open import Ordinal.WellFormed hiding (wf⇒wf)
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
open import Function using (_∘_; λ-)
open import Relation.Binary.PropositionalEquality as Eq using (refl)
```

## 定义

我们说序数 `α` 是序数函数 `F` 的不动点, 当且仅当 `F α ≈ α`.

```agda
_isFixpointOf_ : Ord → (Ord → Ord) → Set
α isFixpointOf F = F α ≈ α
```

我们说 `rec F from α by ω` 是 `F` 从 `α` 开始的**无穷迭代**, 记作 `F ⋱ α`.

```agda
_⋱_ : (Ord → Ord) → (Ord → Ord)
F ⋱ α = rec F from α by ω
```

由超限递归的相关引理立即可知无穷迭代保持函数的弱增长性和 ≤-单调性.

```agda
module _ {F : Ord → Ord} where

  ⋱-incr-≤ : ≤-increasing F → ≤-increasing (F ⋱_)
  ⋱-incr-≤ ≤-incr = rec-from-incr-≤ ω ≤-incr

  ⋱-mono-≤ : ≤-monotonic F → ≤-monotonic (F ⋱_)
  ⋱-mono-≤ ≤-mono = rec-from-mono-≤ ω ≤-mono
```

我们说 `F ∘ suc` 的从 `F zero` 开始的递归是 `F` 的**后继迭代**, 记作 `F ⁺`

```agda
_⁺ : (Ord → Ord) → (Ord → Ord)
F ⁺ = rec F ∘ suc from (F zero) by_
```

后继迭代具有良好的性质, 只要 `F` ≤-单调且弱增长, `F ⁺` 就是序数嵌入.

```agda
⁺-normal : ∀ F → ≤-monotonic F → ≤-increasing F → normal (F ⁺)
⁺-normal F F-mono-≤ F-incr-≤ =
    rec-by-mono-≤ Fs-mono-≤ (<⇒≤-incr Fs-incr-<)
  , rec-by-mono-< Fs-mono-≤ Fs-incr-<
  , λ- ≈-refl where
    Fs-mono-≤ : ≤-monotonic (F ∘ suc)
    Fs-mono-≤ ≤ = F-mono-≤ (s≤s ≤)
    Fs-incr-< : <-increasing (F ∘ suc)
    Fs-incr-< α = s≤⇒< (F-incr-≤ (suc α))
```

我们说 `F ⋱_ ∘ suc` 的从 `F ⋱ zero` 开始的递归是 `F` 的不动点枚举函数, 记作 `F ′`.

```agda
_′ : (Ord → Ord) → Ord → Ord
F ′ = F ⋱_ ⁺
```

我们接下来解释该定义的合理性.

## 不动点

给定一个序数嵌入 `F`.

```agda
module _ {F : Ord → Ord} (nml@(≤-mono , <-mono , lim-ct) : normal F) where
  private ≤-incr = normal⇒≤-incr nml
```

**引理** `F` 的从任意初始值开始的无穷递归都是 `F` 的不动点.

```agda
  ⋱-fp : ∀ α₀ → (F ⋱ α₀) isFixpointOf F
  ⋱-fp α₀ =                                begin-equality
    F (F ⋱ α₀)                             ≈⟨ lim-ct _ ⟩
    lim (λ n → F (rec F from α₀ by ⌜ n ⌝)) ≈˘⟨ l≈ls (≤-incr α₀) ⟩
    F ⋱ α₀                                 ∎
```

**注意** 存在 `F` 的任意大的不动点.

```agda
  _ : ≤-increasing (F ⋱_)
  _ = ⋱-incr-≤ ≤-incr
```

## 最小不动点

**引理** `F` 的从零开始的无穷递归 `F ⋱ zero` 是 `F` 的最小不动点.

```agda
  ⋱₀-fp : (F ⋱ zero) isFixpointOf F
  ⋱₀-fp = ⋱-fp zero

  ⋱₀-min : ∀ {α} → α isFixpointOf F → F ⋱ zero ≤ α
  ⋱₀-min {α} fp = l≤ helper where
    helper : ∀ n → (rec F from zero by ⌜ n ⌝) ≤ α
    helper zero    = z≤
    helper (suc n) =               begin
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
    ⋱₀-monoSeq : MonoSequence (rec F from zero by_ ∘ ⌜_⌝)
    ⋱₀-monoSeq = wrap mono where
      mono : monoSequence _
      mono {m} {suc n} (ℕ.s≤s m≤n) with m≤n⇒m<n∨m≡n m≤n
      ... | inj₁ m<n =                begin-strict
        rec F from zero by ⌜ m ⌝      <⟨ mono m<n ⟩
        rec F from zero by ⌜ n ⌝      ≤⟨ ≤-incr _ ⟩
        rec F from zero by ⌜ suc n ⌝  ∎
      ... | inj₂ refl = helper m where
        helper : ∀ m → rec F from zero by ⌜ m ⌝ < rec F from zero by ⌜ suc m ⌝
        helper zero    = z-incr
        helper (suc m) = <-mono (helper m)
```

**引理** 如果 `F` 保良构, 那么 `F ⋱ zero` 良构.

```agda
    ⋱₀-wf : wf-preserving F → WellFormed (F ⋱ zero)
    ⋱₀-wf wfp = helper , ⋱₀-monoSeq where
      helper : ∀ {n} → WellFormed (rec F from zero by ⌜ n ⌝)
      helper {zero}  = tt
      helper {suc n} = wfp helper
```

**事实** 如果 `F` 还在良构后继处增长, 那么 `F` 的最小不动点严格大于 `F` 在有限序数处的值.

```agda
    Fn<F⋱₀ : suc-increasing F → ∀ n → F ⌜ n ⌝ < F ⋱ zero
    Fn<F⋱₀ s-incr n =                       begin-strict
      F ⌜ n ⌝                               <⟨ <-mono <s ⟩
      F ⌜ suc n ⌝                           ≤⟨ ≤-mono (helper n) ⟩
      rec F from zero by ⌜ suc (suc n) ⌝    ≤⟨ f≤l ⟩
      F ⋱ zero                              ∎ where
        helper : ∀ n → suc ⌜ n ⌝ ≤ F (rec F from zero by ⌜ n ⌝)
        helper zero    = <⇒s≤ z-incr
        helper (suc n) =                    begin
          ⌜ suc (suc n) ⌝                   ≤⟨ <⇒s≤ (s-incr ⌜ n ⌝ ⦃ ⌜ n ⌝-wellFormed ⦄) ⟩
          F ⌜ suc n ⌝                       ≤⟨ ≤-mono (helper n) ⟩
          F (F (rec F from zero by ⌜ n ⌝))  ∎
```

## 后继不动点

**引理** `F` 的从 `suc α` 开始的无穷递归是 `F` 的大于 `α` 的最小不动点, 叫做 `F` 于 `α` 的后继不动点.

```agda
  ⋱ₛ-fp : ∀ α → (F ⋱ suc α) isFixpointOf F
  ⋱ₛ-fp α = ⋱-fp (suc α)

  ⋱ₛ-incr-< : <-increasing (F ⋱_ ∘ suc)
  ⋱ₛ-incr-< α = s≤⇒< (⋱-incr-≤ ≤-incr (suc α))

  ⋱ₛ-suc : ∀ α β → α < β → β isFixpointOf F → F ⋱ suc α ≤ β
  ⋱ₛ-suc α β α<β fp = l≤ helper where
    helper : ∀ n → rec F from suc α by ⌜ n ⌝ ≤ β
    helper zero    = <⇒s≤ α<β
    helper (suc n) =                  begin
        F (rec F from suc α by ⌜ n ⌝) ≤⟨ ≤-mono (helper n) ⟩
        F β                           ≈⟨ fp ⟩
        β                             ∎
```

**引理** `F ⋱_ ∘ suc` ≤-单调.

```agda
  ⋱ₛ-mono-≤ : ≤-monotonic (F ⋱_ ∘ suc)
  ⋱ₛ-mono-≤ α≤β = ⋱-mono-≤ ≤-mono (s≤s α≤β)
```

现在, 假设 `F` 在良构后继处增长.

```agda
  module _ (s-incr : suc-increasing F) where
```

**引理** `F` 的从 `suc α` 开始的有穷递归是递归次数的单调序列.

```agda
    ⋱ₛ-monoSeq : ∀ α → ⦃ WellFormed α ⦄ → MonoSequence (rec F from suc α by_ ∘ ⌜_⌝)
    ⋱ₛ-monoSeq α = wrap mono where
      mono : monoSequence _
      mono {m} {suc n} (ℕ.s≤s m≤n) with m≤n⇒m<n∨m≡n m≤n
      ... | inj₁ m<n =                 begin-strict
        rec F from suc α by ⌜ m ⌝      <⟨ mono m<n ⟩
        rec F from suc α by ⌜ n ⌝      ≤⟨ ≤-incr _ ⟩
        rec F from suc α by ⌜ suc n ⌝  ∎
      ... | inj₂ refl = helper m where
        helper : ∀ m → rec F from suc α by ⌜ m ⌝ < rec F from suc α by ⌜ suc m ⌝
        helper zero    = s-incr α
        helper (suc m) = <-mono (helper m)
```

**引理** 如果 `F` 保良构, 那么 `F ⋱_ ∘ suc` 也保良构.

```agda
    ⋱ₛ-wfp : wf-preserving F → wf-preserving (F ⋱_ ∘ suc)
    ⋱ₛ-wfp wfp {α} wfα = helper , ⋱ₛ-monoSeq α ⦃ wfα ⦄ where
      helper : ∀ {n} → WellFormed (rec F from suc α by ⌜ n ⌝)
      helper {zero}  = wfα
      helper {suc n} = wfp helper
```

## 不动点的枚举

**引理** `F ⋱_ ∘ suc` 的从 `F ⋱ zero` 开始的递归是 `F` 的不动点枚举函数.

```agda
  ′-fp : ∀ α → (F ′) α isFixpointOf F
  ′-fp zero    = ⋱₀-fp
  ′-fp (suc α) = ⋱ₛ-fp _
  ′-fp (lim f) =                begin-equality
    F ((F ′) (lim f))           ≈⟨ lim-ct _ ⟩
    lim (λ n → F ((F ′) (f n))) ≈⟨ l≈l (′-fp (f _)) ⟩
    (F ′) (lim f)               ∎
```

我们接下来证明高阶函数 `_′` 保持序数函数的一系列性质.

**定理** `_′` 保持序数嵌入.

```agda
  ′-normal : normal (F ′)
  ′-normal = ⁺-normal (F ⋱_) (⋱-mono-≤ ≤-mono) (⋱-incr-≤ ≤-incr)
```

**注意** 这意味着 `_′` 也可以一直迭代下去, 得到高阶不动点.

**定理** `_′` 保持保良构性.

```agda
  ′-wfp : zero-increasing F → suc-increasing F → wf-preserving F → wf-preserving (F ′)
  ′-wfp z-incr s-incr wfp = rec-wfp (⋱₀-wf z-incr wfp) ⋱ₛ-mono-≤ ⋱ₛ-incr-< (⋱ₛ-wfp s-incr wfp)
```

**定理** `_′` 保持零处增长性.

```agda
module _ {F} where
  ′-zero-incr : zero-increasing F → zero-increasing (F ′)
  ′-zero-incr z-incr = <f⇒<l {n = 1} z-incr
```

**定理** `_′` 保持良构后继处增长性.

```agda
  ′-suc-incr : normal F → suc-increasing F → suc-increasing (F ′)
  ′-suc-incr nml s-incr α =           begin-strict
    suc α                             <⟨ s-incr α ⟩
    rec F from suc α by ⌜ 1 ⌝         ≤⟨ f≤l ⟩
    F ⋱ suc α                         ≤⟨ ⋱ₛ-mono-≤ nml (rec-by-incr-≤ (⋱ₛ-mono-≤ nml) (⋱ₛ-incr-< nml) α) ⟩
    (F ′) (suc α)                     ∎
```

## 高阶性质

`_⁺` 和 `_′` 也具有与增长性, 单调性, 合同性类似的性质, 只不过是高阶的.

**定理** `_′` 满足高阶增长性.

```agda
module _ {F} (nml@(≤-mono , _ , _) : normal F) where
  ′-incrʰ-≤ : ∀ α → F α ≤ (F ′) α
  ′-incrʰ-≤ α =  begin
    F α          ≤⟨ ≤-mono (normal⇒≤-incr (′-normal nml) α) ⟩
    F ((F ′) α)  ≈⟨ ′-fp nml α ⟩
    (F ′) α      ∎
```

**引理** `_⁺` 满足高阶单调性.

```agda
module _ {F G} (≤-mono : ≤-monotonic F) where
  ⁺-monoʰ-≤ : (∀ {α} → F α ≤ G α) → (∀ {α} → (F ⁺) α ≤ (G ⁺) α)
  ⁺-monoʰ-≤ F≤G {zero}  = F≤G {zero}
  ⁺-monoʰ-≤ F≤G {suc α} =         begin
    F (suc ((F ⁺) α))             ≤⟨ ≤-mono (s≤s (⁺-monoʰ-≤ F≤G)) ⟩
    F (suc ((G ⁺) α))             ≤⟨ F≤G ⟩
    G (suc ((G ⁺) α))             ∎
  ⁺-monoʰ-≤ F≤G {lim f} =         begin
    lim (λ n → (F ⁺) (f n))       ≤⟨ l≤l (λ n → ⁺-monoʰ-≤ F≤G) ⟩
    lim (λ n → (G ⁺) (f n))       ∎
```

**引理** `_′` 满足高阶单调性.

```agda
module _ {F G} (≤-mono : ≤-monotonic F) where
  ′-monoʰ-≤ : (∀ {α} → F α ≤ G α) → (∀ {α} → (F ′) α ≤ (G ′) α)
  ′-monoʰ-≤ F≤G = ⁺-monoʰ-≤ (⋱-mono-≤ ≤-mono) (l≤l ≤) where
    ≤ : ∀ {α} n → rec F from α by ⌜ n ⌝ ≤ rec G from α by ⌜ n ⌝
    ≤ zero = ≤-refl
    ≤ {α} (suc n) =             begin
      F (rec F from α by ⌜ n ⌝) ≤⟨ ≤-mono (≤ n) ⟩
      F (rec G from α by ⌜ n ⌝) ≤⟨ F≤G ⟩
      G (rec G from α by ⌜ n ⌝) ∎
```

**定理** `_⁺` 和 `_′` 满足高阶合同性, 即保持函数外延 `≈ᶠ`.

```agda
module _ {F G} (F-mono : ≤-monotonic F) (G-mono : ≤-monotonic G) where

  ⁺-congʰ : F ≈ᶠ G → (F ⁺) ≈ᶠ (G ⁺)
  ⁺-congʰ F≈ᶠG = ⁺-monoʰ-≤ F-mono (proj₁ F≈ᶠG)
               , ⁺-monoʰ-≤ G-mono (proj₂ F≈ᶠG)

  ′-congʰ : F ≈ᶠ G → (F ′) ≈ᶠ (G ′)
  ′-congʰ F≈ᶠG = ′-monoʰ-≤ F-mono (proj₁ F≈ᶠG)
               , ′-monoʰ-≤ G-mono (proj₂ F≈ᶠG)
```
