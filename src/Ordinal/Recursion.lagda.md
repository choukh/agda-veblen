---
title: Agda大序数(4) 超限递归
zhihu-tags: Agda, 序数, 大数数学
zhihu-url: https://zhuanlan.zhihu.com/p/576854750
---

# Agda大序数(4) 超限递归

> 交流Q群: 893531731  
> 总目录: [Everything.html](https://choukh.github.io/agda-lvo/Everything.html)  
> 本文源码: [Ordinal/Recursion.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/Ordinal/Recursion.lagda.md)  
> 高亮渲染: [Ordinal.Recursion.html](https://choukh.github.io/agda-lvo/Ordinal.Recursion.html)  
> 如果你在知乎看到本文: 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

从本章开始, 我们会视情况打开 [*实验性有损合一化*](https://agda.readthedocs.io/en/v2.6.2.2/language/lossy-unification.html) 特性, 它可以减少显式标记隐式参数的需要, 而且跟 `--safe` 是兼容的. 当然它也有一些缺点, 具体这里不会展开.

```agda
{-# OPTIONS --without-K --safe --experimental-lossy-unification #-}

module Ordinal.Recursion where
```

## 前置

本章在内容上延续前三章.

```agda
open import Ordinal
open Ordinal.≤-Reasoning
open import Ordinal.WellFormed using (wellFormed)
open import Ordinal.Function
```

以下标准库依赖在前几章都出现过.

```agda
open import Data.Nat as ℕ using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; refl)
```

## 超限递归

我们定义超限递归函数 `rec F from α₀ by α` (读作递归 `F` 自 `α₀` 以 `α` 次) 如下.

- 若递归以零次, 其值就是初始值 `α₀`.
- 若递归以 `suc α` 次, 其值为 `F` 作用于 `α` 次的值.
- 若递归以 `lim f` 次, 其值为对 `f n` 次的值所组成的序列取极限.

```agda
rec_from_by_ : (Ord → Ord) → Ord → Ord → Ord
rec F from α₀ by zero  = α₀
rec F from α₀ by suc α = F (rec F from α₀ by α)
rec F from α₀ by lim f = lim λ n → rec F from α₀ by (f n)
```

现在给定一个序数函数 F.

```agda
private variable
  {F} : Ord → Ord
```

### 固定次数

如果固定递归的次数 `α`, 那么超限递归可以看作是一个高阶函数, 它将序数函数 F 转化成另一个序数函数 `rec F from_by α`, 它以初始值 `α₀` 为自变量.

**引理** 如果 `F` 弱增长 (非无穷降链), 那么 `rec F from_by α` 也弱增长.

```agda
rec-from-incr-≤ : ∀ α → ≤-increasing F → ≤-increasing (rec F from_by α)
rec-from-incr-≤     zero    ≤-incr α₀ = ≤-refl
rec-from-incr-≤ {F} (suc α) ≤-incr α₀ = begin
  α₀                                    ≤⟨ rec-from-incr-≤ α ≤-incr α₀ ⟩
  rec F from α₀ by α                    ≤⟨ ≤-incr _ ⟩
  rec F from α₀ by suc α                ∎
rec-from-incr-≤ {F} (lim f) ≤-incr α₀ = begin
  α₀                                    ≤⟨ rec-from-incr-≤ (f 0) ≤-incr α₀ ⟩
  rec F from α₀ by f 0                  ≤⟨ ≤f⇒≤l ≤-refl ⟩
  rec F from α₀ by lim f                ∎
```

**引理** 如果 `F` ≤-单调, 那么 `rec F from_by α` 也 ≤-单调.

```agda
rec-from-mono-≤ : ∀ α → ≤-monotonic F → ≤-monotonic (rec F from_by α)
rec-from-mono-≤ zero    _      ≤ = ≤
rec-from-mono-≤ (suc γ) ≤-mono ≤ = ≤-mono
  (rec-from-mono-≤ γ ≤-mono ≤)     -- rec F from α by γ ≤ rec F from β by γ
rec-from-mono-≤ (lim f) ≤-mono ≤ = l≤ λ n → ≤f⇒≤l
  (rec-from-mono-≤ (f n) ≤-mono ≤) -- rec F from α by f n ≤ rec F from β by f n
```

### 固定初始值

现在我们考察固定初始值 `α₀` 的超限递归函数 `rec F from α₀ by_`.

由定义立即可知 `rec F from α₀ by_` 极限连续.

```agda
rec-ct : ∀ {F α₀} → lim-continuous (rec F from α₀ by_)
rec-ct _ = ≈-refl
```

**引理** 如果 `F` ≤-单调且强增长, 那么 `rec F from α₀ by_` 弱增长.

```agda
rec-by-incr-≤ : ∀ {α₀} → ≤-monotonic F → <-increasing F → ≤-increasing (rec F from α₀ by_)
rec-by-incr-≤          ≤-mono <-incr zero    = z≤
rec-by-incr-≤ {F} {α₀} ≤-mono <-incr (suc α) = begin
  suc α                                        ≤⟨ s≤s (rec-by-incr-≤ ≤-mono <-incr α) ⟩
  suc (rec F from α₀ by α)                     ≤⟨ <⇒s≤ (<-incr _) ⟩
  rec F from α₀ by suc α                       ∎
rec-by-incr-≤          ≤-mono <-incr (lim f) = l≤ λ n → ≤f⇒≤l
  (rec-by-incr-≤ ≤-mono <-incr (f n))        -- f n ≤ rec F from α₀ by f n
```

**注意** 即使 `F` 强增长, 我们也只能证明 `rec F from α₀ by_` 弱增长. 这里已经可以看出不动点的端倪了, 当递归达到一定次数的时候值可能就不再增长了.

为了证明 `rec F from α₀ by_` 的单调性, 我们引入一个辅助概念, 叫做 **s∸单调**. 它可以看作 `F` 保持第一章的 [`s∸≤`](Ordinal.html#7626) 关系.

```agda
s∸-monotonic : (Ord → Ord) → Set
s∸-monotonic F = ∀ α d → F (suc (α ∸ d)) ≤ F α
```

**引理** 如果 `F` 弱增长, 那么 `rec F from α₀ by_` s∸单调.

```agda
rec-by-mono-s∸≤ : ∀ {α₀} → ≤-increasing F → s∸-monotonic (rec F from α₀ by_)
rec-by-mono-s∸≤          ≤-incr (suc α) (inj₁ tt) = ≤-refl
rec-by-mono-s∸≤ {F} {α₀} ≤-incr (suc α) (inj₂ d)  = begin
  rec F from α₀ by suc (α ∸ d)                      ≤⟨ rec-by-mono-s∸≤ ≤-incr α d ⟩
  rec F from α₀ by α                                ≤⟨ ≤-incr _ ⟩
  rec F from α₀ by suc α                            ∎
rec-by-mono-s∸≤ {F} {α₀} ≤-incr (lim f) (n , d)   = begin
  rec F from α₀ by suc (f n ∸ d)                    ≤⟨ rec-by-mono-s∸≤ ≤-incr (f n) d ⟩
  rec F from α₀ by f n                              ≤⟨ ≤f⇒≤l ≤-refl ⟩
  rec F from α₀ by lim f                            ∎
```

**引理** 如果 `F` ≤-单调且弱增长, 那么 `rec F from α₀ by_` ≤-单调.

```agda
rec-by-mono-≤ : ∀ {α₀} → ≤-monotonic F → ≤-increasing F → ≤-monotonic (rec F from α₀ by_)
rec-by-mono-≤          ≤-mono ≤-incr {α} {β} z≤      = rec-from-incr-≤ β ≤-incr _
rec-by-mono-≤ {F} {α₀} ≤-mono ≤-incr {α} {β} (s≤ ≤∸) = begin
  rec F from α₀ by α                                   ≤⟨ ≤-mono (rec-by-mono-≤ ≤-mono ≤-incr ≤∸) ⟩
  rec F from α₀ by suc (β ∸ _)                         ≤⟨ rec-by-mono-s∸≤ ≤-incr β _ ⟩
  rec F from α₀ by β                                   ∎
rec-by-mono-≤ {F} {α₀} ≤-mono ≤-incr {α} {β} (l≤ f≤) = l≤ λ n →
  rec-by-mono-≤ ≤-mono ≤-incr (f≤ n)                 -- rec F from α₀ by f n ≤ rec F from α₀ by β
```

**引理** 如果 `F` ≤-单调且强增长, 那么 `rec F from α₀ by_` <-单调.

```agda
rec-by-mono-< : ∀ {α₀} → ≤-monotonic F → <-increasing F → <-monotonic (rec F from α₀ by_)
rec-by-mono-< {F} {α₀} ≤-mono <-incr {α} {suc β} < = begin-strict
  rec F from α₀ by α              ≤⟨ rec-by-mono-≤ ≤-mono (<⇒≤-incr <-incr) (<s⇒≤ <) ⟩
  rec F from α₀ by β              <⟨ <-incr _ ⟩
  rec F from α₀ by suc β          ∎
rec-by-mono-< {F} {α₀} ≤-mono <-incr {α} {lim f} ((n , d) , ≤∸) = begin-strict
  rec F from α₀ by α              ≤⟨ rec-by-mono-≤ ≤-mono (<⇒≤-incr <-incr) ≤∸ ⟩
  rec F from α₀ by (f n ∸ d)      <⟨ <-incr _ ⟩
  rec F from α₀ by suc (f n ∸ d)  ≤⟨ rec-by-mono-s∸≤ (<⇒≤-incr <-incr) (f n) d ⟩
  rec F from α₀ by f n            ≤⟨ f≤l ⟩
  rec F from α₀ by lim f          ∎
```

## 本章结论

虽然超限递归对递归次数不能保证强增长, 但是对初始值能保证强增长.

**定理** 如果 `F` ≤-单调且强增长, 那么 `rec F from_by α` 也强增长, 只要 `α > zero`.

```agda
rec-from-incr-< : ∀ {α} → α > zero → ≤-monotonic F
  → <-increasing F → <-increasing (rec F from_by α)
rec-from-incr-< {F} {suc α} _ ≤-mono <-incr α₀ = begin-strict
  α₀                      ≤⟨ rec-from-incr-≤ α (<⇒≤-incr <-incr) α₀ ⟩
  rec F from α₀ by α      <⟨ rec-by-mono-< ≤-mono <-incr <s ⟩
  rec F from α₀ by suc α  ∎
rec-from-incr-< {F} {lim f} ((n , d) , ≤∸) ≤-mono <-incr α₀ = <f⇒<l
  (rec-from-incr-< (d , ≤∸) ≤-mono <-incr α₀) -- α₀ < rec F from α₀ by f n
```

**定理** 如果 `F` ≤-单调且强增长, 那么 `rec F from α₀ by_` 保良构, 只要初始值良构且 `F` 保良构.

```agda
rec-wfp : ∀ {α₀} → wellFormed α₀ → ≤-monotonic F → <-increasing F
  → wf-preserving F → wf-preserving (rec F from α₀ by_)
rec-wfp wfα₀ ≤-mono <-incr wf-p {zero}  wfα = wfα₀
rec-wfp wfα₀ ≤-mono <-incr wf-p {suc α} wfα = wf-p
  -- wellFormed (rec F from α₀ by α)
  (rec-wfp wfα₀ ≤-mono <-incr wf-p wfα)
rec-wfp wfα₀ ≤-mono <-incr wf-p {lim f} wfα =
  -- wellFormed (rec F from α₀ by f n)
  ( rec-wfp wfα₀ ≤-mono <-incr wf-p (proj₁ wfα) )
  -- rec F from α₀ by f m < rec F from α₀ by f n
  , λ m<n → rec-by-mono-< ≤-mono <-incr (proj₂ wfα m<n)
```
