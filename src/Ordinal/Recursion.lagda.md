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
> 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

```agda
{-# OPTIONS --without-K --safe #-}

module Ordinal.Recursion where
```

本章在内容上延续前三章.

```agda
open import Ordinal
open import Ordinal.WellFormed using (wellFormed)
open import Ordinal.Function

open import Data.Nat as ℕ using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
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
rec-from-≤-enlg : ∀ α → ≤-enlarging F → ≤-enlarging (rec F from_by α)
rec-from-≤-enlg zero    ≤-enlg α₀ = ≤-refl
rec-from-≤-enlg (suc α) ≤-enlg α₀ = ≤-trans
  (rec-from-≤-enlg α ≤-enlg α₀)     -- α₀ ≤ rec F from α₀ by α
  (≤-enlg _)                        -- rec F from α₀ by α ≤ F (rec F from α₀ by α)
rec-from-≤-enlg (lim f) ≤-enlg α₀ = ≤-trans
  (rec-from-≤-enlg (f 0) ≤-enlg α₀) -- α₀ ≤ rec F from α₀ by f 0
  (≤→≤l ≤-refl)                     -- rec F from α₀ by f 0 ≤ lim λ n → rec F from α₀ by f n
```

**引理** 如果 `F` ≤-单调, 那么 `rec F from_by α` 也 ≤-单调.

```agda
rec-from-≤-mono : ∀ α → ≤-monotonic F → ≤-monotonic (rec F from_by α)
rec-from-≤-mono zero    _      ≤ = ≤
rec-from-≤-mono (suc γ) ≤-mono ≤ = ≤-mono
  (rec-from-≤-mono γ ≤-mono ≤)     -- rec F from α by γ ≤ rec F from β by γ
rec-from-≤-mono (lim f) ≤-mono ≤ = l≤ λ n → ≤→≤l
  (rec-from-≤-mono (f n) ≤-mono ≤) -- rec F from α by f n ≤ rec F from β by f n
```

### 固定初始值

现在我们考察固定初始值 `α₀` 的超限递归函数 `rec F from α₀ by_`.

**引理** 如果 `F` ≤-单调且强增长, 那么 `rec F from α₀ by_` 弱增长.  
**Remark** 即使 `F` 强增长, 我们也只能证明 `rec F from α₀ by_` 弱增长. 这里已经可以看出不动点的端倪了, 当递归达到一定次数的时候值可能就不再增长了.

```agda
rec-by-≤-enlg : ∀ {α₀} → ≤-monotonic F → <-enlarging F → ≤-enlarging (rec F from α₀ by_)
rec-by-≤-enlg ≤-mono <-enlg zero    = z≤
rec-by-≤-enlg ≤-mono <-enlg (suc α) = ≤-trans
  (s≤s (rec-by-≤-enlg ≤-mono <-enlg α)) -- suc α ≤ suc (rec F from α₀ by α)
  (<→s≤ (<-enlg _))                     -- suc (rec F from α₀ by α) ≤ F (rec F from α₀ by α)
rec-by-≤-enlg ≤-mono <-enlg (lim f) = l≤ λ n → ≤→≤l
  (rec-by-≤-enlg ≤-mono <-enlg (f n))   -- f n ≤ rec F from α₀ by f n
```

为了证明 `rec F from α₀ by_` 的单调性, 我们引入一个辅助概念, 叫做 **s∸单调**. 它可以看作 `F` 保持第一章的 [`s∸≤`](Ordinal.html#7532) 关系.

```agda
s∸-monotonic : (Ord → Ord) → Set
s∸-monotonic F = ∀ α d → F (suc (α ∸ d)) ≤ F α
```

**引理** 如果 `F` 弱增长, 那么 `rec F from α₀ by_` s∸单调.

```agda
rec-by-∸-mono : ∀ {α₀} → ≤-enlarging F → s∸-monotonic (rec F from α₀ by_)
rec-by-∸-mono ≤-enlg (suc α) (inj₁ tt) = ≤-refl
rec-by-∸-mono ≤-enlg (suc α) (inj₂ d)  = ≤-trans
  (rec-by-∸-mono ≤-enlg α d)     -- F (rec F from α₀ by (α ∸ d)) ≤ rec F from α₀ by α
  (≤-enlg _)                     -- rec F from α₀ by α ≤ F rec F from α₀ by α
rec-by-∸-mono ≤-enlg (lim f) (n , d)   = ≤-trans
  (rec-by-∸-mono ≤-enlg (f n) d) -- F (rec F from α₀ by (f n ∸ d)) ≤ rec F from α₀ by f n
  (≤→≤l ≤-refl)                  -- rec F from α₀ by f n ≤ lim λ n → rec F from α₀ by f n
```

**引理** 如果 `F` ≤-单调且弱增长, 那么 `rec F from α₀ by_` ≤-单调.

```agda
rec-by-≤-mono : ∀ {α₀} → ≤-monotonic F → ≤-enlarging F → ≤-monotonic (rec F from α₀ by_)
rec-by-≤-mono ≤-mono ≤-enlg {α} {β} z≤      = rec-from-≤-enlg β ≤-enlg _
rec-by-≤-mono ≤-mono ≤-enlg {α} {β} (s≤ ≤∸) = ≤-trans
  (≤-mono (rec-by-≤-mono ≤-mono ≤-enlg ≤∸)) -- F (rec F from α₀ by α) ≤ F (rec F from α₀ by (β ∸ d))
  (rec-by-∸-mono ≤-enlg β _)                -- F (rec F from α₀ by (β ∸ d)) ≤ rec F from α₀ by β
rec-by-≤-mono ≤-mono ≤-enlg {α} {β} (l≤ f≤) = l≤ λ n →
  rec-by-≤-mono ≤-mono ≤-enlg (f≤ n)        -- rec F from α₀ by f n ≤ rec F from α₀ by β
```

**引理** 如果 `F` ≤-单调且强增长, 那么 `rec F from α₀ by_` <-单调.

```agda
rec-by-<-mono : ∀ {α₀} → ≤-monotonic F → <-enlarging F → <-monotonic (rec F from α₀ by_)
rec-by-<-mono ≤-mono <-enlg {α} {suc β} <              = ≤-<-trans
  (rec-by-≤-mono ≤-mono (<⇒≤-enlg <-enlg) (<s→≤ <)) -- rec F from α₀ by α ≤ rec F from α₀ by β
  (<-enlg _)                                        -- rec F from α₀ by β < F (rec F from α₀ by β)
rec-by-<-mono ≤-mono <-enlg {α} {lim f} ((n , d) , ≤∸) = ≤-<-trans
  (rec-by-≤-mono ≤-mono (<⇒≤-enlg <-enlg) ≤∸)       -- rec F from α₀ by α ≤ rec F from α₀ by (f n ∸ d)
  (<-≤-trans (<-≤-trans
    (<-enlg _)                                      -- rec F from α₀ by (f n ∸ d) < F (rec F from α₀ by (f n ∸ d))
    (rec-by-∸-mono (<⇒≤-enlg <-enlg) (f n) d)       -- F (rec F from α₀ by (f n ∸ d)) ≤ rec F from α₀ by f n
  ) f≤l)                                            -- rec F from α₀ by f n ≤ lim λ n → rec F from α₀ by f n
```

## 本章结论

虽然超限递归对递归次数不能保证强增长, 但是对初始值能保证强增长.

**定理** 如果 `F` ≤-单调且强增长, 那么 `rec F from_by α` 也强增长, 只要 `α > zero`.

```agda
rec-from-<-enlg : ∀ {α} → α > zero → ≤-monotonic F
  → <-enlarging F → <-enlarging (rec F from_by α)
rec-from-<-enlg {α = suc α} _              ≤-mono <-enlg α₀ = ≤-<-trans
  (rec-from-≤-enlg α (<⇒≤-enlg <-enlg) α₀)    -- α₀ ≤ rec F from α₀ by α
  (rec-by-<-mono ≤-mono <-enlg {α} <s)        -- rec F from α₀ by α < F (rec F from α₀ by α)
rec-from-<-enlg {α = lim f} ((n , d) , ≤∸) ≤-mono <-enlg α₀ = <→<l
  (rec-from-<-enlg (d , ≤∸) ≤-mono <-enlg α₀) -- α₀ < rec F from α₀ by f n
```

**定理** 如果 `F` ≤-单调且强增长, 那么 `rec F from α₀ by_` 保良构, 只要初始值良构且 `F` 保良构.

```agda
rec-wf-preserving : ∀ {α₀} → wellFormed α₀ → ≤-monotonic F → <-enlarging F
  → wf-preserving F → wf-preserving (rec F from α₀ by_)
rec-wf-preserving wfα₀ ≤-mono <-enlg wf-p {zero}  wfα = wfα₀
rec-wf-preserving wfα₀ ≤-mono <-enlg wf-p {suc α} wfα = wf-p
  -- wellFormed (rec F from α₀ by α)
  (rec-wf-preserving wfα₀ ≤-mono <-enlg wf-p {α} wfα)
rec-wf-preserving wfα₀ ≤-mono <-enlg wf-p {lim f} wfα =
  -- wellFormed (rec F from α₀ by f n)
  ( λ {n} → rec-wf-preserving wfα₀ ≤-mono <-enlg wf-p {f n} (proj₁ wfα) )
  -- rec F from α₀ by f m < rec F from α₀ by f n
  , λ m<n → rec-by-<-mono ≤-mono <-enlg (proj₂ wfα m<n)
```
