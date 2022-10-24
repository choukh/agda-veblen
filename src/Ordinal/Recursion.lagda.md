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

**引理** 如果 `F` 弱放大 (非无穷降链), 那么 `rec F from_by α` 也弱放大.

```agda
rec-from-≤-enl : ∀ α → ≤-enlarging F → ≤-enlarging (rec F from_by α)
rec-from-≤-enl zero    ≤-enl α₀ = ≤-refl
rec-from-≤-enl (suc α) ≤-enl α₀ = ≤-trans
  (rec-from-≤-enl α ≤-enl α₀)     -- α₀ ≤ rec F from α₀ by α
  (≤-enl _)                       -- rec F from α₀ by α ≤ F (rec F from α₀ by α)
rec-from-≤-enl (lim f) ≤-enl α₀ = ≤-trans
  (rec-from-≤-enl (f 0) ≤-enl α₀) -- α₀ ≤ rec F from α₀ by f 0
  (≤→≤l ≤-refl)                   -- rec F from α₀ by f 0 ≤ lim λ n → rec F from α₀ by f n
```

**引理** 如果 `F` 弱递增, 那么 `rec F from_by α` 也弱递增.

```agda
rec-from-≤-inc : ∀ α → ≤-increasing F → ≤-increasing (rec F from_by α)
rec-from-≤-inc zero    _     ≤ = ≤
rec-from-≤-inc (suc γ) ≤-inc ≤ = ≤-inc
  (rec-from-≤-inc γ ≤-inc ≤)       -- rec F from α by γ ≤ rec F from β by γ
rec-from-≤-inc (lim f) ≤-inc ≤ = l≤ λ n → ≤→≤l
  (rec-from-≤-inc (f n) ≤-inc ≤)   -- rec F from α by f n ≤ rec F from β by f n
```

### 固定初始值

现在我们考察固定初始值 `α₀` 的超限递归函数 `rec F from α₀ by_`.

**引理** 如果 `F` 弱递增且强放大, 那么 `rec F from α₀ by_` 弱放大.  
**Remark** 即使 `F` 强放大, 我们也只能证明 `rec F from α₀ by_` 弱放大. 这里已经可以看出不动点的端倪了, 当递归达到一定次数的时候值可能就不再增长了.

```agda
rec-by-≤-enl : ∀ {α₀} → ≤-increasing F → <-enlarging F → ≤-enlarging (rec F from α₀ by_)
rec-by-≤-enl ≤-inc <-enl zero    = z≤
rec-by-≤-enl ≤-inc <-enl (suc α) = ≤-trans
  (s≤s (rec-by-≤-enl ≤-inc <-enl α)) -- suc α ≤ suc (rec F from α₀ by α)
  (<→s≤ (<-enl _))                   -- suc (rec F from α₀ by α) ≤ F (rec F from α₀ by α)
rec-by-≤-enl ≤-inc <-enl (lim f) = l≤ λ n → ≤→≤l
  (rec-by-≤-enl ≤-inc <-enl (f n))   -- f n ≤ rec F from α₀ by f n
```

为了证明 `rec F from α₀ by_` 的递增性, 我们引入一个辅助概念, 叫做 **s∸递增**. 它可以看作 `F` 保持第一章的 [`s∸≤`](Ordinal.html#7532) 关系.

```agda
s∸-increasing : (Ord → Ord) → Set
s∸-increasing F = ∀ α d → F (suc (α ∸ d)) ≤ F α
```

**引理** 如果 `F` 弱放大, 那么 `rec F from α₀ by_` s∸递增.

```agda
rec-by-∸-inc : ∀ {α₀} → ≤-enlarging F → s∸-increasing (rec F from α₀ by_)
rec-by-∸-inc ≤-enl (suc α) (inj₁ tt) = ≤-refl
rec-by-∸-inc ≤-enl (suc α) (inj₂ d)  = ≤-trans
  (rec-by-∸-inc ≤-enl α d)     -- F (rec F from α₀ by (α ∸ d)) ≤ rec F from α₀ by α
  (≤-enl _)                    -- rec F from α₀ by α ≤ F rec F from α₀ by α
rec-by-∸-inc ≤-enl (lim f) (n , d)   = ≤-trans
  (rec-by-∸-inc ≤-enl (f n) d) -- F (rec F from α₀ by (f n ∸ d)) ≤ rec F from α₀ by f n
  (≤→≤l ≤-refl)                -- rec F from α₀ by f n ≤ lim λ n → rec F from α₀ by f n
```

**引理** 如果 `F` 弱递增且弱放大, 那么 `rec F from α₀ by_` 弱递增.

```agda
rec-by-≤-inc : ∀ {α₀} → ≤-increasing F → ≤-enlarging F → ≤-increasing (rec F from α₀ by_)
rec-by-≤-inc ≤-inc ≤-enl {α} {β} z≤      = rec-from-≤-enl β ≤-enl _
rec-by-≤-inc ≤-inc ≤-enl {α} {β} (s≤ ≤∸) = ≤-trans
  (≤-inc (rec-by-≤-inc ≤-inc ≤-enl ≤∸)) -- F (rec F from α₀ by α) ≤ F (rec F from α₀ by (β ∸ d))
  (rec-by-∸-inc ≤-enl β _)              -- F (rec F from α₀ by (β ∸ d)) ≤ rec F from α₀ by β
rec-by-≤-inc ≤-inc ≤-enl {α} {β} (l≤ f≤) = l≤ λ n →
  rec-by-≤-inc ≤-inc ≤-enl (f≤ n)       -- rec F from α₀ by f n ≤ rec F from α₀ by β
```

**引理** 如果 `F` 弱递增且强放大, 那么 `rec F from α₀ by_` 强递增.

```agda
rec-by-<-inc : ∀ {α₀} → ≤-increasing F → <-enlarging F → <-increasing (rec F from α₀ by_)
rec-by-<-inc ≤-inc <-enl {α} {suc β} <             = ≤-<-trans
  (rec-by-≤-inc ≤-inc (<⇒≤-enl <-enl) (<s→≤ <)) -- rec F from α₀ by α ≤ rec F from α₀ by β
  (<-enl _)                                     -- rec F from α₀ by β < F (rec F from α₀ by β)
rec-by-<-inc ≤-inc <-enl {α} {lim f} ((n , d) , ≤∸) = ≤-<-trans
  (rec-by-≤-inc ≤-inc (<⇒≤-enl <-enl) ≤∸)       -- rec F from α₀ by α ≤ rec F from α₀ by (f n ∸ d)
  (<-≤-trans (<-≤-trans
    (<-enl _)                                   -- rec F from α₀ by (f n ∸ d) < F (rec F from α₀ by (f n ∸ d))
    (rec-by-∸-inc (<⇒≤-enl <-enl) (f n) d)      -- F (rec F from α₀ by (f n ∸ d)) ≤ rec F from α₀ by f n
  ) f≤l)                                        -- rec F from α₀ by f n ≤ lim λ n → rec F from α₀ by f n
```

## 本章结论

虽然超限递归对递归次数不能保证强放大, 但是对初始值能保证强放大.

**定理** 如果 `F` 弱递增且强放大, 那么 `rec F from_by α` 也强放大, 只要 `α > zero`.

```agda
rec-from-<-enl : ∀ {α} → α > zero → ≤-increasing F
  → <-enlarging F → <-enlarging (rec F from_by α)
rec-from-<-enl {α = suc α} _              ≤-inc <-enl α₀ = ≤-<-trans
  (rec-from-≤-enl α (<⇒≤-enl <-enl) α₀)    -- α₀ ≤ rec F from α₀ by α
  (rec-by-<-inc ≤-inc <-enl {α} <s)        -- rec F from α₀ by α < F (rec F from α₀ by α)
rec-from-<-enl {α = lim f} ((n , d) , ≤∸) ≤-inc <-enl α₀ = <→<l
  (rec-from-<-enl (d , ≤∸) ≤-inc <-enl α₀) -- α₀ < rec F from α₀ by f n
```

**定理** 如果 `F` 弱递增且强放大, 那么 `rec F from α₀ by_` 保良构, 只要初始值良构且 `F` 保良构.

```agda
rec-wf-preserving : ∀ {α₀} → wellFormed α₀ → ≤-increasing F → <-enlarging F
  → wf-preserving F → wf-preserving (rec F from α₀ by_)
rec-wf-preserving wfα₀ ≤-inc <-enl wf-p {zero}  wfα = wfα₀
rec-wf-preserving wfα₀ ≤-inc <-enl wf-p {suc α} wfα = wf-p
  -- wellFormed (rec F from α₀ by α)
  (rec-wf-preserving wfα₀ ≤-inc <-enl wf-p {α} wfα)
rec-wf-preserving wfα₀ ≤-inc <-enl wf-p {lim f} wfα =
  -- wellFormed (rec F from α₀ by f n)
  ( λ {n} → rec-wf-preserving wfα₀ ≤-inc <-enl wf-p {f n} (proj₁ wfα) )
  -- rec F from α₀ by f m < rec F from α₀ by f n
  , λ m<n → rec-by-<-inc ≤-inc <-enl (proj₂ wfα m<n)
```
