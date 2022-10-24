---
title: Agda大序数(4) 超限递归
zhihu-tags: Agda, 序数, 大数数学
---

# Agda大序数(4) 超限递归

> 交流Q群: 893531731  
> 总目录: [Everything.html](https://choukh.github.io/agda-lvo/Everything.html)  
> 本文源码: [Ordinal/Recursion.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/Ordinal/Recursion.lagda.md)  
> 高亮渲染: [Ordinal.Recursion.html](https://choukh.github.io/agda-lvo/Ordinal.Recursion.html)  
> 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

**(本章施工中)**

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

我们定义超限递归函数 `rec F from α₀ by α` (读作递归 `F` 自 `α₀` 以 `α` 次) 如下.

- 若递归以零次, 其值就是初始值 `α₀`.
- 若递归以 `suc α` 次, 其值为 `F` 作用于 `α` 次的值.
- 若递归以 `lim f` 次, 其值为对 `f n` 次的值所组成的序列取极限.

```agda
rec_from_by_ : (Ord → Ord) → Ord → Ord → Ord
rec F from α₀ by zero  = α₀
rec F from α₀ by suc α = F (rec F from α₀ by α)
rec F from α₀ by lim f = lim (λ n → rec F from α₀ by (f n))
```

现在给定一个序数函数 F.

```agda
private variable
  {F} : Ord → Ord
```

如果固定递归的次数 `α`, 那么超限递归可以看作是一个高阶函数, 它将序数函数 F 转化成另一个序数函数 `rec F from_by α`, 它以初始值 `α₀` 为自变量.

**引理** 如果 `F` 弱放大 (非无穷降链), 那么 `rec F from_by α` 也弱放大.

```agda
rec-from-≤-enl : ∀ α → ≤-enlarging F → ≤-enlarging (rec F from_by α)
rec-from-≤-enl zero    ≤-enl α₀ = ≤-refl
rec-from-≤-enl (suc α) ≤-enl α₀ = ≤-trans
  (rec-from-≤-enl α ≤-enl α₀)     {- α₀ ≤ rec F from α₀ by α -}
  (≤-enl _)                       {- rec F from α₀ by α ≤ F (rec F from α₀ by α) -}
rec-from-≤-enl (lim f) ≤-enl α₀ = ≤-trans
  (rec-from-≤-enl (f 0) ≤-enl α₀) {- α₀ ≤ rec F from α₀ by f 0 -}
  (≤→≤l ≤-refl)                   {- rec F from α₀ by f 0 ≤ lim (λ n → rec F from α₀ by f n) -}
```

**引理** 如果 `F` 弱递增, 那么 `rec F from_by α` 也弱递增.

```agda
rec-from-≤-inc : ∀ α → ≤-increasing F → ≤-increasing (rec F from_by α)
rec-from-≤-inc zero    _     ≤ = ≤
rec-from-≤-inc (suc γ) ≤-inc ≤ = ≤-inc (rec-from-≤-inc γ ≤-inc ≤)
rec-from-≤-inc (lim f) ≤-inc ≤ = l≤ (λ n → ≤→≤l (rec-from-≤-inc (f n) ≤-inc ≤))
```



```agda
rec-by-≤-enl : ∀ {α₀} → ≤-increasing F → <-enlarging F → ≤-enlarging (rec F from α₀ by_)
rec-by-≤-enl ≤-inc <-enl zero    = z≤
rec-by-≤-enl ≤-inc <-enl (suc α) = ≤-trans
  (s≤s (rec-by-≤-enl ≤-inc <-enl α))
  (<→s≤ (<-enl _))
rec-by-≤-enl ≤-inc <-enl (lim f) = l≤ (λ n → ≤→≤l (rec-by-≤-enl ≤-inc <-enl (f n)))
```

```agda
∸-increasing : (Ord → Ord) → Set
∸-increasing F = ∀ α d → F (suc (α ∸ d)) ≤ F α
```

```agda
rec-by-∸-inc : ∀ {α₀} → ≤-enlarging F → ∸-increasing (rec F from α₀ by_)
rec-by-∸-inc ≤-enl (suc α) (inj₁ tt) = ≤-refl
rec-by-∸-inc ≤-enl (suc α) (inj₂ d)  = ≤-trans (rec-by-∸-inc ≤-enl α d) (≤-enl _)
rec-by-∸-inc ≤-enl (lim f) (n , d)   = ≤-trans (rec-by-∸-inc ≤-enl (f n) d) (≤→≤l ≤-refl)
```

```agda
rec-by-≤-inc : ∀ {α₀} → ≤-increasing F → ≤-enlarging F → ≤-increasing (rec F from α₀ by_)
rec-by-≤-inc ≤-inc ≤-enl {α} {β} z≤      = rec-from-≤-enl β ≤-enl _
rec-by-≤-inc ≤-inc ≤-enl {α} {β} (s≤ ≤∸) = ≤-trans
  (≤-inc (rec-by-≤-inc ≤-inc ≤-enl ≤∸))
  (rec-by-∸-inc ≤-enl β _)
rec-by-≤-inc ≤-inc ≤-enl {α} {β} (l≤ f≤) = l≤ λ n → rec-by-≤-inc ≤-inc ≤-enl (f≤ n)
```

```agda
rec-by-<-inc : ∀ {α₀} → ≤-increasing F → <-enlarging F → <-increasing (rec F from α₀ by_)
rec-by-<-inc ≤-inc <-enl {α} {suc β} <             = ≤-<-trans
  (rec-by-≤-inc ≤-inc (<⇒≤-enl <-enl) (<s→≤ <))
  (<-enl _)
rec-by-<-inc ≤-inc <-enl {α} {lim f} ((n , d) , ≤∸) = ≤-<-trans
  (rec-by-≤-inc ≤-inc (<⇒≤-enl <-enl) ≤∸)
  (<-≤-trans (<-≤-trans (<-enl _) (rec-by-∸-inc (<⇒≤-enl <-enl) (f n) d)) f≤l)
```

```agda
rec-from-<-enl : ∀ {α} → α > zero → ≤-increasing F
  → <-enlarging F → <-enlarging (rec F from_by α)
rec-from-<-enl {α = suc α} _              ≤-inc <-enl α₀ = ≤-<-trans
  (rec-from-≤-enl α (<⇒≤-enl <-enl) α₀)
  (rec-by-<-inc ≤-inc <-enl {α} <s)
rec-from-<-enl {α = lim f} ((n , d) , ≤∸) ≤-inc <-enl α₀ = <→<l
  (rec-from-<-enl (d , ≤∸) ≤-inc <-enl α₀)
```

```agda
rec-wf-preserving : ∀ {α₀} → wellFormed α₀ → ≤-increasing F → <-enlarging F
  → wf-preserving F → wf-preserving (rec F from α₀ by_)
rec-wf-preserving wfα₀ ≤-inc <-enl wf-p {zero}  wfα = wfα₀
rec-wf-preserving wfα₀ ≤-inc <-enl wf-p {suc α} wfα = wf-p
  (rec-wf-preserving wfα₀ ≤-inc <-enl wf-p {α} wfα)
rec-wf-preserving wfα₀ ≤-inc <-enl wf-p {lim f} wfα =
  ( λ {n} → rec-wf-preserving wfα₀ ≤-inc <-enl wf-p {f n} (proj₁ wfα) )
  , λ m<n → rec-by-<-inc ≤-inc <-enl (proj₂ wfα m<n)
```
