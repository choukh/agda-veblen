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

```agda
{-# OPTIONS --without-K --safe #-}

module Ordinal.Recursion where
```

本章在内容上延续前三章.

```agda
open import Ordinal
open import Ordinal.WellFormed using (wellFormed)
open import Ordinal.Function
```

```agda
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
```

```agda
private variable
  {F} : Ord → Ord
```

```agda
rec_from_by_ : (Ord → Ord) → Ord → Ord → Ord
rec F from α₀ by zero  = α₀
rec F from α₀ by suc α = F (rec F from α₀ by α)
rec F from α₀ by lim f = lim (λ n → rec F from α₀ by (f n))
```

```agda
rec-from-≤-enl : ∀ α → ≤-enlarging F → ≤-enlarging (rec F from_by α)
rec-from-≤-enl zero    ≤-enl α₀ = ≤-refl
rec-from-≤-enl (suc α) ≤-enl α₀ = ≤-trans (rec-from-≤-enl α     ≤-enl α₀) (≤-enl _)
rec-from-≤-enl (lim f) ≤-enl α₀ = ≤-trans (rec-from-≤-enl (f 0) ≤-enl α₀) (≤→≤l ≤-refl)
```

```agda
rec-by-≤-enl : ∀ α₀ → ≤-increasing F → <-enlarging F → ≤-enlarging (rec F from α₀ by_)
rec-by-≤-enl α₀ ≤-inc <-enl zero    = z≤
rec-by-≤-enl α₀ ≤-inc <-enl (suc α) = ≤-trans (s≤s (rec-by-≤-enl α₀ ≤-inc <-enl α)) (<→s≤ (<-enl _))
rec-by-≤-enl α₀ ≤-inc <-enl (lim f) = l≤ (λ n → ≤→≤l (rec-by-≤-enl α₀ ≤-inc <-enl (f n)))
```

```agda
∸-increasing : (Ord → Ord) → Set
∸-increasing F = ∀ α d → F (suc (α ∸ d)) ≤ F α
```

```agda
rec-by-∸-inc : ∀ α₀ → ≤-enlarging F → ∸-increasing (rec F from α₀ by_)
rec-by-∸-inc α₀ ≤-enl (suc α) (inj₁ tt) = ≤-refl
rec-by-∸-inc α₀ ≤-enl (suc α) (inj₂ d)  = ≤-trans (rec-by-∸-inc α₀ ≤-enl α d) (≤-enl _)
rec-by-∸-inc α₀ ≤-enl (lim f) (n , d)   = ≤-trans (rec-by-∸-inc α₀ ≤-enl (f n) d) (≤→≤l ≤-refl)
```

```agda
rec-by-≤-inc : ∀ α₀ → ≤-increasing F → ≤-enlarging F → ≤-increasing (rec F from α₀ by_)
rec-by-≤-inc α₀ ≤-inc ≤-enl {α} {β} z≤      = rec-from-≤-enl β ≤-enl α₀
rec-by-≤-inc α₀ ≤-inc ≤-enl {α} {β} (s≤ ≤∸) = ≤-trans
  (≤-inc (rec-by-≤-inc α₀ ≤-inc ≤-enl ≤∸))
  (rec-by-∸-inc α₀ ≤-enl β _)
rec-by-≤-inc α₀ ≤-inc ≤-enl {α} {β} (l≤ f≤) = l≤ λ n → rec-by-≤-inc α₀ ≤-inc ≤-enl (f≤ n)
```
