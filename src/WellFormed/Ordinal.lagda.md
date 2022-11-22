---
title: Agda大序数(2-1) 良构序数
zhihu-tags: Agda, 序数, 大数数学
---

# Agda大序数(2-1) 良构序数

> 交流Q群: 893531731  
> 目录: [WellFormed.html](https://choukh.github.io/agda-lvo/WellFormed.html)  
> 本文源码: [Ordinal.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/WellFormed/Ordinal.lagda.md)  
> 高亮渲染: [Ordinal.html](https://choukh.github.io/agda-lvo/WellFormed.Ordinal.html)  
> 如果你在知乎看到本文: 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

```agda
{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --overlapping-instances #-}

module WellFormed.Ordinal where
```

## 前置

```agda
open import NonWellFormed.Ordinal as ord using (zero; suc; lim) renaming (Ord to ord)
open import NonWellFormed.WellFormed as ord using (WellFormed)

open import Data.Unit using (tt)
open import Data.Nat as ℕ using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (_∘_)
open import Level using (0ℓ)
open import Relation.Binary using (Monotonic₁)
open import Relation.Binary using (Rel; _⇒_)
```

## 良构序数

```agda
record Ord : Set where
  constructor wf
  field
    nwf : ord
    ⦃ wellFormed ⦄ : WellFormed nwf

open Ord

_≤_ : Rel Ord 0ℓ
wf α ≤ wf β = α ord.≤ β

_<_ : Rel Ord 0ℓ
wf α < wf β = α ord.< β

_≈_ : Rel Ord 0ℓ
wf α ≈ wf β = α ord.≈ β

monoSequence : (ℕ → Ord) → Set
monoSequence = Monotonic₁ ℕ._<_ _<_

Zero : Ord
Zero = wf zero

Suc : Ord → Ord
Suc (wf α) = wf (suc α)
```
