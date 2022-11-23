---
title: Agda大序数(2-2) 良构序数
zhihu-tags: Agda, 序数, 大数数学
---

# Agda大序数(2-2) 良构序数

> 交流Q群: 893531731  
> 目录: [WellFormed.html](https://choukh.github.io/agda-lvo/WellFormed.html)  
> 本文源码: [WellFormed.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/WellFormed/WellFormed.lagda.md)  
> 高亮渲染: [WellFormed.html](https://choukh.github.io/agda-lvo/WellFormed.WellFormed.html)  
> 如果你在知乎看到本文: 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

```agda
{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --overlapping-instances #-}

module WellFormed.WellFormed where
```

```agda
open import WellFormed.Ordinal
open import NonWellFormed.WellFormed as ord
  using (MonoSequence; WellFormed; wrap; ⌜_⌝-wellFormed; ⌜⌝-monoSequence)
open Ord using (nwf)
open MonoSequence using (unwrap)

open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym)
```

```agda
⌜_⌝ : ℕ → Ord
⌜ zero ⌝ = Zero
⌜ suc n ⌝ = wf ord.⌜ suc n ⌝ ⦃ ⌜ n ⌝-wellFormed ⦄

ord⌜_⌝ : ∀ n → nwf ⌜ n ⌝ ≡ ord.⌜ n ⌝
ord⌜ zero ⌝ = refl
ord⌜ suc n ⌝ = refl

ω : Ord
ω = Lim ⌜_⌝ mono where
  mono : monoSequence ⌜_⌝
  mono {m} {n} rewrite ord⌜ m ⌝ | ord⌜ n ⌝ = unwrap ⌜⌝-monoSequence


```
