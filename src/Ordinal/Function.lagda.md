---
title: Agda大序数(3) 序数函数
zhihu-tags: Agda, 序数, 大数数学
---

# Agda大序数(3) 序数函数

> 交流Q群: 893531731  
> 本文源码: [Ordinal/Function.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/Ordinal/Function.lagda.md)  
> GitHub Pages: [Ordinal.Function.html](https://choukh.github.io/agda-lvo/Ordinal.Function.html)  
> 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

```agda
{-# OPTIONS --without-K --safe #-}

module Ordinal.Function where

open import Ordinal using (Ord; _≈_)
open import Ordinal.WellFormed using (wellFormed)
```
