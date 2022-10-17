---
title: Agda大序数(0) 总目录
zhihu-tags: Agda, 序数, 大数数学
---

# Agda大序数(0) 总目录

> 交流Q群: 893531731  
> 本文源码: [Everything.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/Everything.lagda.md)  
> 高亮渲染: [Everything.html](https://choukh.github.io/agda-lvo/Everything.html)  
> 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

```agda
{-# OPTIONS --without-K --safe #-}
```

## 所有模块

```agda
open import Ordinal public
```

- Brouwer 序数的归纳定义
- 非严格序 `_≤_` 的归纳定义
- 外延等词 `_≈_` 与严格序 `_<_` 由 `_≤_` 定义
- 证明了 `_≤_` 是偏序, `_<_` 是严格序
- 没有线序, 但不影响后续构筑

```agda
open import Ordinal.WellFormed public
```

- 定义良构序数为由严格递增序列递归构造的序数
- 证明了有限序数与 `ω` 是良构序数

```agda
open import Ordinal.Function public
```

- 定义了序数函数的常用性质
- 对序数嵌入 (normal function) 的定义做了构造主义改造
