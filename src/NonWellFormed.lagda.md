---
title: Agda大序数(1-0) 第1卷目录
zhihu-tags: Agda, 序数, 大数数学
zhihu-url: https://zhuanlan.zhihu.com/p/585851715
---

# Agda大序数(1-0) 第1卷目录

> 交流Q群: 893531731  
> 本文源码: [NonWellFormed.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/NonWellFormed.lagda.md)  
> 高亮渲染: [NonWellFormed.html](https://choukh.github.io/agda-lvo/NonWellFormed.html)  
> 如果你在知乎看到本文: 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

```agda
{-# OPTIONS --without-K --safe #-}

module NonWellFormed where
```

```agda
open import NonWellFormed.Ordinal public
```

- Brouwer 序数的归纳定义
- 非严格序 `_≤_` 的归纳定义
- 外延等词 `_≈_` 与严格序 `_<_` 由 `_≤_` 定义
- 证明了 `_≤_` 是偏序, `_<_` 是严格序
- 没有线序, 但不影响后续构筑

```agda
open import NonWellFormed.WellFormed public
```

- 定义良构序数为由单调序列递归构造的序数
- 证明了有限序数与 `ω` 是良构序数

```agda
open import NonWellFormed.Function public
```

- 定义了序数函数的常用性质
- 对序数嵌入 (normal function) 的定义做了一些改造, 使之不依赖良构条件

```agda
open import NonWellFormed.Recursion public
```

- 定义了一般形式的序数递归函数 (超限递归), 并证明了它的一般性质

```agda
open import NonWellFormed.Arithmetic public
```

- 由超限递归定义了 `_+_`, `_*_` 和 `_^_` 并证明了它们的保良构性
- 结合律, 分配律, 等等

```agda
open import NonWellFormed.Tetration public
```

- 我们展示第四级运算被锁死, 即 `α ^^ β ≈ α ^^ ω` 对任意 `β ≥ ω`

```agda
open import NonWellFormed.Fixpoint public
```

- 定义了无穷迭代 `_⋱_`
- 如果 `F` 是序数嵌入那么 `F ⋱ α` 是不小于 `α` 的不动点
- 递归 `F ⋱_ ∘ suc` 即得 `F` 的不动点枚举函数, 记作 `F ′`
- 我们证明了高阶函数 `_′` 保持序数嵌入且保持保良序性

```agda
open import NonWellFormed.Fixpoint.Lower public
```

- 关于不动点的一些平凡的例子

```agda
open import NonWellFormed.Epsilon public
```

- ε函数定义为 `(ω ^_) ′`
- 对任意 `α` 有 `ε (suc α) ≡ ω ^^[ suc (ε α) ] ω`
- ζ 定义为 `ε ′` 且 η 为 `ζ ′`
- `ε`, `ζ`, `η`, ... 都是序数嵌入且保良构

```agda
open import NonWellFormed.Epsilon.Alternative public
```

- 我们证明了对任意良构 `α` 有 `ε (suc α) ≈ ε α ^^ ω`

```agda
open import NonWellFormed.VeblenFunction public
```

- 定义了二元 Veblen 函数 `φ α β`
- 证明了 `φ` 的嵌入性, 单调性, 合同性, 不动点性和保良构性
- Γ₀ 定义为 `(λ α → φ α zero) ⋱ zero`

[前往第2卷](https://choukh.github.io/agda-lvo/WellFormed.html)
