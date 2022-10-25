---
title: Agda大序数(5) 序数算术
zhihu-tags: Agda, 序数, 大数数学
---

# Agda大序数(5) 序数算术

> 交流Q群: 893531731  
> 总目录: [Everything.html](https://choukh.github.io/agda-lvo/Everything.html)  
> 本文源码: [Ordinal/Arithmetic.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/Ordinal/Arithmetic.lagda.md)  
> 高亮渲染: [Ordinal.Arithmetic.html](https://choukh.github.io/agda-lvo/Ordinal.Arithmetic.html)  
> 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

**(本章施工中)**

```agda
{-# OPTIONS --without-K --safe #-}

module Ordinal.Arithmetic where
```

本章在内容上延续前四章.

```agda
open import Ordinal
open import Ordinal.WellFormed using (wellFormed; ⌜_⌝)
open import Ordinal.Function
open import Ordinal.Recursion
```

我们需要以下标准库依赖.

```agda
open import Algebra.Definitions {A = Ord} _≈_
open import Data.Nat as ℕ using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Relation.Binary.Reasoning.Setoid (OrdSetoid)
  using (begin_; step-≈; step-≈˘; _∎)
```

## 序数算术

本章考察序数的加法, 乘法和指数运算.

```agda
infixl 6 _+_
infixl 7 _*_
infixl 8 _^_
```

按序数理论的惯例我们用右边的数作为递归次数, 于是加法定义为对左边的数取右边的数那么多次后继. 这与 Agda 的自然数加法正好相反.

```agda
_+_ : Ord → Ord → Ord
α + β = rec suc from α by β
```

由于序数算术不满足交换律, 中缀算符的左右两边所扮演的角色是不对等的. 一旦选取了加法的方向, 乘法和指数运算所递归的函数也随即确定, 即为 `_+` 和 `_*`. 相反的方向 (`+_` 和 `*_`) 性质会很差, 具体我们后面会考察.

```agda
_*_ : Ord → Ord → Ord
α * β = rec (_+ α) from ⌜ 0 ⌝ by β

_^_ : Ord → Ord → Ord
α ^ β = rec (_* α) from ⌜ 1 ⌝ by β
```

由定义立即有

```agda
_ : ∀ {α} → α + zero ≡ α
_ = refl

_ : ∀ {α β} → α + suc β ≡ suc (α + β)
_ = refl

_ : ∀ {α f} → α + lim f ≡ lim λ n → α + f n
_ = refl
```

```agda
_ : ∀ {α} → α * zero ≡ zero
_ = refl

_ : ∀ {α β} → α * suc β ≡ α * β + α
_ = refl

_ : ∀ {α f} → α * lim f ≡ lim λ n → α * f n
_ = refl
```

```agda
_ : ∀ {α} → α ^ zero ≡ ⌜ 1 ⌝
_ = refl

_ : ∀ {α β} → α ^ suc β ≡ α ^ β * α
_ = refl

_ : ∀ {α f} → α ^ lim f ≡ lim λ n → α ^ f n
_ = refl
```

## 加法

我们对照 [Data.Nat.Properties](https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#14236) 考察序数加法的性质.

序数加法有结合律, 但没有交换律.

```agda
+-assoc : Associative _+_
+-assoc _ _ zero = ≡→≈ refl
+-assoc α β (suc γ) = s≈s (+-assoc α β γ)
+-assoc α β (lim f) = l≤ (λ n → ≤→≤l (proj₁ (+-assoc α β (f n))))
                    , l≤ (λ n → ≤→≤l (proj₂ (+-assoc α β (f n))))
```

序数零是序数加法单位元.

```agda
+-identityˡ : LeftIdentity zero _+_
+-identityˡ zero    = ≡→≈ refl
+-identityˡ (suc α) = s≈s (+-identityˡ α)
+-identityˡ (lim f) = l≤ (λ n → ≤→≤l (proj₁ (+-identityˡ (f n))))
                    , l≤ (λ n → ≤→≤l (proj₂ (+-identityˡ (f n))))

+-identityʳ : RightIdentity zero _+_
+-identityʳ = λ _ → ≡→≈ refl

+-identity : Identity zero _+_
+-identity = +-identityˡ , +-identityʳ
```

如所期望的那样, 序数算术也有一加一等于二.

```agda
_ : ⌜ 1 ⌝ + ⌜ 1 ⌝ ≡ ⌜ 2 ⌝
_ = refl
```

一般地, 我们有

```agda
--m+n : ∀ {m n} → ⌜ m ⌝ + ⌜ n ⌝ ≡ ⌜ m ℕ.+ n ⌝
--m+n {ℕ.zero} = {!   !}
--m+n {ℕ.suc m} = {!   !}
```

序数加法没有 `suc α + β ≡ suc (α + β)`
