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

## 前置

本章在内容上延续前四章.

```agda
open import Ordinal
open import Ordinal.WellFormed using (wellFormed; ⌜_⌝; ω)
open import Ordinal.Function
open import Ordinal.Recursion
```

以下标准库依赖在前几章都出现过.

```agda
open import Data.Nat as ℕ using (ℕ)
import Data.Nat.Properties as ℕ
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (id)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; refl; sym; cong)
```

本章需要 `≤-Reasoning` 和 `≡-Reasoning` 两套推理, 由于 syntax 重名, 我们采用短模块名进行区分.

```agda
open module ≡ = Eq.≡-Reasoning
open module ≤ = Ordinal.≤-Reasoning
```

本章需要考察序数上的代数结构.

```agda
open import Algebra.Definitions {A = Ord} _≈_
open import Algebra.Structures  {A = Ord} _≈_
```

## 序数算术

我们引入序数的加法, 乘法和幂运算.

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

由于序数算术不满足交换律, 中缀算符的左右两边所扮演的角色是不对等的. 一旦选取了加法的方向, 乘法和幂运算所递归的函数也随即确定, 即为 `_+` 和 `_*`. 相反的方向 (`+_` 和 `*_`) 性质会很差, 具体我们后面会考察.

```agda
_*_ : Ord → Ord → Ord
α * β = rec (_+ α) from ⌜ 0 ⌝ by β

_^_ : Ord → Ord → Ord
α ^ β = rec (_* α) from ⌜ 1 ⌝ by β
```

## 加法

由 `_+_` 的定义立即有

```agda
_ : ∀ {α} → α + zero ≡ α
_ = refl

_ : ∀ {α β} → α + suc β ≡ suc (α + β)
_ = refl

_ : ∀ {α f} → α + lim f ≡ lim λ n → α + f n
_ = refl
```

### 有限序数

如所期望的那样, 我们有序数算术版的一加一等于二.

```agda
_ : ⌜ 1 ⌝ + ⌜ 1 ⌝ ≡ ⌜ 2 ⌝
_ = refl
```

一般地, 我们有

**事实** 有限序数加法与自然数加法等价.

```agda
⌜_⌝+⌜_⌝ : ∀ m n → ⌜ m ⌝ + ⌜ n ⌝ ≡ ⌜ m ℕ.+ n ⌝
⌜ m ⌝+⌜ ℕ.zero ⌝    = ≡.begin
  ⌜ m ⌝ + ⌜ ℕ.zero ⌝  ≡.≡⟨⟩
  ⌜ m ⌝               ≡.≡˘⟨ cong ⌜_⌝ (ℕ.+-identityʳ m) ⟩
  ⌜ m ℕ.+ ℕ.zero ⌝    ≡.∎
⌜ m ⌝+⌜ ℕ.suc n ⌝   = ≡.begin
  ⌜ m ⌝ + suc ⌜ n ⌝   ≡.≡⟨⟩
  suc (⌜ m ⌝ + ⌜ n ⌝) ≡.≡⟨ cong suc ⌜ m ⌝+⌜ n ⌝ ⟩
  suc ⌜ m ℕ.+ n ⌝     ≡.≡˘⟨ cong ⌜_⌝ (ℕ.+-suc m n) ⟩
  ⌜ m ℕ.+ ℕ.suc n ⌝   ≡.∎
```

### 运算律

我们接着考察序数加法的一般性质.

**引理** 序数加法满足结合律.

```agda
+-assoc : Associative _+_
+-assoc _ _ zero = ≡⇒≈ refl
+-assoc α β (suc γ) = s≈s (+-assoc α β γ)
+-assoc α β (lim f) = l≤ (λ n → ≤→≤l (proj₁ (+-assoc α β (f n))))
                    , l≤ (λ n → ≤→≤l (proj₂ (+-assoc α β (f n))))
```

**引理** 序数零是序数加法单位元.

```agda
+-identityˡ : LeftIdentity zero _+_
+-identityˡ zero    = ≡⇒≈ refl
+-identityˡ (suc α) = s≈s (+-identityˡ α)
+-identityˡ (lim f) = l≤ (λ n → ≤→≤l (proj₁ (+-identityˡ (f n))))
                    , l≤ (λ n → ≤→≤l (proj₂ (+-identityˡ (f n))))

+-identityʳ : RightIdentity zero _+_
+-identityʳ = λ _ → ≡⇒≈ refl

+-identity : Identity zero _+_
+-identity = +-identityˡ , +-identityʳ
```

序数加法没有交换律, 反例如下.

```agda
_ : ω + ⌜ 1 ⌝ ≡ suc ω
_ = refl

1+ω : ⌜ 1 ⌝ + ω ≈ ω
1+ω = l≤ (λ n → ≤→≤l {n = ℕ.suc n}
        (≤-respˡ-≈ (≡⇒≈ (sym ⌜ 1 ⌝+⌜ n ⌝)) ≤-refl)) {- ⌜ 1 ⌝ + ⌜ n ⌝ ≤ suc ⌜ n ⌝ -}
    , l≤ (λ n → ≤→≤l {n = n}
        (≤-respʳ-≈ (≡⇒≈ (sym ⌜ 1 ⌝+⌜ n ⌝)) ≤s))     {- ⌜ n ⌝ ≤ ⌜ 1 ⌝ + ⌜ n ⌝ -}
```

### 增长性, 单调性与合同性

由上一章超限递归的基本性质立即得到序数加法的增长性和单调性.

```agda
+-incrˡ-≤ : ∀ α → ≤-increasing (_+ α)
+-incrˡ-≤ α β = rec-from-incr-≤ α (λ _ → ≤s) β

+-incrʳ-≤ : ∀ α → ≤-increasing (α +_)
+-incrʳ-≤ α β = rec-by-incr-≤ s≤s (λ _ → <s) β

+-incrˡ-< : ∀ α → α > zero → <-increasing (_+ α)
+-incrˡ-< α >z β = rec-from-incr-< >z s≤s (λ _ → <s) β

+-monoˡ-≤ : ∀ α → ≤-monotonic (_+ α)
+-monoˡ-≤ α ≤ = rec-from-mono-≤ α s≤s ≤

+-monoʳ-≤ : ∀ α → ≤-monotonic (α +_)
+-monoʳ-≤ α ≤ = rec-by-mono-≤ s≤s (λ _ → ≤s) ≤

+-monoʳ-< : ∀ α → <-monotonic (α +_ )
+-monoʳ-< α < = rec-by-mono-< s≤s (λ _ → <s) <
```

由 `+-monoˡ-≤` 以及 `+-monoʳ-≤` 立即得到 `_+_` 的合同性 (congruence).

```agda
+-congˡ : LeftCongruent _+_
+-congˡ {α} (≤ , ≥) = +-monoʳ-≤ α ≤ , +-monoʳ-≤ α ≥

+-congʳ : RightCongruent _+_
+-congʳ {α} (≤ , ≥) = +-monoˡ-≤ α ≤ , +-monoˡ-≤ α ≥

+-cong : Congruent₂ _+_
+-cong {v = v} x≈y u≈v = ≈-trans (+-congˡ u≈v) (+-congʳ {v} x≈y)
```

### 代数结构

序数加法构成原群, 半群和幺半群.

```agda
+-isMagma : IsMagma _+_
+-isMagma = record
  { isEquivalence = ≈-isEquivalence
  ; ∙-cong        = +-cong
  }

+-isSemigroup : IsSemigroup _+_
+-isSemigroup = record
  { isMagma = +-isMagma
  ; assoc   = +-assoc
  }

+-0-isMonoid : IsMonoid _+_ zero
+-0-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity    = +-identity
  }
```

## 乘法

由 `_*_` 的定义立即有

```agda
_ : ∀ {α} → α * zero ≡ zero
_ = refl

_ : ∀ {α β} → α * suc β ≡ α * β + α
_ = refl

_ : ∀ {α f} → α * lim f ≡ lim λ n → α * f n
_ = refl
```

### 有限序数

**事实** 有限序数乘法与自然数乘法等价.

## 幂运算

由 `_^_` 的定义立即有

```agda
_ : ∀ {α} → α ^ zero ≡ ⌜ 1 ⌝
_ = refl

_ : ∀ {α β} → α ^ suc β ≡ α ^ β * α
_ = refl

_ : ∀ {α f} → α ^ lim f ≡ lim λ n → α ^ f n
_ = refl
```

## 序数嵌入

`+_`, `*_`, `^_` 都是序数嵌入, 但 `_+`, `_*`, `_^` 不是.

```agda
+-normal : ∀ α → normal (α +_)
+-normal α = +-monoʳ-≤ α , +-monoʳ-< α , rec-ct
```

## 保良构性

`+_`, `*_`, `^_` 都保良构, 但 `_+`, `_*`, `_^` 不保.

```agda
+-wfp : ∀ {α} → wellFormed α → wf-preserving (α +_)
+-wfp wfα {β} = rec-wfp wfα s≤s (λ _ → <s) id {β}
```
