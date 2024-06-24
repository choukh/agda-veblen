---
title: Agda大序数(5) 序数算术
zhihu-tags: Agda, 序数, 大数数学
zhihu-url: https://zhuanlan.zhihu.com/p/578641323
---

# Agda大序数(5) 序数算术

> 交流Q群: 893531731  
> 目录: [NonWellFormed.html](https://choukh.github.io/agda-veblen/NonWellFormed.html)  
> 本文源码: [Arithmetic.lagda.md](https://github.com/choukh/agda-veblen/blob/main/src/NonWellFormed/Arithmetic.lagda.md)  
> 高亮渲染: [Arithmetic.html](https://choukh.github.io/agda-veblen/NonWellFormed.Arithmetic.html)  

本章打开了 [*实验性有损合一化*](https://agda.readthedocs.io/en/v2.6.2.2/language/lossy-unification.html) 特性, 它可以减少显式标记隐式参数的需要, 而且跟 `--safe` 是兼容的. 当然它也有一些缺点, 具体这里不会展开.

```agda
{-# OPTIONS --without-K --safe --experimental-lossy-unification #-}

module NonWellFormed.Arithmetic where
```

## 前置

本章在内容上延续前四章.

```agda
open import NonWellFormed.Ordinal
open import NonWellFormed.WellFormed
open import NonWellFormed.Function
open import NonWellFormed.Recursion
```

以下标准库依赖在前几章都出现过.

```agda
open import Level using (0ℓ)
open import Data.Nat as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕ
open import Data.Unit using (tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (id; λ-)
open import Relation.Binary using (_Preserves_⟶_)
open Relation.Binary.Tri
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong)
```

本章需要 `≤-Reasoning` 和 `≡-Reasoning` 两套推理. 由于 `step-≡` 对应的 syntax 重名, 我们加上短模块名进行区分: `≡.≡⟨⟩`, `≤.≡⟨⟩`.

```agda
open module ≡ = Eq.≡-Reasoning renaming
  ( begin_          to begin-propeq_
  ; _∎              to _◼)
open module ≤ = NonWellFormed.Ordinal.≤-Reasoning renaming
  ( begin-equality_ to begin-eq_
  ; begin_          to begin-nonstrict_)
```

本章需要谈论序数上的代数结构.

```agda
open import Algebra.Bundles
open import Algebra.Morphism
open import Algebra.Definitions {A = Ord} _≈_
open import Algebra.Structures  {A = Ord} _≈_
```

## 序数算术

我们引入序数的加法, 乘法和幂运算.

```agda
infixl 6 _+_
infixl 7 _*_
infix 8 _^_
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
⌜⌝+⌜⌝≡⌜+⌝ : ∀ m n → ⌜ m ⌝ + ⌜ n ⌝ ≡ ⌜ m ℕ.+ n ⌝
⌜⌝+⌜⌝≡⌜+⌝ m zero      = begin-propeq
  ⌜ m ⌝ + ⌜ 0 ⌝         ≡.≡⟨⟩
  ⌜ m ⌝                 ≡.≡˘⟨ cong ⌜_⌝ (ℕ.+-identityʳ m) ⟩
  ⌜ m ℕ.+ 0 ⌝           ◼
⌜⌝+⌜⌝≡⌜+⌝ m (suc n)   = begin-propeq
  ⌜ m ⌝ + suc ⌜ n ⌝     ≡.≡⟨⟩
  suc (⌜ m ⌝ + ⌜ n ⌝)   ≡.≡⟨ cong suc (⌜⌝+⌜⌝≡⌜+⌝ m n) ⟩
  suc ⌜ m ℕ.+ n ⌝       ≡.≡˘⟨ cong ⌜_⌝ (ℕ.+-suc m n) ⟩
  ⌜ m ℕ.+ suc n ⌝       ◼
```

### 运算律

我们接着考察序数加法的一般性质.

**引理** 序数加法满足结合律.

```agda
+-assoc : Associative _+_
+-assoc _ _ zero    = ≈-refl
+-assoc α β (suc γ) = s≈s (+-assoc α β γ)
+-assoc α β (lim f) = l≈l (+-assoc α β (f _))
```

**引理** `⌜ 0 ⌝` 是序数加法的幺元.

```agda
+-identityˡ : LeftIdentity ⌜ 0 ⌝ _+_
+-identityˡ zero    = ≈-refl
+-identityˡ (suc α) = s≈s (+-identityˡ α)
+-identityˡ (lim f) = l≈l (+-identityˡ (f _))

+-identityʳ : RightIdentity ⌜ 0 ⌝ _+_
+-identityʳ = λ- ≈-refl

+-identity : Identity ⌜ 0 ⌝ _+_
+-identity = +-identityˡ , +-identityʳ
```

序数加法没有交换律, 反例如下.

```agda
_ : ω + ⌜ 1 ⌝ ≡ suc ω
_ = refl

1+ω≈ω : ⌜ 1 ⌝ + ω ≈ ω
1+ω≈ω =                     begin-eq
  lim (λ n → ⌜ 1 ⌝ + ⌜ n ⌝) ≈⟨ l≈l (≡⇒≈ (⌜⌝+⌜⌝≡⌜+⌝ 1 _)) ⟩
  lim (λ n → ⌜ 1 ℕ.+ n ⌝)   ≈˘⟨ l≈ls ≤s ⟩
  lim (λ n → ⌜ n ⌝)         ∎
```

### 增长性, 单调性与合同性

由上一章超限递归的基本性质立即得到序数加法的增长性和单调性.

```agda
module _ (α) where

  +-incrʳ-≤ : ≤-increasing (_+ α)
  +-incrʳ-≤ β = rec-from-incr-≤ α (λ- ≤s) β

  +-incrˡ-≤ : ≤-increasing (α +_)
  +-incrˡ-≤ β = rec-by-incr-≤ s≤s (λ- <s) β

  +-incrʳ-< : α > ⌜ 0 ⌝ → <-increasing (_+ α)
  +-incrʳ-< >z β = rec-from-incr-< >z s≤s (λ- <s) β

  +-monoˡ-≤ : ≤-monotonic (_+ α)
  +-monoˡ-≤ ≤ = rec-from-mono-≤ α s≤s ≤

  +-monoʳ-≤ : ≤-monotonic (α +_)
  +-monoʳ-≤ ≤ = rec-by-mono-≤ s≤s (λ- ≤s) ≤

  +-monoʳ-< : <-monotonic (α +_ )
  +-monoʳ-< < = rec-by-mono-< s≤s (λ- <s) <
```

**注意** 只有 `_+` 是强增长的, `+_` 不保证强增长. 这就是我们在乘法的定义中使用 `_+` 的原因.

由 `+-monoˡ-≤` 以及 `+-monoʳ-≤` 立即得到 `_+_` 的合同性 (congruence).

```agda
+-congˡ : LeftCongruent _+_
+-congˡ {α} (≤ , ≥) = +-monoʳ-≤ α ≤ , +-monoʳ-≤ α ≥

+-congʳ : RightCongruent _+_
+-congʳ {α} (≤ , ≥) = +-monoˡ-≤ α ≤ , +-monoˡ-≤ α ≥

+-cong : Congruent₂ _+_
+-cong {α} {β} {γ} {δ} α≈β γ≈δ = begin-eq
  α + γ ≈⟨ +-congˡ γ≈δ ⟩
  α + δ ≈⟨ +-congʳ α≈β ⟩
  β + δ ∎
```

### 代数结构

**定理** 序数加法构成原群, 半群和幺半群.

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

+-0-isMonoid : IsMonoid _+_ ⌜ 0 ⌝
+-0-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity    = +-identity
  }
```

```agda
+-magma : Magma 0ℓ 0ℓ
+-magma = record
  { isMagma = +-isMagma
  }

+-semigroup : Semigroup 0ℓ 0ℓ
+-semigroup = record
  { isSemigroup = +-isSemigroup
  }

+-0-monoid : Monoid 0ℓ 0ℓ
+-0-monoid = record
  { isMonoid = +-0-isMonoid
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

```agda
⌜⌝*⌜⌝≡⌜*⌝ : ∀ m n → ⌜ m ⌝ * ⌜ n ⌝ ≡ ⌜ m ℕ.* n ⌝
⌜⌝*⌜⌝≡⌜*⌝ m zero        = begin-propeq
  ⌜ m ⌝ * ⌜ 0 ⌝           ≡.≡˘⟨ cong ⌜_⌝ (ℕ.*-zeroʳ m) ⟩
  ⌜ m ℕ.* 0 ⌝             ◼
⌜⌝*⌜⌝≡⌜*⌝ m (suc n)     = begin-propeq
  ⌜ m ⌝ * suc ⌜ n ⌝       ≡.≡⟨⟩
  ⌜ m ⌝ * ⌜ n ⌝ + ⌜ m ⌝   ≡.≡⟨ cong (_+ ⌜ m ⌝) (⌜⌝*⌜⌝≡⌜*⌝ m n) ⟩
  ⌜ m ℕ.* n ⌝ + ⌜ m ⌝     ≡.≡⟨ ⌜⌝+⌜⌝≡⌜+⌝ (m ℕ.* n) m ⟩
  ⌜ m ℕ.* n ℕ.+ m ⌝       ≡.≡⟨ cong ⌜_⌝ (ℕ.+-comm (m ℕ.* n) m) ⟩
  ⌜ m ℕ.+ m ℕ.* n ⌝       ≡.≡˘⟨ cong ⌜_⌝ (ℕ.*-suc m n) ⟩
  ⌜ m ℕ.* suc n ⌝         ◼
```

### 运算律

**引理** `⌜ 1 ⌝` 是序数乘法的幺元.

```agda
*-identityˡ : LeftIdentity ⌜ 1 ⌝ _*_
*-identityˡ zero    = ≈-refl
*-identityˡ (suc α) = begin-eq
  ⌜ 1 ⌝ * suc α       ≤.≡⟨⟩
  suc (⌜ 1 ⌝ * α)     ≈⟨ s≈s (*-identityˡ α) ⟩
  suc α               ∎
*-identityˡ (lim f) = l≈l (*-identityˡ (f _))

*-identityʳ : RightIdentity ⌜ 1 ⌝ _*_
*-identityʳ α = begin-eq
  α * ⌜ 1 ⌝     ≤.≡⟨⟩
  α * ⌜ 0 ⌝ + α ≈⟨ +-identityˡ α ⟩
  α             ∎

*-identity : Identity ⌜ 1 ⌝ _*_
*-identity = *-identityˡ , *-identityʳ
```

**引理** `⌜ 0 ⌝` 是序数乘法的零元.

```agda
*-zeroˡ : LeftZero ⌜ 0 ⌝ _*_
*-zeroˡ zero      = ≈-refl
*-zeroˡ (suc α)   = begin-eq
  ⌜ 0 ⌝ * suc α     ≤.≡⟨⟩
  ⌜ 0 ⌝ * α + ⌜ 0 ⌝ ≈⟨ +-identityʳ (⌜ 0 ⌝ * α) ⟩
  ⌜ 0 ⌝ * α         ≈⟨ *-zeroˡ α ⟩
  ⌜ 0 ⌝             ∎
*-zeroˡ (lim f) = l≤ (λ n → proj₁ (*-zeroˡ (f n))) , z≤

*-zeroʳ : RightZero ⌜ 0 ⌝ _*_
*-zeroʳ _ = ≈-refl

*-zero : Zero ⌜ 0 ⌝ _*_
*-zero = *-zeroˡ , *-zeroʳ
```

**引理** 序数乘法对序数加法满足左分配律.

```agda
*-distribˡ-+ : _*_ DistributesOverˡ _+_
*-distribˡ-+ α β zero     = begin-eq
  α * (β + ⌜ 0 ⌝)           ≤.≡⟨⟩
  α * β + ⌜ 0 ⌝             ≈˘⟨ +-congˡ (*-zeroʳ (α * β)) ⟩
  α * β + α * ⌜ 0 ⌝         ∎
*-distribˡ-+ α β (suc γ)  = begin-eq
  α * (β + suc γ)           ≤.≡⟨⟩
  α * (β + γ) + α           ≈⟨ +-congʳ (*-distribˡ-+ α β γ) ⟩
  α * β + α * γ + α         ≈⟨ +-assoc (α * β) (α * γ) α ⟩
  α * β + (α * γ + α)       ≤.≡⟨⟩
  α * β + (α * suc γ)       ∎
*-distribˡ-+ α β (lim f)  = l≈l (*-distribˡ-+ α β (f _))
```

**引理** 序数乘法满足结合律.

```agda
*-assoc : Associative _*_
*-assoc α β zero    = ≈-refl
*-assoc α β (suc γ) = begin-eq
  α * β * suc γ       ≤.≡⟨⟩
  α * β * γ + α * β   ≈⟨ +-congʳ {α * β} (*-assoc α β γ) ⟩
  α * (β * γ) + α * β ≈˘⟨ *-distribˡ-+ α (β * γ) β ⟩
  α * (β * γ + β)     ≤.≡⟨⟩
  α * (β * suc γ)     ∎
*-assoc α β (lim f) = l≈l (*-assoc α β (f _))
```

### 增长性, 单调性与合同性

序数乘法的单调性等需要配合序数加法的相关性质, 且需要注意运算方向和证明顺序都与加法有所不同, 且有些性质需要额外的前提.

首先是从 `*_` 的 ≤-单调性推出 `_*` 的弱增长性.

```agda
*-monoʳ-≤ : ∀ α → ≤-monotonic (α *_)
*-monoʳ-≤ α = rec-by-mono-≤ (+-monoˡ-≤ α) (+-incrʳ-≤ α)

*-incrʳ-≤ : ∀ α → ⦃ α ≥ ⌜ 1 ⌝ ⦄ → ≤-increasing (_* α)
*-incrʳ-≤ α ⦃ α≥1 ⦄ β = begin-nonstrict
  β                     ≈˘⟨ *-identityʳ β ⟩
  β * ⌜ 1 ⌝             ≤⟨ *-monoʳ-≤ β α≥1 ⟩
  β * α                 ∎
```

然后, 类似地, 从 `*_` 的 <-单调性推出 `_*` 的强增长性.

```agda
*-monoʳ-< : ∀ α → ⦃ α > ⌜ 0 ⌝ ⦄ → <-monotonic (α *_)
*-monoʳ-< α ⦃ α>0 ⦄ = rec-by-mono-< (+-monoˡ-≤ α) (+-incrʳ-< α α>0)

*-incrʳ-< : ∀ α β → ⦃ α > ⌜ 0 ⌝ ⦄ → ⦃ β > ⌜ 1 ⌝ ⦄ → α < α * β
*-incrʳ-< α β ⦃ _ ⦄ ⦃ β>1 ⦄ = begin-strict
  α                         ≈˘⟨ *-identityʳ α ⟩
  α * ⌜ 1 ⌝                 <⟨ *-monoʳ-< α β>1 ⟩
  α * β                     ∎
```

**注意** 只有 `_*` 是强增长的, `*_` 不保证强增长. 这就是我们在幂运算的定义中使用 `_*` 的原因.

接着是从 `_*` 的 ≤-单调性推出 `*_` 的弱增长性. 注意前者已经无法使用超限递归的相关引理了, 需要直接用归纳法证明.

```agda
*-monoˡ-≤ : ∀ α → ≤-monotonic (_* α)
*-monoˡ-≤ zero            _ = z≤
*-monoˡ-≤ (suc α) {β} {γ} ≤ = begin-nonstrict
  β * suc α                   ≤.≡⟨⟩
  β * α + β                   ≤⟨ +-monoʳ-≤ (β * α) ≤ ⟩
  β * α + γ                   ≤⟨ +-monoˡ-≤ γ (*-monoˡ-≤ α ≤) ⟩
  γ * α + γ                   ≤.≡⟨⟩
  γ * suc α                   ∎
*-monoˡ-≤ (lim f) {β} {γ} ≤ = l≤ λ n → ≤f⇒≤l (*-monoˡ-≤ (f n) ≤)

*-incrˡ-≤ : ∀ α → ⦃ α ≥ ⌜ 1 ⌝ ⦄ → ≤-increasing (α *_)
*-incrˡ-≤ α ⦃ α≥1 ⦄ β = begin-nonstrict
  β                     ≈˘⟨ *-identityˡ β ⟩
  ⌜ 1 ⌝ * β             ≤⟨ *-monoˡ-≤ β α≥1 ⟩
  α * β                 ∎
```

最后, 我们用 ≤-单调性证明合同性.

```agda
*-congˡ : LeftCongruent _*_
*-congˡ {α} (≤ , ≥) = *-monoʳ-≤ α ≤ , *-monoʳ-≤ α ≥

*-congʳ : RightCongruent _*_
*-congʳ {α} (≤ , ≥) = *-monoˡ-≤ α ≤ , *-monoˡ-≤ α ≥

*-cong : Congruent₂ _*_
*-cong {α} {β} {γ} {δ} α≈β γ≈δ = begin-eq
  α * γ ≈⟨ *-congˡ γ≈δ ⟩
  α * δ ≈⟨ *-congʳ α≈β ⟩
  β * δ ∎
```

### 代数结构

**定理** 序数乘法构成原群, 半群和幺半群.

```agda
*-isMagma : IsMagma _*_
*-isMagma = record
  { isEquivalence = ≈-isEquivalence
  ; ∙-cong        = *-cong
  }

*-isSemigroup : IsSemigroup _*_
*-isSemigroup = record
  { isMagma = *-isMagma
  ; assoc   = *-assoc
  }

*-1-isMonoid : IsMonoid _*_ ⌜ 1 ⌝
*-1-isMonoid = record
  { isSemigroup = *-isSemigroup
  ; identity    = *-identity
  }
```

```agda
*-magma : Magma 0ℓ 0ℓ
*-magma = record
  { isMagma = *-isMagma
  }

*-semigroup : Semigroup 0ℓ 0ℓ
*-semigroup = record
  { isSemigroup = *-isSemigroup
  }

*-1-monoid : Monoid 0ℓ 0ℓ
*-1-monoid = record
  { isMonoid = *-1-isMonoid
  }
```

### 其他引理

```agda
α*2≈α+α : ∀ α → α * ⌜ 2 ⌝ ≈ α + α
α*2≈α+α α     = begin-eq
  α * ⌜ 2 ⌝     ≤.≡⟨⟩
  α * ⌜ 1 ⌝ + α ≈⟨ +-congʳ (*-identityʳ α) ⟩
  α + α         ∎
```

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

### 有限序数

**事实** 有限序数幂运算与自然数幂运算等价.

```agda
⌜⌝^⌜⌝≡⌜^⌝ : ∀ m n → ⌜ m ⌝ ^ ⌜ n ⌝ ≡ ⌜ m ℕ.^ n ⌝
⌜⌝^⌜⌝≡⌜^⌝ m zero      = refl
⌜⌝^⌜⌝≡⌜^⌝ m (suc n)   = begin-propeq
  ⌜ m ⌝ ^ suc ⌜ n ⌝     ≡.≡⟨⟩
  ⌜ m ⌝ ^ ⌜ n ⌝ * ⌜ m ⌝ ≡.≡⟨ cong (_* ⌜ m ⌝) (⌜⌝^⌜⌝≡⌜^⌝ m n) ⟩
  ⌜ m ℕ.^ n ⌝ * ⌜ m ⌝   ≡.≡⟨ ⌜⌝*⌜⌝≡⌜*⌝ (m ℕ.^ n) m ⟩
  ⌜ m ℕ.^ n ℕ.* m ⌝     ≡.≡⟨ cong ⌜_⌝ (ℕ.*-comm (m ℕ.^ n) m) ⟩
  ⌜ m ℕ.^ suc n ⌝       ◼
```

### 运算律

**引理** `⌜ 1 ⌝` 是序数幂运算的右幺元和左零元.

```agda
^-identityʳ : RightIdentity ⌜ 1 ⌝ _^_
^-identityʳ α = begin-eq
  α ^ ⌜ 1 ⌝     ≤.≡⟨⟩
  α ^ ⌜ 0 ⌝ * α ≈⟨ *-identityˡ α ⟩
  α             ∎

^-zeroˡ : LeftZero ⌜ 1 ⌝ _^_
^-zeroˡ zero      = ≈-refl
^-zeroˡ (suc α)   = begin-eq
  ⌜ 1 ⌝ ^ suc α     ≤.≡⟨⟩
  ⌜ 1 ⌝ ^ α * ⌜ 1 ⌝ ≈⟨ *-identityʳ _ ⟩
  ⌜ 1 ⌝ ^ α         ≈⟨ ^-zeroˡ α ⟩
  ⌜ 1 ⌝             ∎
^-zeroˡ (lim f) = l≤ (λ n → proj₁ (^-zeroˡ (f n)))
                , ≤f⇒≤l (proj₂ (^-zeroˡ (f 1)))
```

零的幂比较奇怪. 首先零的零次幂是一, 这个由定义立即可得. 然后零的后继次幂是乘法右零元的特例.

```agda
_ : ∀ α → ⌜ 0 ⌝ ^ suc α ≈ ⌜ 0 ⌝
_ = *-zeroʳ
```

但是零的极限次幂在我们的构筑中不是良构序数. 例如 `zero ^ ω` 是如下序列的极限.

> zero ^ ⌜ 0 ⌝, zero ^ ⌜ 1 ⌝, zero ^ ⌜ 2 ⌝, ...

即

> ⌜ 1 ⌝, ⌜ 0 ⌝, ⌜ 0 ⌝, ...

当然我们可以无视首项, 把该序列的极限视作零, 就像有些书那样. 这里不做这种处理, 也没有必要.

**引理** 幂运算对加法满足左分配律, 只不过分配之后转换成了乘法.

```agda
^-distribˡ-+-* : ∀ α β γ → α ^ (β + γ) ≈ α ^ β * α ^ γ
^-distribˡ-+-* α β zero    = begin-eq
  α ^ (β + zero)             ≈˘⟨ *-identityʳ _ ⟩
  α ^ β * ⌜ 1 ⌝              ≈⟨ *-congˡ (≈-refl {⌜ 1 ⌝}) ⟩
  α ^ β * α ^ ⌜ 0 ⌝          ∎
^-distribˡ-+-* α β (suc γ) = begin-eq
  α ^ (β + suc γ)            ≤.≡⟨⟩
  α ^ (β + γ) * α            ≈⟨ *-congʳ (^-distribˡ-+-* α β γ) ⟩
  α ^ β * α ^ γ * α          ≈⟨ *-assoc _ _ _ ⟩
  α ^ β * (α ^ γ * α)        ≈⟨ *-congˡ ≈-refl ⟩
  α ^ β * (α ^ suc γ)        ∎
^-distribˡ-+-* α β (lim f) = l≈l (^-distribˡ-+-* α β (f _))
```

**引理** 幂运算满足结合律, 只不过结合之后转换成了乘法.

```agda
^-*-assoc : ∀ α β γ → (α ^ β) ^ γ ≈ α ^ (β * γ)
^-*-assoc α β zero    = ≈-refl
^-*-assoc α β (suc γ) = begin-eq
  (α ^ β) ^ suc γ       ≤.≡⟨⟩
  (α ^ β) ^ γ * α ^ β   ≈⟨ *-congʳ (^-*-assoc α β γ) ⟩
  α ^ (β * γ) * α ^ β   ≈˘⟨ ^-distribˡ-+-* α _ _ ⟩
  α ^ (β * γ + β)       ≤.≡⟨⟩
  α ^ (β * suc γ)       ∎
^-*-assoc α β (lim f) = l≈l (^-*-assoc α β (f _))
```

### 增长性, 单调性与合同性

幂运算的单调性等性质比乘法的更不规整, 需要更强的额外前提.

首先相对简单的是从 `^_` 的 ≤-单调性到 `_^` 的弱增长性.

```agda
^-monoʳ-≤ : ∀ α → ⦃ α ≥ ⌜ 1 ⌝ ⦄ → ≤-monotonic (α ^_)
^-monoʳ-≤ α = rec-by-mono-≤ (*-monoˡ-≤ α) (*-incrʳ-≤ α)

^-incrʳ-≤ : ∀ α β → ⦃ α ≥ ⌜ 1 ⌝ ⦄ → β ≥ ⌜ 1 ⌝ → α ≤ α ^ β
^-incrʳ-≤ α β β≥1 = begin-nonstrict
  α                 ≈˘⟨ ^-identityʳ α ⟩
  α ^ ⌜ 1 ⌝         ≤⟨ ^-monoʳ-≤ α β≥1 ⟩
  α ^ β             ∎
```

**引理** 底数不为零的幂运算结果大于零.

```agda
^>0 : ∀ {α β} → ⦃ α ≥ ⌜ 1 ⌝ ⦄ → α ^ β > ⌜ 0 ⌝
^>0 {α} {β} = begin-strict
  ⌜ 0 ⌝       <⟨ <s ⟩
  ⌜ 1 ⌝       ≤.≡⟨⟩
  α ^ ⌜ 0 ⌝   ≤⟨ ^-monoʳ-≤ α z≤ ⟩
  α ^ β       ∎
```

`^_` 的 <-单调性无法从 `rec-by-mono-<` 推出, 但可以直接用归纳法证明.

```agda
^-monoʳ-< : ∀ α → ⦃ α > ⌜ 1 ⌝ ⦄ → <-monotonic (α ^_)
^-monoʳ-< α ⦃ α>1 ⦄ {β} {suc γ} < =
  let instance α≥1 = <⇒≤ α>1 in begin-strict
  α ^ β                         ≤⟨ ^-monoʳ-≤ α (<s⇒≤ <) ⟩
  α ^ γ                         <⟨ *-incrʳ-< (α ^ γ) α ⦃ ^>0 ⦄ ⟩
  α ^ γ * α                     ≤.≡⟨⟩
  α ^ suc γ                     ∎
^-monoʳ-< α {β} {lim f} ((n , d) , ≤f) = begin-strict
  α ^ β                         <⟨ ^-monoʳ-< α (d , ≤f) ⟩
  α ^ f n                       ≤⟨ f≤l ⟩
  α ^ lim f                     ∎
```

然后容易推出 `_^` 的强增长性.

```agda
^-incrʳ-< : ∀ α β → ⦃ α > ⌜ 1 ⌝ ⦄ → β > ⌜ 1 ⌝ → α < α ^ β
^-incrʳ-< α β β>1 = begin-strict
  α                 ≈˘⟨ ^-identityʳ _ ⟩
  α ^ ⌜ 1 ⌝         <⟨ ^-monoʳ-< α β>1 ⟩
  α ^ β             ∎
```

**注意** 只有 `_^` 是强增长的, `^_` 不保证强增长. 我们会在下一章展示 `^_` 定义的迭代幂次会遇到不动点.

`_^` 的 ≤-单调性无法使用超限递归的相关引理, 需要用归纳法证明.

```agda
^-monoˡ-≤ : ∀ α → ≤-monotonic (_^ α)
^-monoˡ-≤ zero            _   = ≤-refl
^-monoˡ-≤ (suc α) {β} {γ} β≤γ = begin-nonstrict
  β ^ suc α                     ≤.≡⟨⟩
  β ^ α * β                     ≤⟨ *-monoʳ-≤ _ β≤γ ⟩
  β ^ α * γ                     ≤⟨ *-monoˡ-≤ _ (^-monoˡ-≤ _ β≤γ) ⟩
  γ ^ α * γ                     ∎
^-monoˡ-≤ (lim f) {β} {γ} β≤γ = l≤ λ n → ≤f⇒≤l (^-monoˡ-≤ (f n) β≤γ)
```

`^_` 的弱增长性又是个特殊的性质, 它无法从 `^-monoˡ-≤` 推出, 但可以直接用归纳法证明.

```agda
^-incrˡ-≤ : ∀ α β → ⦃ β > ⌜ 1 ⌝ ⦄ → α ≤ β ^ α
^-incrˡ-≤ zero    β         = ≤s
^-incrˡ-≤ (suc α) β ⦃ β>1 ⦄  = begin-nonstrict
  suc α                       ≤⟨ s≤s (^-incrˡ-≤ α β) ⟩
  suc (β ^ α)                 ≤.≡⟨⟩
  β ^ α + ⌜ 1 ⌝               ≤⟨ +-monoʳ-≤ (β ^ α) (<⇒s≤ (^>0 ⦃ <⇒≤ β>1 ⦄)) ⟩
  β ^ α + β ^ α               ≈˘⟨ α*2≈α+α _ ⟩
  β ^ α * ⌜ 2 ⌝               ≤⟨ *-monoʳ-≤ (β ^ α) (<⇒s≤ β>1) ⟩
  β ^ α * β                   ≤.≡⟨⟩
  β ^ suc α                   ∎
^-incrˡ-≤ (lim f) β         = l≤l λ n → begin-nonstrict
  f n                         ≤⟨ ^-incrˡ-≤ (f n) β ⟩
  β ^ f n                     ∎
```

幂运算的合同性只有半边是无条件的, 另一半要求底数不为零.

```agda
^-congʳ : RightCongruent _^_
^-congʳ {α} (≤ , ≥) = ^-monoˡ-≤ α ≤ , ^-monoˡ-≤ α ≥

^-congˡ : ∀ {α} → ⦃ α ≥ ⌜ 1 ⌝ ⦄ → (α ^_) Preserves _≈_ ⟶ _≈_
^-congˡ {α} (≤ , ≥) = ^-monoʳ-≤ α ≤ , ^-monoʳ-≤ α ≥
```

### 代数结构

**定理** 底数不为零的 `^_` 是加法半群到乘法半群的群同态, 也是加法幺半群到乘法幺半群的群同态.

```agda
^-semigroup-morphism : ∀ {α} → ⦃ α ≥ ⌜ 1 ⌝ ⦄ → (α ^_) Is +-semigroup -Semigroup⟶ *-semigroup
^-semigroup-morphism = record
  { ⟦⟧-cong = ^-congˡ
  ; ∙-homo  = ^-distribˡ-+-* _
  }

^-monoid-morphism : ∀ {α} → ⦃ α ≥ ⌜ 1 ⌝ ⦄ → (α ^_) Is +-0-monoid -Monoid⟶ *-1-monoid
^-monoid-morphism = record
  { sm-homo = ^-semigroup-morphism
  ; ε-homo  = ≈-refl
  }
```

## 序数嵌入

**定理** 右侧运算 `+_`, `*_`, `^_` 都是序数嵌入.

```agda
+-normal : ∀ α → normal (α +_)
+-normal α = +-monoʳ-≤ α , +-monoʳ-< α , rec-ct

*-normal : ∀ α → ⦃ α > ⌜ 0 ⌝ ⦄ → normal (α *_)
*-normal α = *-monoʳ-≤ α , *-monoʳ-< α , rec-ct

^-normal : ∀ α → ⦃ α > ⌜ 1 ⌝ ⦄ → normal (α ^_)
^-normal α ⦃ α>1 ⦄ = ^-monoʳ-≤ α ⦃ <⇒≤ α>1 ⦄ , ^-monoʳ-< α , rec-ct
```

**注意** 左侧运算 `_+`, `_*`, `_^` 不是序数嵌入.

## 保良构性

**定理** 右侧运算 `+_`, `*_`, `^_` 都保良构.

```agda
+-wfp : ∀ {α} → WellFormed α → wf-preserving (α +_)
+-wfp wfα = rec-wfp wfα s≤s (λ- <s) id

*-wfp : ∀ {α} → WellFormed α → α > ⌜ 0 ⌝ → wf-preserving (α *_)
*-wfp {α} wfα α>0 = rec-wfp tt (+-monoˡ-≤ α) (+-incrʳ-< α α>0) (λ wfx → +-wfp wfx wfα)

^-wfp : ∀ {α} → WellFormed α → ⦃ α > ⌜ 1 ⌝ ⦄ → wf-preserving (α ^_)
^-wfp {α} wfα {zero} _ = tt
^-wfp {α} wfα ⦃ α>1 ⦄ {suc β} wfβ = *-wfp (^-wfp wfα wfβ) (^>0 ⦃ <⇒≤ α>1 ⦄) wfα
^-wfp {α} wfα {lim f} (wfn , wrap mono) = ^-wfp wfα wfn , wrap λ m<n → ^-monoʳ-< α (mono m<n)
```

**注意** 左侧运算 `_+`, `_*`, `_^` 不保良构.

## 其他引理

**引理** 加法结合律和乘法结合律可以推广到任意有限元.

```agda
+-assoc-n : ∀ α n → α + α * ⌜ n ⌝ ≈ α * ⌜ n ⌝ + α
+-assoc-n α zero      = ≈-sym (+-identityˡ α)
+-assoc-n α (suc n)   = begin-eq
  α + α * suc ⌜ n ⌝     ≤.≡⟨⟩
  α + (α * ⌜ n ⌝ + α)   ≈˘⟨ +-assoc _ _ _ ⟩
  α + α * ⌜ n ⌝ + α     ≈⟨ +-congʳ (+-assoc-n α n) ⟩
  α * suc ⌜ n ⌝ + α     ∎

*-assoc-n : ∀ α n → α * α ^ ⌜ n ⌝ ≈ α ^ ⌜ n ⌝ * α
*-assoc-n α zero      = begin-eq
  α * ⌜ 1 ⌝             ≈⟨ *-identityʳ α ⟩
  α                     ≈˘⟨ *-identityˡ α ⟩
  ⌜ 1 ⌝ * α             ∎
*-assoc-n α (suc n)   = begin-eq
  α * α ^ suc ⌜ n ⌝     ≤.≡⟨⟩
  α * (α ^ ⌜ n ⌝ * α)   ≈˘⟨ *-assoc _ _ _ ⟩
  α * α ^ ⌜ n ⌝ * α     ≈⟨ *-congʳ (*-assoc-n α n) ⟩
  α ^ suc ⌜ n ⌝ * α     ∎
```

以下引理会在后续章节处理 `ω` 指数塔的时候用到, 其证明是迄今为止各种引理的集大成.

**引理** ω的幂对加法有吸收律.

```agda
ω^-absorb-+ : ∀ {α β} → ⦃ WellFormed β ⦄ → α < β → ω ^ α + ω ^ β ≈ ω ^ β
ω^-absorb-+ {α} {suc β} α<β =
    l≤ (λ n →                   begin-nonstrict
      ω ^ α + ω ^ β * ⌜ n ⌝     ≤⟨ +-monoˡ-≤ _ (^-monoʳ-≤ ω (<s⇒≤ α<β)) ⟩
      ω ^ β + ω ^ β * ⌜ n ⌝     ≈⟨ +-assoc-n _ _ ⟩
      ω ^ β * ⌜ n ⌝ + ω ^ β     ≤.≡⟨⟩
      ω ^ β * suc ⌜ n ⌝         ≤⟨ *-monoʳ-≤ _ (<⇒≤ (n<ω {suc n})) ⟩
      ω ^ β * ω                 ≤.≡⟨⟩
      ω ^ suc β                 ∎)
  , l≤ (λ n →                   begin-nonstrict
      ω ^ β * ⌜ n ⌝             ≤⟨ +-incrˡ-≤ _ _ ⟩
      ω ^ α + ω ^ β * ⌜ n ⌝     ≤⟨ +-monoʳ-≤ _ (*-monoʳ-≤ _ (<⇒≤ n<ω)) ⟩
      ω ^ α + ω ^ β * ω         ≤.≡⟨⟩
      ω ^ α + ω ^ suc β         ∎)
ω^-absorb-+ {α} {lim f} ⦃ wf ⦄ α<l with ∃[n]<fn α<l
... | (m , α<fm) = l≤ helper , l≤ λ n → ≤f⇒≤l (+-incrˡ-≤ _ _) where
  helper : ∀ n → ω ^ α + ω ^ f n ≤ lim (λ n → ω ^ f n)
  helper n with (ℕ.<-cmp m n)
  ... | tri< m<n _ _  = ≤f⇒≤l ( begin-nonstrict
        ω ^ α + ω ^ f n         ≤⟨ proj₁ (ω^-absorb-+ {β = f n} α<fn) ⟩
        ω ^ f n                 ∎)
    where α<fn = let (_ , wrap mono) = wf in <-trans α<fm (mono m<n)
  ... | tri≈ _ refl _ = ≤f⇒≤l ( begin-nonstrict
        ω ^ α + ω ^ f n         ≤⟨ proj₁ (ω^-absorb-+ α<fm) ⟩
        ω ^ f n                 ∎)
  ... | tri> _ _ n<m  = ≤f⇒≤l ( begin-nonstrict
        ω ^ α + ω ^ f n         ≤⟨ +-monoʳ-≤ _ (^-monoʳ-≤ _ fn≤fm) ⟩
        ω ^ α + ω ^ f m         ≤⟨ proj₁ (ω^-absorb-+ α<fm) ⟩
        ω ^ f m                 ∎)
    where fn≤fm = let (_ , wrap mono) = wf in <⇒≤ (mono n<m)
```
