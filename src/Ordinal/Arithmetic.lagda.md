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
{-# OPTIONS --experimental-lossy-unification #-}

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
open import Data.Unit using (tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (id)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; refl; sym; cong)
```

本章需要 `≤-Reasoning` 和 `≡-Reasoning` 两套推理. 由于 `step-≡` 对应的 syntax 重名, 我们加上短模块名进行区分: `≡.≡⟨⟩`, `≤.≡⟨⟩`.

```agda
open module ≡ = Eq.≡-Reasoning renaming
  ( begin_          to begin-propeq_
  ; _∎              to _◼)
open module ≤ = Ordinal.≤-Reasoning renaming
  ( begin-equality_ to begin-eq_
  ; begin_          to begin-nonstrict_)
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
⌜⌝+⌜⌝≡⌜+⌝ : ∀ m n → ⌜ m ⌝ + ⌜ n ⌝ ≡ ⌜ m ℕ.+ n ⌝
⌜⌝+⌜⌝≡⌜+⌝ m ℕ.zero    = begin-propeq
  ⌜ m ⌝ + ⌜ ℕ.zero ⌝    ≡.≡⟨⟩
  ⌜ m ⌝                 ≡.≡˘⟨ cong ⌜_⌝ (ℕ.+-identityʳ m) ⟩
  ⌜ m ℕ.+ ℕ.zero ⌝      ◼
⌜⌝+⌜⌝≡⌜+⌝ m (ℕ.suc n) = begin-propeq
  ⌜ m ⌝ + suc ⌜ n ⌝     ≡.≡⟨⟩
  suc (⌜ m ⌝ + ⌜ n ⌝)   ≡.≡⟨ cong suc (⌜⌝+⌜⌝≡⌜+⌝ m n) ⟩
  suc ⌜ m ℕ.+ n ⌝       ≡.≡˘⟨ cong ⌜_⌝ (ℕ.+-suc m n) ⟩
  ⌜ m ℕ.+ ℕ.suc n ⌝     ◼
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
+-identityʳ = λ _ → ≈-refl

+-identity : Identity ⌜ 0 ⌝ _+_
+-identity = +-identityˡ , +-identityʳ
```

序数加法没有交换律, 反例如下.

```agda
_ : ω + ⌜ 1 ⌝ ≡ suc ω
_ = refl

1+ω≈ω : ⌜ 1 ⌝ + ω ≈ ω
1+ω≈ω = l≤ (λ n → ≤f⇒≤l (begin-nonstrict
          ⌜ 1 ⌝ + ⌜ n ⌝           ≤.≡⟨ ⌜⌝+⌜⌝≡⌜+⌝ 1 n ⟩
          ⌜ 1 ℕ.+ n ⌝             ∎))
      , l≤ (λ n → ≤f⇒≤l (begin-nonstrict
          ⌜ n ⌝ ≤⟨ ≤s ⟩ suc ⌜ n ⌝ ≤.≡˘⟨ ⌜⌝+⌜⌝≡⌜+⌝ 1 n ⟩
          ⌜ 1 ⌝ + ⌜ n ⌝           ∎))
```

### 增长性, 单调性与合同性

由上一章超限递归的基本性质立即得到序数加法的增长性和单调性.

```agda
module _ (α) where

  +-incrˡ-≤ : ≤-increasing (_+ α)
  +-incrˡ-≤ β = rec-from-incr-≤ α (λ _ → ≤s) β

  +-incrʳ-≤ : ≤-increasing (α +_)
  +-incrʳ-≤ β = rec-by-incr-≤ s≤s (λ _ → <s) β

  +-incrˡ-< : α > ⌜ 0 ⌝ → <-increasing (_+ α)
  +-incrˡ-< >z β = rec-from-incr-< >z s≤s (λ _ → <s) β

  +-monoˡ-≤ : ≤-monotonic (_+ α)
  +-monoˡ-≤ ≤ = rec-from-mono-≤ α s≤s ≤

  +-monoʳ-≤ : ≤-monotonic (α +_)
  +-monoʳ-≤ ≤ = rec-by-mono-≤ s≤s (λ _ → ≤s) ≤

  +-monoʳ-< : <-monotonic (α +_ )
  +-monoʳ-< < = rec-by-mono-< s≤s (λ _ → <s) <
```

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
⌜⌝*⌜⌝≡⌜*⌝ m ℕ.zero      = begin-propeq
  ⌜ m ⌝ * zero            ≡.≡˘⟨ cong ⌜_⌝ (ℕ.*-zeroʳ m) ⟩
  ⌜ m ℕ.* ℕ.zero ⌝        ◼
⌜⌝*⌜⌝≡⌜*⌝ m (ℕ.suc n)   = begin-propeq
  ⌜ m ⌝ * suc ⌜ n ⌝       ≡.≡⟨⟩
  ⌜ m ⌝ * ⌜ n ⌝ + ⌜ m ⌝   ≡.≡⟨ cong (_+ ⌜ m ⌝) (⌜⌝*⌜⌝≡⌜*⌝ m n) ⟩
  ⌜ m ℕ.* n ⌝ + ⌜ m ⌝     ≡.≡⟨ ⌜⌝+⌜⌝≡⌜+⌝ (m ℕ.* n) m ⟩
  ⌜ m ℕ.* n ℕ.+ m ⌝       ≡.≡⟨ cong ⌜_⌝ (ℕ.+-comm (m ℕ.* n) m) ⟩
  ⌜ m ℕ.+ m ℕ.* n ⌝       ≡.≡˘⟨ cong ⌜_⌝ (ℕ.*-suc m n) ⟩
  ⌜ m ℕ.* ℕ.suc n ⌝       ◼
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
*-identityˡ (lim f) = l≤ (λ n →       begin-nonstrict
                        ⌜ 1 ⌝ * f n   ≈⟨ *-identityˡ (f n) ⟩
                        f n           ≤⟨ f≤l ⟩
                        lim f         ∎)
                    , l≤ (λ n →       begin-nonstrict
                        f n           ≈˘⟨ *-identityˡ (f n) ⟩
                        ⌜ 1 ⌝ * f n   ≤⟨ f≤l ⟩
                        ⌜ 1 ⌝ * lim f ∎)

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

首先是从右侧乘法的 ≤-单调性推出左侧乘法的弱增长性.

```agda
*-monoʳ-≤ : ∀ α → ≤-monotonic (α *_)
*-monoʳ-≤ α = rec-by-mono-≤ (+-monoˡ-≤ α) (+-incrˡ-≤ α)

*-incrˡ-≤ : ∀ α → α ≥ ⌜ 1 ⌝ → ≤-increasing (_* α)
*-incrˡ-≤ α α≥1 β = begin-nonstrict
  β               ≈˘⟨ *-identityʳ β ⟩
  β * ⌜ 1 ⌝       ≤⟨ *-monoʳ-≤ β α≥1 ⟩
  β * α           ∎
```

然后, 类似地, 从右侧乘法的 <-单调性推出左侧乘法的强增长性.

```agda
*-monoʳ-< : ∀ α → α > ⌜ 0 ⌝ → <-monotonic (α *_)
*-monoʳ-< α α>0 = rec-by-mono-< (+-monoˡ-≤ α) (+-incrˡ-< α α>0)

*-incrˡ-< : ∀ α β → α > ⌜ 0 ⌝ → β > ⌜ 1 ⌝ → α < α * β
*-incrˡ-< α β α>0 β>1 = begin-strict
  α                     ≈˘⟨ *-identityʳ α ⟩
  α * ⌜ 1 ⌝             <⟨ *-monoʳ-< α α>0 β>1 ⟩
  α * β                 ∎
```

接着是从左侧乘法的 ≤-单调性推出右侧乘法的弱增长性. 注意前者已经无法使用超限递归的相关引理了, 需要用归纳法证明.

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

*-incrʳ-≤ : ∀ α → α ≥ ⌜ 1 ⌝ → ≤-increasing (α *_)
*-incrʳ-≤ α α≥1 β = begin-nonstrict
  β                 ≈˘⟨ *-identityˡ β ⟩
  ⌜ 1 ⌝ * β         ≤⟨ *-monoˡ-≤ β α≥1 ⟩
  α * β             ∎
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

**定理** 右侧运算 `+_`, `*_`, `^_` 都是序数嵌入.

```agda
+-normal : ∀ α → normal (α +_)
+-normal α = +-monoʳ-≤ α , +-monoʳ-< α , rec-ct

*-normal : ∀ α → α > ⌜ 0 ⌝ → normal (α *_)
*-normal α α>0 = *-monoʳ-≤ α , *-monoʳ-< α α>0 , rec-ct
```

**注意** 左侧运算 `_+`, `_*`, `_^` 不是序数嵌入.

## 保良构性

**定理** 右侧运算 `+_`, `*_`, `^_` 都保良构.

```agda
+-wfp : ∀ {α} → wellFormed α → wf-preserving (α +_)
+-wfp wfα = rec-wfp wfα s≤s (λ _ → <s) id

*-wfp : ∀ {α} → wellFormed α → α > ⌜ 0 ⌝ → wf-preserving (α *_)
*-wfp {α} wfα α>0 = rec-wfp tt (+-monoˡ-≤ α) (+-incrˡ-< α α>0) (λ wfx → +-wfp wfx wfα)
```

**注意** 左侧运算 `_+`, `_*`, `_^` 不保良构.
