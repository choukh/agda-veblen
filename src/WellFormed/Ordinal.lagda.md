---
title: Agda大序数(2-1) 序数的定义
zhihu-tags: Agda, 序数, 大数数学
---

# Agda大序数(2-1) 序数的定义

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
open import NonWellFormed.Ordinal as ord
  using (zero; suc; lim) renaming (Ord to ord) public
open import NonWellFormed.WellFormed as ord using (WellFormed) public

open import Data.Unit using (tt)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (_∘_; it)
open import Level using (0ℓ)
open import Relation.Nullary using (¬_)
open import Relation.Binary using (Monotonic₁)
open import Relation.Binary using (Rel; _⇒_)
open import Relation.Binary.Definitions
  using (Reflexive; Symmetric; Transitive; Trans; Irreflexive; Asymmetric)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
```

## 良构序数

```agda
record Ord : Set where
  constructor wf
  field
    nwf : ord
    ⦃ wellFormed ⦄ : WellFormed nwf

open Ord
```

```agda
infix 4 _≤_ _≥_ _≰_ _≱_

_≤_ : Rel Ord 0ℓ
wf α ≤ wf β = α ord.≤ β

_≥_ : Rel Ord 0ℓ
α ≥ β = β ≤ α

_≰_ : Rel Ord 0ℓ
α ≰ β = ¬ α ≤ β

_≱_ : Rel Ord 0ℓ
α ≱ β = ¬ β ≤ α
```

```agda
infix 4 _≈_ _≉_

_≈_ : Rel Ord 0ℓ
wf α ≈ wf β = α ord.≈ β

_≉_ : Rel Ord 0ℓ
α ≉ β = ¬ α ≈ β
```

```agda
infix 4 _<_ _>_ _≮_ _≯_

_<_ : Rel Ord 0ℓ
wf α < wf β = α ord.< β

_>_ : Rel Ord 0ℓ
α > β = β < α

_≮_ : Rel Ord 0ℓ
α ≮ β = ¬ α < β

_≯_ : Rel Ord 0ℓ
α ≯ β = ¬ β < α
```

```agda
pattern Zero = wf zero

Suc : Ord → Ord
Suc (wf α) = wf (suc α)

Suc-injective : ∀ {α β} → Suc α ≡ Suc β → α ≡ β
Suc-injective refl = refl
```

```agda
monoSequence : (ℕ → Ord) → Set
monoSequence = Monotonic₁ ℕ._<_ _<_

record MonoSequence (f : ℕ → Ord) : Set where
  constructor wrap
  field unwrap : monoSequence f

Lim : ∀ f → ⦃ MonoSequence f ⦄ → Ord
Lim f ⦃ wrap mono ⦄ = wf (lim (λ n → nwf (f n))) ⦃ wfl ⦄ where
  wfl = (λ {n} → wellFormed (f n)) , ord.wrap mono
```

```agda
lift : ∀ (f : ℕ → ord) → ⦃ ∀ {n} → WellFormed (f n) ⦄ → (ℕ → Ord)
lift f n = wf (f n)

instance
  lift-mono : ∀ {f : ℕ → ord} ⦃ wf : WellFormed (lim f) ⦄ → MonoSequence (lift f ⦃ proj₁ wf ⦄)
  lift-mono = wrap (ord.MonoSequence.unwrap (proj₂ it))
```

```agda
open import NonWellFormed.Ordinal using
  ( z≤; l≤; ≤s; s∸≤; s≤s; ≤f⇒≤l; l≤l; f≤l
  ; s≈s; l≈l; l≈ls
  ; z<s; <s; s<s; <f⇒<l
  ; <⇒≤; <⇒≱
  ; <⇒s≤; s≤⇒<; ≤⇒<s; <s⇒≤
  ) public
```

```agda
open import NonWellFormed.Ordinal using
  ( ≤-refl; ≤-trans
  ; ≈-refl; ≈-sym; ≈-trans
  ; <-irrefl-≈; <-trans; <-asym
  ; <-≤-trans; ≤-<-trans
  ) public
```

```agda
open import Relation.Binary.Structures (_≈_)
  using (IsEquivalence; IsPreorder; IsPartialOrder; IsStrictPartialOrder)

≈-isEquivalence : IsEquivalence
≈-isEquivalence = record
  { refl  = ≈-refl
  ; sym   = ≈-sym
  ; trans = ≈-trans
  }

≤-isPreorder : IsPreorder _≤_
≤-isPreorder = record
  { isEquivalence = ≈-isEquivalence
  ; reflexive = proj₁
  ; trans = ≤-trans
  }

≤-isPartialOrder : IsPartialOrder _≤_
≤-isPartialOrder = record
  { isPreorder = ≤-isPreorder
  ; antisym = λ ≤ ≥ → ≤ , ≥
  }

<-isStrictPartialOrder : IsStrictPartialOrder _<_
<-isStrictPartialOrder = record
  { isEquivalence = ≈-isEquivalence
  ; irrefl = <-irrefl-≈
  ; trans = <-trans
  ; <-resp-≈ = (λ (β≤γ , _) α<β → <-≤-trans α<β β≤γ) ,
                λ (_ , α≤β) β<γ → ≤-<-trans α≤β β<γ
  }
```

```agda
≤-respʳ-≈ = IsPartialOrder.≤-respʳ-≈ ≤-isPartialOrder
≤-respˡ-≈ = IsPartialOrder.≤-respˡ-≈ ≤-isPartialOrder
≤-resp-≈ = IsPartialOrder.≤-resp-≈ ≤-isPartialOrder

<-respʳ-≈ = IsStrictPartialOrder.<-respʳ-≈ <-isStrictPartialOrder
<-respˡ-≈ = IsStrictPartialOrder.<-respˡ-≈ <-isStrictPartialOrder
<-resp-≈ = IsStrictPartialOrder.<-resp-≈ <-isStrictPartialOrder
```

```agda
module ≤-Reasoning where
  open import Relation.Binary.Reasoning.Base.Triple
    ≤-isPreorder
    <-trans
    <-resp-≈
    <⇒≤
    <-≤-trans
    ≤-<-trans
    public
```

```agda
open Relation.Binary using (Setoid)

OrdSetoid : Setoid 0ℓ 0ℓ
OrdSetoid = record
  { Carrier = Ord
  ; _≈_ = _≈_
  ; isEquivalence = ≈-isEquivalence
  }
```
