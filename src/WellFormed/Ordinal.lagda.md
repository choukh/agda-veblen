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
open import NonWellFormed.Ordinal as ord using (zero; suc; lim) renaming (Ord to ord)
open import NonWellFormed.WellFormed as ord using (MonoSequence; WellFormed; wrap)

open import Data.Unit using (tt)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (_∘_)
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
≡⇒≈ : _≡_ ⇒ _≈_
≡⇒≈ refl = ord.≈-refl

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ = ord.<⇒≤

<⇒≱ : _<_ ⇒ _≱_
<⇒≱ = ord.<⇒≱

≤⇒≯ : _≤_ ⇒ _≯_
≤⇒≯ = ord.≤⇒≯
```

```agda
≤-refl : Reflexive _≤_
≤-refl = ord.≤-refl

≤-trans : Transitive _≤_
≤-trans = ord.≤-trans

≈-refl : Reflexive _≈_
≈-refl = ord.≈-refl

≈-sym : Symmetric _≈_
≈-sym = ord.≈-sym

<-trans : Transitive _<_
<-trans = ord.<-trans
```

```agda
Zero : Ord
Zero = wf zero

Suc : Ord → Ord
Suc (wf α) = wf (suc α)
```

```agda
monoSequence : (ℕ → Ord) → Set
monoSequence = Monotonic₁ ℕ._<_ _<_

Lim : ∀ f → monoSequence f → Ord
Lim f mf = wf (ord.lim (λ n → nwf (f n))) ⦃ wfl ⦄ where
  wfl = (λ {n} → wellFormed (f n)) , wrap mf
```

```agda
z≤ : ∀ α → Zero ≤ α
z≤ _ = ord.z≤
```

```agda
≤s : ∀ {α} → α ≤ Suc α
≤s = ord.≤s

s≤s : ∀ {α β} → α ≤ β → Suc α ≤ Suc β
s≤s = ord.s≤s
```

```agda
≤f⇒≤l : ∀ {α f n} {mf : monoSequence f} → α ≤ f n → α ≤ Lim f mf
≤f⇒≤l = ord.≤f⇒≤l

l≤l : ∀ {f g} {mf : monoSequence f} {mg : monoSequence g}
  → (∀ n → f n ≤ g n) → Lim f mf ≤ Lim g mg
l≤l = ord.l≤l

f≤l : ∀ f n (mf : monoSequence f) → f n ≤ Lim f mf
f≤l _ _ _ = ord.f≤l
```

```agda
s≈s : ∀ {α β} → α ≈ β → Suc α ≈ Suc β
s≈s = ord.s≈s

l≈l : ∀ {f g} {mf : monoSequence f} {mg : monoSequence g}
  → (∀ {n} → f n ≈ g n) → Lim f mf ≈ Lim g mg
l≈l = ord.l≈l

l≈ls : ∀ {f} {mf : monoSequence f}
  → f 0 ≤ f 1 → Lim f mf ≈ Lim (f ∘ ℕ.suc) (λ ≤ → mf (ℕ.s≤s ≤))
l≈ls = ord.l≈ls
```

```agda
z<s : ∀ {α} → Zero < Suc α
z<s = ord.z<s

<s : ∀ {α} → α < Suc α
<s = ord.<s

s<s : ∀ {α β} → α < β → Suc α < Suc β
s<s = ord.s<s

<f⇒<l : ∀ {α f n} {mf : monoSequence f} → α < f n → α < Lim f mf
<f⇒<l = ord.<f⇒<l
```

```agda
<⇒s≤ : ∀ {α β} → α < β → Suc α ≤ β
<⇒s≤ = ord.<⇒s≤

s≤⇒< : ∀ {α β} → Suc α ≤ β → α < β
s≤⇒< = ord.s≤⇒<

≤⇒<s : ∀ {α β} → α ≤ β → α < Suc β
≤⇒<s = ord.≤⇒<s

<s⇒≤ : ∀ {α β} → α < Suc β → α ≤ β
<s⇒≤ = ord.<s⇒≤
```

```agda
open import Relation.Binary.Structures (_≈_)
  using (IsEquivalence; IsPreorder; IsPartialOrder; IsStrictPartialOrder)

≈-isEquivalence : IsEquivalence
≈-isEquivalence = record
  { refl  = ord.≈-refl
  ; sym   = ord.≈-sym
  ; trans = ord.≈-trans
  }

≤-isPreorder : IsPreorder _≤_
≤-isPreorder = record
  { isEquivalence = ≈-isEquivalence
  ; reflexive = proj₁
  ; trans = ord.≤-trans
  }

≤-isPartialOrder : IsPartialOrder _≤_
≤-isPartialOrder = record
  { isPreorder = ≤-isPreorder
  ; antisym = λ ≤ ≥ → ≤ , ≥
  }

<-isStrictPartialOrder : IsStrictPartialOrder _<_
<-isStrictPartialOrder = record
  { isEquivalence = ≈-isEquivalence
  ; irrefl = ord.<-irrefl-≈
  ; trans = ord.<-trans
  ; <-resp-≈ = (λ (β≤γ , _) α<β → ord.<-≤-trans α<β β≤γ) ,
                λ (_ , α≤β) β<γ → ord.≤-<-trans α≤β β<γ
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
    ord.<-trans
    <-resp-≈
    ord.<⇒≤
    ord.<-≤-trans
    ord.≤-<-trans
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
