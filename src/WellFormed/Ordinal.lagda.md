---
title: Agda大序数(2-1) 序数record类型
zhihu-tags: Agda, 序数, 大数数学
---

# Agda大序数(2-1) 序数record类型

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
open import NonWellFormed.WellFormed as ord
  using (WellFormed; ⌜_⌝-wellFormed; ω-wellFormed)
open import NonWellFormed.WellFormed using (wf⇒wf; wf⇒mono) public

open import Data.Unit using (tt) public
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; ∃-syntax)
open import Function using (_∘_; _↩_; it)
open import Level using (0ℓ)
open import Relation.Nullary using (¬_)
open import Relation.Binary using (Monotonic₁)
open import Relation.Binary using (Rel; _⇒_)
open import Relation.Binary.Definitions
  using (Reflexive; Symmetric; Transitive; Trans; Irreflexive; Asymmetric)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong)
```

## 良构序数

```agda
record Ord : Set where
  constructor wf
  field
    nwf : ord
    ⦃ wellFormed ⦄ : WellFormed nwf
open Ord public
```

```agda
lift : ∀ (f : ℕ → ord) → ⦃ ∀ {n} → WellFormed (f n) ⦄ → (ℕ → Ord)
lift f n = wf (f n)

dip : (ℕ → Ord) → (ℕ → ord)
dip f = nwf ∘ f
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
wf-cong-≡-≈ : ∀ α β ⦃ wfα : WellFormed α ⦄ ⦃ wfβ : WellFormed β ⦄ → α ≡ β → wf α ≈ wf β
wf-cong-≡-≈ α β refl = ord.≈-refl

wf-cong-≈-≈ : ∀ α β ⦃ wfα : WellFormed α ⦄ ⦃ wfβ : WellFormed β ⦄ → α ord.≈ β → wf α ≈ wf β
wf-cong-≈-≈ α β ≈ = ≈
```

```agda
pattern Zero = wf zero

≡z⇒≡Z : ∀ {α} ⦃ wfα : WellFormed α ⦄ → α ≡ zero → wf α ≡ Zero
≡z⇒≡Z refl = refl

≡Z⇒≡z : ∀ α ⦃ wfα : WellFormed α ⦄ → wf α ≡ Zero → α ≡ zero
≡Z⇒≡z α refl = refl
```

```agda
Suc : Ord → Ord
Suc (wf α) = wf (suc α)

Suc-injective : ∀ {α β} → Suc α ≡ Suc β → α ≡ β
Suc-injective refl = refl
```

```agda
record MonoSequence (f : ℕ → Ord) : Set where
  constructor wrap
  field unwrap : Monotonic₁ ℕ._<_ _<_ f
open MonoSequence public

instance
  liftMono : ∀ {f : ℕ → ord} ⦃ wf : WellFormed (lim f) ⦄ → MonoSequence (lift f)
  liftMono = wrap (ord.MonoSequence.unwrap it)

  dipMono : ∀ {f} → ⦃ MonoSequence f ⦄ → ord.MonoSequence (dip f)
  dipMono ⦃ wrap mono ⦄ = ord.wrap mono

Lim : ∀ f → ⦃ MonoSequence f ⦄ → Ord
Lim f = wf (lim (dip f)) ⦃ wfl ⦄ where
  wfl = (λ {n} → wellFormed (f n)) , dipMono
```

```agda
_ : ∀ {α} → Zero ≤ α
_ = ord.z≤

_ : ∀ {α β} → α ≤ β → Suc α ≤ Suc β
_ = ord.s≤s

_ : ∀ {f g} ⦃ mf : MonoSequence f ⦄ ⦃ mg : MonoSequence g ⦄
  → (∀ n → f n ≤ g n) → Lim f ≤ Lim g
_ = ord.l≤l
```

```agda
open import NonWellFormed.Ordinal using
  ( z≤; l≤; ≤s; s∸≤; s≤s; ≤f⇒≤l; l≤l; f≤l
  ; s≈s; l≈l; l≈ls
  ; s≰z
  ; z<s; <s; s<s; <f⇒<l
  ; <⇒≤; <⇒≱
  ; ≤⇒≤s; <⇒s≤; s≤⇒<; ≤⇒<s; <s⇒≤
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
⌜_⌝ : ℕ → Ord
⌜ n ⌝ = wf ord.⌜ n ⌝ ⦃ ⌜ n ⌝-wellFormed ⦄

⌜⌝-monoSequence : MonoSequence ⌜_⌝
⌜⌝-monoSequence = liftMono ⦃ ω-wellFormed ⦄

ω : Ord
ω = Lim ⌜_⌝ ⦃ ⌜⌝-monoSequence ⦄
```

```agda
_ : ∀ {n} → ⌜ n ⌝ ≤ ω
_ = ord.n≤ω

_ : ∀ {f} ⦃ mf : MonoSequence f ⦄ → ω ≤ Lim f
_ = ord.ω≤l
```

```agda
open import NonWellFormed.WellFormed using
  ( n≤ω; z<ω ; s<ω; n<ω; ω≤l; ω≤s⇒ω≤
  ; z<l; f<l; <l⇒s<l; l≤s⇒l≤
  ; fn<fsn; ⌜n⌝≤fn; ∃[n]<fn; ∃[m]fn<gm
  ) public
```

```agda
⌜⌝-injective : ∀ {m n} → ⌜ m ⌝ ≡ ⌜ n ⌝ → m ≡ n
⌜⌝-injective eq = ord.⌜⌝-injective (cong nwf eq)
```

```agda
⌜⌝-surjective : ∀ α → α < ω → ∃[ n ] α ≡ ⌜ n ⌝
⌜⌝-surjective Zero _ = 0 , refl
⌜⌝-surjective (wf (suc α)) s<ω with ⌜⌝-surjective (wf α) (<-trans <s s<ω)
... | zero  , refl = 1 , refl
... | suc n , refl = suc (suc n) , refl
⌜⌝-surjective (wf (lim f)) l<ω = ⊥-elim (<⇒≱ l<ω ω≤l)
```

```agda
∃[<ω]wf↩ℕ : (∃[ α ] α < ω) ↩ ℕ
∃[<ω]wf↩ℕ = record
  { to        = λ (α , <ω) → proj₁ (⌜⌝-surjective α <ω)
  ; from      = λ n → ⌜ n ⌝ , n<ω
  ; to-cong   = λ{ refl → refl }
  ; from-cong = λ{ refl → refl }
  ; inverseˡ   = λ n → ⌜⌝-injective (sym (proj₂ (⌜⌝-surjective ⌜ n ⌝ n<ω)))
  }
```

```agda
≢z⇒>z : ∀ {α} → α ≢ Zero → α > Zero
≢z⇒>z ≢ = ord.≢z⇒>z (≢ ∘ ≡z⇒≡Z)

≈z⇒≡z : ∀ {α} → α ≈ Zero → α ≡ Zero
≈z⇒≡z = ≡z⇒≡Z ∘ ord.≈z⇒≡z

≤z⇒≡z : ∀ {α} → α ≤ Zero → α ≡ Zero
≤z⇒≡z = ≡z⇒≡Z ∘ ord.≤z⇒≡z

≡z⊎>z : ∀ α → α ≡ Zero ⊎ α > Zero
≡z⊎>z (wf α) with ord.≡z⊎>z α
... | inj₁ ≡ = inj₁ (≡z⇒≡Z ≡)
... | inj₂ > = inj₂ >
```

```agda
<ω⊎≥ω : ∀ α → α < ω ⊎ α ≥ ω
<ω⊎≥ω α = ord.<ω⊎≥ω (nwf α)
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
