---
title: Agda大序数(2-2) 良构序数
zhihu-tags: Agda, 序数, 大数数学
---

# Agda大序数(2-2) 良构序数

> 交流Q群: 893531731  
> 目录: [WellFormed.html](https://choukh.github.io/agda-lvo/WellFormed.html)  
> 本文源码: [WellFormed.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/WellFormed/WellFormed.lagda.md)  
> 高亮渲染: [WellFormed.html](https://choukh.github.io/agda-lvo/WellFormed.WellFormed.html)  
> 如果你在知乎看到本文: 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

```agda
{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --overlapping-instances #-}

module WellFormed.WellFormed where
```

```agda
open import WellFormed.Ordinal
open WellFormed.Ordinal.≤-Reasoning
open import NonWellFormed.WellFormed as ord using (WellFormed; ⌜_⌝-wellFormed; ω-wellFormed)

open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat as ℕ using (ℕ; zero; suc; z≤n)
open import Data.Nat.Properties as ℕ using (m≤n⇒m<n∨m≡n)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; ∃-syntax)
open import Function using (_∘_; _↩_; it)
open import Relation.Binary using (Monotonic₁)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong)
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
n≤ω : ∀ {n} → ⌜ n ⌝ ≤ ω
n≤ω = ord.n≤ω

z<ω : Zero < ω
z<ω = ord.z<ω

s<ω : ∀ α → α < ω → Suc α < ω
s<ω _ = ord.s<ω

n<ω : ∀ {n} → ⌜ n ⌝ < ω
n<ω = ord.n<ω
```

```agda
fn<fsn : ∀ {f n} → ⦃ MonoSequence f ⦄ → f n < f (suc n)
fn<fsn = ord.fn<fsn
```

```agda
⌜n⌝≤fn : ∀ {f n} → ⦃ MonoSequence f ⦄ → ⌜ n ⌝ ≤ f n
⌜n⌝≤fn = ord.⌜n⌝≤fn
```

```agda
ω≤l : ∀ {f} ⦃ mf : MonoSequence f ⦄ → ω ≤ Lim f
ω≤l = ord.ω≤l
```

```agda
⌜⌝-injective : ∀ {m n} → ⌜ m ⌝ ≡ ⌜ n ⌝ → m ≡ n
⌜⌝-injective eq = ord.⌜⌝-injective (cong inudctive eq)
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
z<l : ∀ {f} ⦃ mf : MonoSequence f ⦄ → Zero < Lim f
z<l = ord.z<l

f<l : ∀ {f n} ⦃ mf : MonoSequence f ⦄ → f n < Lim f
f<l = ord.f<l
```

```agda
∃[n]<fn : ∀ α {f} ⦃ mf : MonoSequence f ⦄ → α < Lim f → ∃[ n ] α < f n
∃[n]<fn _ = ord.∃[n]<fn
```

```agda
module _ {f g} ⦃ mf : MonoSequence f ⦄ ⦃ mg : MonoSequence g ⦄ where
  ∃[m]fn<gm : Lim f ≤ Lim g → ∀ n → ∃[ m ] f n < g m
  ∃[m]fn<gm = ord.∃[m]fn<gm
```

```agda
<l⇒s<l : ∀ α {f} ⦃ mf : MonoSequence f ⦄ → α < Lim f → Suc α < Lim f
<l⇒s<l _ = ord.<l⇒s<l
```

```agda
l≤s⇒l≤ : ∀ {f} α ⦃ mf : MonoSequence f ⦄ → Lim f ≤ Suc α → Lim f ≤ α
l≤s⇒l≤ _ = ord.l≤s⇒l≤
```

```agda
ω≤s⇒ω≤ : ∀ α → ω ≤ Suc α → ω ≤ α
ω≤s⇒ω≤ _ = ord.ω≤s⇒ω≤
```

```agda
≢z⇒>z : ∀ {α} → α ≢ Zero → α > Zero
≢z⇒>z ≢ = ord.≢z⇒>z (≢ ∘ ≡z⇒≡Z)
```

```agda
≈z⇒≡z : ∀ {α} → α ≈ Zero → α ≡ Zero
≈z⇒≡z = ≡z⇒≡Z ∘ ord.≈z⇒≡z
```

```agda
≤z⇒≡z : ∀ {α} → α ≤ Zero → α ≡ Zero
≤z⇒≡z = ≡z⇒≡Z ∘ ord.≤z⇒≡z
```

```agda
≡z⊎>z : ∀ α → α ≡ Zero ⊎ α > Zero
≡z⊎>z (wf α) with ord.≡z⊎>z α
... | inj₁ ≡ = inj₁ (≡z⇒≡Z ≡)
... | inj₂ > = inj₂ >
```

```agda
<ω⊎≥ω : ∀ α → α < ω ⊎ α ≥ ω
<ω⊎≥ω (wf α) = ord.<ω⊎≥ω α
```
