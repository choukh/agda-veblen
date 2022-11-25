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
open import Data.Nat as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕ
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; ∃-syntax)
open import Function using (_∘_; _↩_)
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
<ω⊎≥ω α = ord.<ω⊎≥ω (inudctive α)
```
