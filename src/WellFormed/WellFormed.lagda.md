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
open import NonWellFormed.WellFormed as ord using (WellFormed; ⌜_⌝-wellFormed)

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
⌜ zero ⌝ = Zero
⌜ suc n ⌝ = wf ord.⌜ suc n ⌝ ⦃ ⌜ n ⌝-wellFormed ⦄

ord⌜_⌝ : ∀ n → inudctive ⌜ n ⌝ ≡ ord.⌜ n ⌝
ord⌜ zero ⌝ = refl
ord⌜ suc n ⌝ = refl

inudctive⌜_⌝ : ∀ n → ord.⌜ n ⌝ ≡ inudctive ⌜ n ⌝
inudctive⌜ n ⌝ = sym ord⌜ n ⌝

⌜⌝-monoSequence : MonoSequence ⌜_⌝
⌜⌝-monoSequence = wrap mono where
  mono : monoSequence ⌜_⌝
  mono {m} {n} rewrite ord⌜ m ⌝ | ord⌜ n ⌝
    = ord.MonoSequence.unwrap ord.⌜⌝-monoSequence

ω : Ord
ω = Lim ⌜_⌝ ⦃ ⌜⌝-monoSequence ⦄
```

```agda
n≤ω : ∀ n → ⌜ n ⌝ ≤ ω
n≤ω n = f≤l {n = n}

z<ω : Zero < ω
z<ω = begin-strict Zero <⟨ z<s ⟩ ⌜ 1 ⌝ ≤⟨ n≤ω 1 ⟩ ω ∎

s<ω : ∀ α → α < ω → Suc α < ω
s<ω α ((n , d) , ≤) rewrite ord⌜ n ⌝ =
  (suc n , inj₁ tt) , ≤-trans (s≤s ≤) s∸≤

n<ω : ∀ n → ⌜ n ⌝ < ω
n<ω zero = z<ω
n<ω (suc n) rewrite inudctive⌜ n ⌝ = s<ω ⌜ n ⌝ (n<ω n)
```

```agda
fn<fsn : ∀ {f n} → ⦃ MonoSequence f ⦄ → f n < f (suc n)
fn<fsn ⦃ wrap mono ⦄ = mono (ℕ.s≤s ℕ.≤-refl)
```

```agda
⌜n⌝≤fn : ∀ {f} n → ⦃ MonoSequence f ⦄ → ⌜ n ⌝ ≤ f n
⌜n⌝≤fn zero = z≤
⌜n⌝≤fn {f} (suc n) rewrite inudctive⌜ n ⌝ = begin
  Suc ⌜ n ⌝         ≤⟨ s≤s (⌜n⌝≤fn n) ⟩
  Suc (f n)         ≤⟨ <⇒s≤ fn<fsn ⟩
  f (suc n)         ∎
```

```agda
ω≤l : ∀ {f} ⦃ mf : MonoSequence f ⦄ → ω ≤ Lim f
ω≤l = l≤ (λ n → ≤f⇒≤l (⌜n⌝≤fn n))
```

```agda
⌜⌝-injective : ∀ {m n} → ⌜ m ⌝ ≡ ⌜ n ⌝ → m ≡ n
⌜⌝-injective {m} {n} eq = ord.⌜⌝-injective helper where
  helper : ord.⌜ m ⌝ ≡ ord.⌜ n ⌝
  helper rewrite inudctive⌜ m ⌝ | inudctive⌜ n ⌝ = cong inudctive eq
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
  ; from      = λ n → ⌜ n ⌝ , n<ω n
  ; to-cong   = λ{ refl → refl }
  ; from-cong = λ{ refl → refl }
  ; inverseˡ   = λ n → ⌜⌝-injective (sym (proj₂ (⌜⌝-surjective ⌜ n ⌝ (n<ω n))))
  }
```

```agda
z<l : ∀ {f} ⦃ mf : MonoSequence f ⦄ → Zero < Lim f
z<l {f} = <-≤-trans z<ω ω≤l

f<l : ∀ {f n} ⦃ mf : MonoSequence f ⦄ → f n < Lim f
f<l = <-≤-trans fn<fsn f≤l
```

```agda
∃[n]<fn : ∀ α {f} ⦃ mf : MonoSequence f ⦄ → α < Lim f → ∃[ n ] α < f n
∃[n]<fn Zero  {f} _ = 1 , (≤-<-trans z≤ fn<fsn)
∃[n]<fn (wf (suc α)) {f} s<l with ∃[n]<fn (wf α) (<-trans <s s<l)
... | n , <f = suc n , (begin-strict
  wf (suc α)            ≤⟨ <⇒s≤ <f ⟩
  f n                   <⟨ fn<fsn ⟩
  f (suc n)             ∎)
∃[n]<fn (wf (lim α)) ((n , d) , l<f) = n , d , l<f
```

```agda
module _ {f g} ⦃ mf : MonoSequence f ⦄ ⦃ mg : MonoSequence g ⦄ where
  ∃[m]fn<gm : Lim f ≤ Lim g → ∀ n → ∃[ m ] f n < g m
  ∃[m]fn<gm (l≤ fn≤l) n = ∃[n]<fn (f n) (begin-strict
    f n                            <⟨ fn<fsn ⟩
    f (suc n)                      ≤⟨ fn≤l (suc n) ⟩
    Lim g                          ∎)
```

```agda
<l⇒s<l : ∀ α {f} ⦃ mf : MonoSequence f ⦄ → α < Lim f → Suc α < Lim f
<l⇒s<l α {f} ⦃ mono ⦄ < with ∃[n]<fn α <
... | n , <f = begin-strict Suc α ≤⟨ <⇒s≤ <f ⟩ f n <⟨ f<l ⟩ Lim f ∎
```

```agda
l≤s⇒l≤ : ∀ {f} α ⦃ mf : MonoSequence f ⦄ → Lim f ≤ Suc α → Lim f ≤ α
l≤s⇒l≤ {f} α ⦃ mono ⦄ (l≤ fn≤s) = l≤ λ n → <s⇒≤ (begin-strict
  f n       <⟨ fn<fsn ⟩
  f (suc n) ≤⟨ fn≤s (suc n) ⟩
  Suc α     ∎)
```

```agda
ω≤s⇒ω≤ : ∀ α → ω ≤ Suc α → ω ≤ α
ω≤s⇒ω≤ α ω≤s = l≤s⇒l≤ α ⦃ ⌜⌝-monoSequence ⦄ ω≤s
```

```agda
≢z⇒>z : ∀ {α} → α ≢ Zero → α > Zero
≢z⇒>z {Zero}     z≢z = ⊥-elim (z≢z refl)
≢z⇒>z {wf (suc α)} _ = inj₁ tt , z≤
≢z⇒>z {wf (lim f)} _ = z<l
```

```agda
≈z⇒≡z : ∀ {α} → α ≈ Zero → α ≡ Zero
≈z⇒≡z {Zero} _ = refl
≈z⇒≡z {wf (suc α)} (s≤z , _) = ⊥-elim (s≰z s≤z)
≈z⇒≡z {wf (lim f)} (l≤z , _) = ⊥-elim (<⇒≱ z<l l≤z)
```

```agda
≤z⇒≡z : ∀ {α} → α ≤ Zero → α ≡ Zero
≤z⇒≡z ≤z = ≈z⇒≡z (≤z , z≤)
```

```agda
≡z⊎>z : ∀ α → α ≡ Zero ⊎ α > Zero
≡z⊎>z Zero         = inj₁ refl
≡z⊎>z (wf (suc α)) = inj₂ z<s
≡z⊎>z (wf (lim f)) = inj₂ z<l
```

```agda
<ω⊎≥ω : ∀ α → α < ω ⊎ α ≥ ω
<ω⊎≥ω Zero = inj₁ z<ω
<ω⊎≥ω (wf (suc α)) with <ω⊎≥ω (wf α)
... | inj₁ <ω = inj₁ (s<ω (wf α) <ω)
... | inj₂ ≥ω = inj₂ (≤⇒≤s ≥ω)
<ω⊎≥ω (wf (lim f)) = inj₂ ω≤l
```
