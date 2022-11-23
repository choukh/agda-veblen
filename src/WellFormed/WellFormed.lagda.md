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
open import NonWellFormed.WellFormed as ord using (WellFormed; ⌜_⌝-wellFormed)

open Ord using (nwf)
open WellFormed.Ordinal.≤-Reasoning

open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕ
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Function using (_∘_; _↩_; it)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; refl; sym; cong)
```

```agda
⌜_⌝ : ℕ → Ord
⌜ zero ⌝ = Zero
⌜ suc n ⌝ = wf ord.⌜ suc n ⌝ ⦃ ⌜ n ⌝-wellFormed ⦄

ord⌜_⌝ : ∀ n → nwf ⌜ n ⌝ ≡ ord.⌜ n ⌝
ord⌜ zero ⌝ = refl
ord⌜ suc n ⌝ = refl

nwf⌜_⌝ : ∀ n → ord.⌜ n ⌝ ≡ nwf ⌜ n ⌝
nwf⌜ n ⌝ = sym ord⌜ n ⌝

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
n<ω (suc n) rewrite nwf⌜ n ⌝ = s<ω ⌜ n ⌝ (n<ω n)
```

```agda
fn<fsn : ∀ f n → ⦃ MonoSequence f ⦄ → f n < f (suc n)
fn<fsn f n ⦃ wrap mono ⦄ = mono (ℕ.s≤s ℕ.≤-refl)
```

```agda
⌜n⌝≤fn : ∀ f n → ⦃ MonoSequence f ⦄ → ⌜ n ⌝ ≤ f n
⌜n⌝≤fn f zero = z≤
⌜n⌝≤fn f (suc n) rewrite nwf⌜ n ⌝ = begin
  Suc ⌜ n ⌝         ≤⟨ s≤s (⌜n⌝≤fn f n) ⟩
  Suc (f n)         ≤⟨ <⇒s≤ (fn<fsn f n) ⟩
  f (suc n)         ∎
```

```agda
ω≤l : ∀ f ⦃ mf : MonoSequence f ⦄ → ω ≤ Lim f
ω≤l f = l≤ (λ n → ≤f⇒≤l (⌜n⌝≤fn f n))
```

```agda
⌜⌝-injective : ∀ {m n} → ⌜ m ⌝ ≡ ⌜ n ⌝ → m ≡ n
⌜⌝-injective {m} {n} eq = ord.⌜⌝-injective helper where
  helper : ord.⌜ m ⌝ ≡ ord.⌜ n ⌝
  helper rewrite nwf⌜ m ⌝ | nwf⌜ n ⌝ = cong nwf eq
```

```agda
⌜⌝-surjective : ∀ α → α < ω → ∃[ n ] α ≡ ⌜ n ⌝
⌜⌝-surjective (wf zero) _ = 0 , refl
⌜⌝-surjective (wf (suc α)) s<ω with ⌜⌝-surjective (wf α) (<-trans <s s<ω)
... | zero  , refl = 1 , refl
... | suc n , refl = suc (suc n) , refl
⌜⌝-surjective (wf (lim f)) l<ω = ⊥-elim (<⇒≱ l<ω (ω≤l (lift f)))
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
