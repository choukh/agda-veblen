---
title: Agda大序数(2*) 经典序数
zhihu-tags: Agda, 序数, 大数数学
---

# Agda大序数(2*) 经典序数

> 交流Q群: 893531731  
> 总目录: [Everything.html](https://choukh.github.io/agda-lvo/Everything.html)  
> 本文源码: [Ordinal/Classic.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/Ordinal/Classic.lagda.md)  
> 高亮渲染: [Ordinal.Classic.html](https://choukh.github.io/agda-lvo/Ordinal.Classic.html)  
> 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

```agda
{-# OPTIONS --without-K #-}

module Ordinal.Classic where

open import Ordinal
open import Ordinal.WellFormed using (wellFormed; z<l; s<l; f<l; fn<fsn)
open import Data.Nat using (ℕ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Nullary using (¬_; _because_; ofʸ; ofⁿ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
```

## 经典逻辑

```agda
open import Axiom.ExcludedMiddle
postulate
  LEM : ∀ {ℓ} → ExcludedMiddle ℓ

¬¬-elim : ∀ {P : Set} → ¬ ¬ P → P
¬¬-elim {P} ¬¬p with LEM {P = P}
...                | _ because ofʸ  p = p
...                | _ because ofⁿ ¬p = ⊥-elim (¬¬p ¬p)

¬∀→∃¬ : ∀ {A : Set} {P : A → Set} → ¬ (∀ x → P x) → ∃[ x ] ¬ P x
¬∀→∃¬ {P = P} ¬∀ = ¬¬-elim λ ¬∃¬ → ¬∀ (λ x → ¬¬-elim (λ ¬p → ¬∃¬ (x , ¬p)))
```

## `≤` 线序

```agda
≤-total : ∀ {α β} → wellFormed α → wellFormed β → α ≤ β ⊎ β ≤ α
≤-split : ∀ {α β} → wellFormed α → wellFormed β → α ≤ β → α < β ⊎ α ≈ β

≤-total {zero}  {β}    _ _ = inj₁ z≤
≤-total {suc α} {zero} _ _ = inj₂ z≤
≤-total {lim f} {zero} _ _ = inj₂ z≤

≤-total {suc α} {suc β} wfα wfβ with ≤-total wfα wfβ
... | inj₁ α≤β = inj₁ (s≤s α≤β)
... | inj₂ β≤α = inj₂ (s≤s β≤α)
≤-total {suc α} {lim f} wfα wfβ with ≤-total wfα wfβ
... | inj₁ α≤l with ≤-split wfα wfβ α≤l
...               | inj₁ α<l = inj₁ (<⇒≤ (s<l (proj₂ wfβ) α<l))
...               | inj₂ α≈l = inj₂ (≤-trans (proj₂ α≈l) ≤s)
≤-total {suc α} {lim f} wfα wfβ
    | inj₂ l≤α = inj₂ (≤-trans l≤α ≤s)

≤-total {lim f} {suc β} wfα wfβ with ≤-total wfα wfβ
... | inj₁ l≤β = inj₁ (≤-trans l≤β ≤s)
... | inj₂ β≤l with ≤-split wfβ wfα β≤l
...               | inj₁ β<l = inj₂ (<⇒≤ (s<l (proj₂ wfα) β<l))
...               | inj₂ β≈l = inj₁ (≤-trans (proj₂ β≈l) ≤s)

≤-total {lim f} {lim g} wfα wfβ with LEM {P = ∀ n → f n ≤ lim g}
... | _ because ofʸ fn≤l = inj₁ (l≤ fn≤l)
... | _ because ofⁿ fn≰l with ¬∀→∃¬ fn≰l
...                         | (n , fn≰l) with ≤-total wfβ (proj₁ wfα)
...                                         | inj₁ l≤fn = inj₂ (≤→≤l l≤fn)
...                                         | inj₂ fn≤l = ⊥-elim (fn≰l fn≤l)

≰⇒≥ : ∀ {α} {β} → wellFormed α → wellFormed β → α ≰ β → α ≥ β
≰⇒≥ wfα wfβ ≰ with ≤-total wfα wfβ
... | inj₁ ≤ = ⊥-elim (≰ ≤)
... | inj₂ ≥ = ≥

<l⊎≥l : ∀ {α g} → wellFormed α → wellFormed (lim g) → α < lim g ⊎ α ≥ lim g
<l⊎≥l {zero}  _   (_ , inc)        = inj₁ (z<l inc)
<l⊎≥l {suc α} wfα wfβ with <l⊎≥l wfα wfβ
...                      | inj₁ <l = inj₁ (s<l (proj₂ wfβ) <l)
...                      | inj₂ ≥l = inj₂ (≤-trans ≥l ≤s)
<l⊎≥l {lim f} {g} wfα wfβ with LEM {P = ∀ n → g n ≤ lim f}
... | _ because ofʸ gn≤l = inj₂ (l≤ gn≤l)
... | _ because ofⁿ gn≰l with ¬∀→∃¬ gn≰l
...                         | (n , gn≰l) with <l⊎≥l {g n} {f} (proj₁ wfβ) wfα
...                                         | inj₁ gn<l = ⊥-elim (<⇒≱ gn<l (≰⇒≥ (proj₁ wfβ) wfα gn≰l))
...                                         | inj₂ l≤gn = inj₁ (≤-<-trans l≤gn (f<l (proj₂ wfβ)))

l≤s→l≤ : ∀ {α f} → wellFormed α → wellFormed (lim f) → lim f ≤ suc α → lim f ≤ α
l≤s→l≤ wfα wfβ l≤s with <l⊎≥l wfα wfβ
...                   | inj₁ <l = ⊥-elim (≤⇒≯ l≤s (s<l (proj₂ wfβ) <l))
...                   | inj₂ ≥l = ≥l

≤-split {zero}  {zero}  _   _   _   = inj₂ ≈-refl
≤-split {zero}  {suc β} _   _   _   = inj₁ (z<s β)
≤-split {zero}  {lim f} _   wfβ _   = inj₁ (z<l (proj₂ wfβ))
≤-split {suc α} {zero}  _   _   s≤z = ⊥-elim (s≰z s≤z)
≤-split {lim f} {zero}  _   _   l≤β = inj₂ (≤z→≈z l≤β)

≤-split {suc α} {suc β} wfα wfβ s≤s
  with ≤-split wfα wfβ (s≤s→≤ s≤s)
... | inj₁ α<β = inj₁ (s<s α<β)
... | inj₂ α≈β = inj₂ (s≈s α≈β)
≤-split {suc α} {lim f} wfα (wfn , inc) (s≤ α≤l)
  with ≤-split wfα wfn (≤∸→≤ α≤l)
... | inj₁ α<fn = inj₁ (s<l inc (<→<l α<fn))
... | inj₂ α≈fn = inj₁ (s<l inc (<→<l (<-respˡ-≈ (≈-sym α≈fn) (fn<fsn inc))))
≤-split {lim f} {suc β} wfα wfβ l≤β
  with ≤-split wfα wfβ (l≤s→l≤ wfβ wfα l≤β)
... | inj₁ l<β = inj₁ (<-trans l<β <s)
... | inj₂ l≈β = inj₁ (<-respˡ-≈ (≈-sym l≈β) <s)

≤-split {lim f} {lim g} wfα wfβ f≤g with LEM {P = ∀ n → g n ≤ lim f}
... | _ because ofʸ gn≤l = inj₂ (f≤g , (l≤ gn≤l))
... | _ because ofⁿ gn≰l with ¬∀→∃¬ gn≰l
...                         | (n , gn≰l) = inj₁ (≤-<-trans
                              (≰⇒≥ (proj₁ wfβ) wfα gn≰l)
                              (f<l (proj₂ wfβ)))
```
