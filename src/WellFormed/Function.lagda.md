---
title: Agda大序数(2-2) 序数函数
zhihu-tags: Agda, 序数, 大数数学
---

# Agda大序数(2-2) 序数函数

> 交流Q群: 893531731  
> 目录: [WellFormed.html](https://choukh.github.io/agda-lvo/WellFormed.html)  
> 本文源码: [Function.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/WellFormed/Function.lagda.md)  
> 高亮渲染: [Function.html](https://choukh.github.io/agda-lvo/WellFormed.Function.html)  
> 如果你在知乎看到本文: 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

```agda
{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --overlapping-instances #-}

module WellFormed.Function where
```

## 前置

```agda
open import WellFormed.Ordinal
open WellFormed.Ordinal.≤-Reasoning
import NonWellFormed.Function as ord

open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Function using (_∘_; id; λ-; it)
open import Relation.Binary using (Monotonic₁; _Respects_)
```

## 序数函数的性质

```agda
private variable
  {F} : Ord → Ord
```

```agda
≤-increasing : (Ord → Ord) → Set
≤-increasing F = ∀ α → α ≤ F α

<-increasing : (Ord → Ord) → Set
<-increasing F = ∀ α → α < F α
```

```agda
<⇒≤-incr : <-increasing F → ≤-increasing F
<⇒≤-incr <-incr α = <⇒≤ (<-incr α)
```

```agda
≤-monotonic : (Ord → Ord) → Set
≤-monotonic F = Monotonic₁ _≤_ _≤_ F

<-monotonic : (Ord → Ord) → Set
<-monotonic F = Monotonic₁ _<_ _<_ F

module _ F (<-mono : <-monotonic F) where
  ∘-mono : ∀ {f} ⦃ mf : MonoSequence f ⦄ → MonoSequence (F ∘ f)
  ∘-mono = wrap (<-mono ∘ unwrap it)
```

```agda
record normal (F : Ord → Ord) : Set where
  constructor nml
  field
    nml-≤ : ≤-monotonic F
    nml-< : <-monotonic F
    nml-≈ : ∀ f ⦃ mf : MonoSequence f ⦄ → F (Lim f) ≈ Lim (F ∘ f) ⦃ ∘-mono F nml-< ⦄
open normal public
```

```agda
module _ (nmlF@(nml _ <-mono ct) : normal F) where
  normal⇒≤-incr : ≤-increasing F
  normal⇒≤-incr Zero         = z≤
  normal⇒≤-incr (wf (suc α)) = let α = wf α in begin
    Suc α                      ≤⟨ s≤s (normal⇒≤-incr α) ⟩
    Suc (F α)                  ≤⟨ <⇒s≤ (<-mono <s) ⟩
    F (Suc α)                  ∎
  normal⇒≤-incr (wf (lim f)) = let instance _ = ∘-mono F <-mono in
                               let f = lift f in l≤ λ n → begin
    f n                        ≤⟨ ≤f⇒≤l (normal⇒≤-incr _) ⟩
    Lim (F ∘ f)                ≈˘⟨ ct f ⟩
    F (Lim f)                  ∎
```

```agda
_≈ᶠ_ : (Ord → Ord) → (Ord → Ord) → Set
F ≈ᶠ G = ∀ {α} → F α ≈ G α

normal-resp-≈ : normal Respects _≈ᶠ_
normal-resp-≈ {F} {G} ext nmlF@(nml ≤-mono <-mono ct) =
  let instance _ = ∘-mono F <-mono in nml
    (λ {α} {β} α≤β → begin G α ≈˘⟨ ext ⟩ F α ≤⟨ ≤-mono α≤β ⟩ F β ≈⟨ ext ⟩ G β ∎)
    (λ {α} {β} α<β → begin-strict G α ≈˘⟨ ext ⟩ F α <⟨ <-mono α<β ⟩ F β ≈⟨ ext ⟩ G β ∎)
    (λ f → begin-equality
      G (Lim f)   ≈˘⟨ ext ⟩
      F (Lim f)   ≈⟨ ct f ⟩
      Lim (F ∘ f) ≈⟨ l≈l ext ⟩
      Lim (G ∘ f) ⦃ {!   !} ⦄ ∎)
```
