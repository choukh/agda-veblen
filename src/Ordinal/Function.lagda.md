---
title: Agda大序数(3) 序数函数
zhihu-tags: Agda, 序数, 大数数学
---

# Agda大序数(3) 序数函数

> 交流Q群: 893531731  
> 总目录: [Everything.html](https://choukh.github.io/agda-lvo/Everything.html)  
> 本文源码: [Ordinal/Function.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/Ordinal/Function.lagda.md)  
> 高亮渲染: [Ordinal.Function.html](https://choukh.github.io/agda-lvo/Ordinal.Function.html)  
> 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

```agda
{-# OPTIONS --without-K --safe #-}

module Ordinal.Function where

open import Ordinal
open import Ordinal.WellFormed using (wellFormed)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary using (_Respects_)
open import Relation.Binary.Reasoning.Setoid (OrdSetoid)
  using (begin_; step-≈; step-≈˘; _∎)
```

```agda
wf-preserving : (Ord → Ord) → Set
wf-preserving F = ∀ {α} → wellFormed α → wellFormed (F α)
```

```agda
≤-enlarging : (Ord → Ord) → Set
≤-enlarging F = ∀ α → α ≤ F α

<-enlarging : (Ord → Ord) → Set
<-enlarging F = ∀ α → α < F α
```

```agda
<→≤-enlarging : ∀ {F} → <-enlarging F → ≤-enlarging F
<→≤-enlarging <-elg = λ α → <⇒≤ (<-elg α)
```

```agda
zero-enlarging : (Ord → Ord) → Set
zero-enlarging F = zero < F zero

suc-enlarging : (Ord → Ord) → Set
suc-enlarging F = ∀ {α} → wellFormed α → suc α < F (suc α)
```

```agda
≤-increasing : (Ord → Ord) → Set
≤-increasing F = ∀ {α β} → α ≤ β → F α ≤ F β

<-increasing : (Ord → Ord) → Set
<-increasing F = ∀ {α β} → α < β → F α < F β
```

```agda
suc-increasing : (Ord → Ord) → Set
suc-increasing F = ∀ α → F α < F (suc α)
```

```agda
<→suc-increasing : ∀ {F} → <-increasing F → suc-increasing F
<→suc-increasing <-inc = λ α → <-inc <s
```

```agda
lim-continuous : (Ord → Ord) → Set
lim-continuous F = ∀ f → F (lim f) ≈ lim (λ n → F (f n))
```

```agda
normal : (Ord → Ord) → Set
normal F = ≤-increasing F × <-increasing F × lim-continuous F
```

```agda
normal→≤-enlarging : ∀ {F} → normal F → ≤-enlarging F
normal→≤-enlarging nml@(_ , <-inc , lim-ct) =
  λ { zero    → z≤
    ; (suc α) → ≤-trans (s≤s (normal→≤-enlarging nml α)) (<→s≤ (<-inc <s))
    ; (lim f) → l≤ (λ n → ≤-respʳ-≈
        (≈-sym (lim-ct f))
        (≤→≤l (normal→≤-enlarging nml (f n)))
      )
    }
```

```agda
normal-resp-≈ : normal Respects (λ F G → ∀ {α} → F α ≈ G α)
normal-resp-≈ {F} {G} ext (≤-elg , <-elg , lim-ct) =
    (λ α≤β → ≤-respˡ-≈ ext (≤-respʳ-≈ ext (≤-elg α≤β)))
  , (λ α<β → <-≤-trans (<-respˡ-≈ ext (<-elg α<β)) (proj₁ ext))
  , (λ f → begin
      G (lim f)           ≈˘⟨ ext ⟩
      F (lim f)           ≈⟨ lim-ct f ⟩
      lim (λ n → F (f n)) ≈⟨ helper f ⟩
      lim (λ n → G (f n)) ∎
    )
    where helper = λ f → l≤ (λ n → ≤→≤l (proj₁ ext))
                       , l≤ (λ n → ≤→≤l (proj₂ ext))
```
