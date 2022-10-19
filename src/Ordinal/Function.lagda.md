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

**(本章施工中)**

```agda
{-# OPTIONS --without-K --safe #-}

module Ordinal.Function where

open import Ordinal
open import Ordinal.WellFormed using (wellFormed; ∃[n]<fn; f<l)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
```

## 序数函数的性质

我们称 F G : Ord → Ord 为序数函数, 它是我们的主要研究对象. 本章统一列出了我们将要考虑的序数函数的性质. 首先, 由上一章的良构谓词, 我们可以谈论**保良构**的函数. 我们会证明我们构造出的每一个序数函数都是保良构的.

```agda
wf-preserving : (Ord → Ord) → Set
wf-preserving F = ∀ {α} → wellFormed α → wellFormed (F α)
```

以下两条称为 F 的放大性. `α ≤ F α` 称为**弱放大**, `α < F α` 称为**强放大**. 弱放大的函数在有些书中又被称为*非无穷降链*.

```agda
≤-enlarging : (Ord → Ord) → Set
≤-enlarging F = ∀ α → α ≤ F α

<-enlarging : (Ord → Ord) → Set
<-enlarging F = ∀ α → α < F α
```

显然, 强放大蕴含弱放大.

```agda
<→≤-enlarging : ∀ {F} → <-enlarging F → ≤-enlarging F
<→≤-enlarging <-elg = λ α → <⇒≤ (<-elg α)
```

下面是两种特殊的放大性, 分别叫做**零处强放大**和**良构后继处强放大**. 在 Veblen 不动点理论中要用到它们. 显然, 强放大蕴含这两者.

```agda
zero-enlarging : (Ord → Ord) → Set
zero-enlarging F = zero < F zero

suc-enlarging : (Ord → Ord) → Set
suc-enlarging F = ∀ {α} → wellFormed α → suc α < F (suc α)
```

以下两条称为 F 的递增性, 分别叫做**弱递增**和**强递增**. 在有些书中, 弱递增又称为单调性, 强递增又称为强单调性.

```agda
≤-increasing : (Ord → Ord) → Set
≤-increasing F = ∀ {α β} → α ≤ β → F α ≤ F β

<-increasing : (Ord → Ord) → Set
<-increasing F = ∀ {α β} → α < β → F α < F β
```

下面是一种特殊的放大性, 称为后继处强递增. 显然, 强递增蕴含后继处强递增.

```agda
suc-increasing : (Ord → Ord) → Set
suc-increasing F = ∀ α → F α < F (suc α)

<→suc-increasing : ∀ {F} → <-increasing F → suc-increasing F
<→suc-increasing <-inc = λ α → <-inc <s
```

如果可以交换 `F` 和 `lim` 的顺序, 我们就说 `F` 在**极限处连续**, 简称连续.

```agda
lim-continuous : (Ord → Ord) → Set
lim-continuous F = ∀ f → F (lim f) ≈ lim (λ n → F (f n))
```

## 序数嵌入

我们在后续章节主要研究**序数嵌入** (normal function), 它定义为弱递增且强递增且连续的序数函数.

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
open import Relation.Binary using (_Respects_)
open import Relation.Binary.Reasoning.Setoid (OrdSetoid)
  using (begin_; step-≈; step-≈˘; _∎)
  
normal-resp-≈ : normal Respects (λ F G → ∀ {α} → F α ≈ G α)
normal-resp-≈ {F} {G} ext (≤-elg , <-elg , lim-ct)
  = (λ α≤β → ≤-respˡ-≈ ext (≤-respʳ-≈ ext (≤-elg α≤β)))
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

## 与传统定义的等价性

在传统文献中序数嵌入定义为在后继处递增且极限处连续的序数函数.

```agda
wf-<-increasing : (Ord → Ord) → Set
wf-<-increasing F = ∀ {α β} → wellFormed α → wellFormed β → α < β → F α < F β
```

```agda
wf-suc-increasing : (Ord → Ord) → Set
wf-suc-increasing F = ∀ {α} → wellFormed α → F α < F (suc α)
```

```agda
wf-normal : (Ord → Ord) → Set
wf-normal F = ≤-increasing F × wf-suc-increasing F × lim-continuous F
```

```agda
wf-nml→<-inc : ∀ {F} → wf-normal F → wf-<-increasing F

wf-nml→<-inc nml@(≤-inc , suc-inc , _) {β = suc β} wfα wfβ α<s
  = ≤-<-trans
    (≤-inc (<s→≤ α<s)) {- F α ≤ F β -}
    (suc-inc wfβ)      {- F β < F (suc β) -}

wf-nml→<-inc nml@(_ , _ , lim-ct) {β = lim f} wfα wfβ@(wfn , inc) α<l
  with ∃[n]<fn inc α<l
...  | (n , α<fn) = <-trans
        (wf-nml→<-inc nml wfα wfn α<fn)       {- F α < F (f n) -}
        (<-respʳ-≈ (≈-sym (lim-ct f)) helper) {- F (f n) < F (lim f) -}
  {- F (f n) < lim (λ n → F (f n)) -}
  where helper = f<l λ m<n → wf-nml→<-inc nml wfn wfn (inc m<n)
```
