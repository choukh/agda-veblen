---
title: Agda大序数(3) 序数函数
zhihu-tags: Agda, 序数, 大数数学
zhihu-url: https://zhuanlan.zhihu.com/p/575766146
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
```

本章在内容上延续前两章.

```agda
open import Ordinal
open import Ordinal.WellFormed using (wellFormed; ∃[n]<fn; f<l)
```

对于标准库除了乘积类型, 我们还将使用函数复合 `_∘_`, 函数**尊重**二元关系 `_Respects_`, 以及序数广集上的 `_≈_` 推理.

```agda
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Binary using (_Respects_)
open import Relation.Binary.Reasoning.Setoid (OrdSetoid)
  using (begin_; step-≈; step-≈˘; _∎)
```

## 序数函数的性质

我们称 F : Ord → Ord 为序数函数, 它是我们的主要研究对象.

```agda
private variable
  {F} : Ord → Ord
```

本章统一列出了我们将要考虑的序数函数的性质. 首先, 由上一章的良构谓词, 我们可以谈论**保良构**的函数. 我们会证明我们构造出的每一个序数函数都是保良构的.

```agda
wf-preserving : (Ord → Ord) → Set
wf-preserving F = ∀ {α} → wellFormed α → wellFormed (F α)
```

以下两条称为 F 的放大性. `α ≤ F α` 称为**弱放大**, `α < F α` 称为**强放大**. 弱放大在有些书中又被称为*非无穷降链*.

```agda
≤-enlarging : (Ord → Ord) → Set
≤-enlarging F = ∀ α → α ≤ F α

<-enlarging : (Ord → Ord) → Set
<-enlarging F = ∀ α → α < F α
```

显然, 强放大蕴含弱放大.

```agda
_ : <-enlarging F → ≤-enlarging F
_ = λ <-elg α → <⇒≤ (<-elg α)
```

下面是两种特殊的放大性, 分别叫做**零放大**和**良构后继放大**. 在 Veblen 不动点理论中要用到它们. 显然, 强放大蕴含这两者.

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

下面是两种特殊的递增性, 分别叫做**后继递增**和**前驱递增**. 显然, 强递增蕴含这两者.

```agda
suc-increasing : (Ord → Ord) → Set
suc-increasing F = ∀ α → F α < F (suc α)

∸-increasing : (Ord → Ord) → Set
∸-increasing F = ∀ α d → F (α ∸ d) < F α

_ : <-increasing F → suc-increasing F
_ = λ <-inc _ → <-inc <s

_ : <-increasing F → ∸-increasing F
_ = λ <-inc α d → <-inc (s≤→< s∸≤)
```

如果可以交换 `F` 和 `lim` 的顺序, 我们就说 `F` 在**极限连续**, 简称连续.

```agda
lim-continuous : (Ord → Ord) → Set
lim-continuous F = ∀ f → F (lim f) ≈ lim (F ∘ f)
```

## 序数嵌入

我们在后续章节主要研究**序数嵌入** (normal function), 它定义为弱递增且强递增且连续的序数函数.

```agda
normal : (Ord → Ord) → Set
normal F = ≤-increasing F × <-increasing F × lim-continuous F
```

对该定义的解释放在下一小节. 我们先来看一些结论. 首先, 序数嵌入蕴含非无穷降链, 即对序数嵌入 `F` 有 `α ≤ F α`. 讨论 `α`.

- 零的情况显然成立.

```agda
normal→≤-enl : normal F → ≤-enlarging F
normal→≤-enl nml@(_ , <-inc , lim-ct) =
  λ { zero    → z≤
```

- 后继的情况, 首先由归纳假设 `α ≤ F α` 有 `suc α ≤ suc (F α)`. 又由强递增式 `F α < F (suc α)` 有 `suc (F α) ≤ F (suc α)`. 结合两者由传递性即得 `suc α ≤ F (suc α)`.

```agda
    ; (suc α) → ≤-trans
        (s≤s (normal→≤-enl nml α)) {- suc α ≤ suc (F α) -}
        (<→s≤ (<-inc <s))                {- suc (F α) ≤ F (suc α) -}
```

- 极限的情况, 即证 `f n ≤ F (lim f)`. 由连续性, `F (lim f) ≈ lim (F ∘ f)`. 只需证 `f n ≤ lim (F ∘ f)`, 只需证 `f n ≤ (F ∘ f) n`, 此即归纳假设.

```agda
    ; (lim f) → l≤ (λ n → ≤-respʳ-≈
        (≈-sym (lim-ct f))                    {- F (lim f) ≈ lim (F ∘ f) -}
        (≤→≤l (normal→≤-enl nml (f n))) {- f n ≤ lim (F ∘ f) -}
      )
    }
```

序数嵌入**尊重**序数函数的外延等价性.

```agda
normal-resp-≈ : normal Respects (λ F G → ∀ {α} → F α ≈ G α)
```

我们有 `F` 和 `G` 的外延等价 `ext`, `F` 的弱递增 `≤-inc`, 强递增 `<-inc` 和连续 `lim-ct`, 要证 `G` 是序数嵌入.

```agda
normal-resp-≈ {F} {G} ext (≤-inc , <-inc , lim-ct)
```

- 需证 `G` 弱递增. 对 `α ≤ β`, 由 `≤-inc` 有 `F α ≤ F β`, 两边都用 `ext` 改写即得 `G α ≤ G β`.

```agda
  = (λ α≤β → ≤-respˡ-≈ ext (≤-respʳ-≈ ext (≤-inc α≤β)))
```

- 需证 `G` 强递增. 对 `α < β`, 由 `<-inc` 有 `F α < F β`, 左边用 `ext` 改写得 `G α < F β`. 由 `ext` 又有 `F β ≤ G β`. 由传递性即得 `G α < G β`.

```agda
  , (λ α<β → <-≤-trans (<-respˡ-≈ ext (<-inc α<β)) (proj₁ ext))
```

- 需证 `G` 连续. 以下改写链是自明的. 对于最后一步, 拆成两个 `_≤_` 式, 分别由 `ext` 的两个分量可证.

```agda
  , (λ f → begin
      G (lim f)   ≈˘⟨ ext ⟩
      F (lim f)   ≈⟨ lim-ct f ⟩
      lim (F ∘ f) ≈⟨ helper f ⟩
      lim (G ∘ f) ∎)
    where helper = λ f → l≤ (λ n → ≤→≤l (proj₁ ext))
                       , l≤ (λ n → ≤→≤l (proj₂ ext))
```

## 与传统定义的等价性

在传统文献中序数嵌入定义为在后继递增且极限连续的序数函数. 两种定义对比如下.

| 本构筑    | 传统     |
| ----     | ----    |
| 弱递增    | -       |
| 强递增    | 后继递增 |
| 极限连续  | 极限连续 |

第三点是一样的, 我们分别解释前两点.

### 弱递增

传统数学中强递增蕴含弱递增, 该论证依赖以下两点.

1. "≤" 到 "< 或 =" 的分裂, 而在本构筑中实现这一点需要排中律, 如[独立的一章](Ordinal.Classic.html)所述.
2. "=" 的合同性 (congruence), 即对任意 F 有 x = y 蕴含 F x = F y, 而本构筑的 `_≈_` 并不具有.

因此在本构筑中强递增与弱递增是相互独立的, 这就解释了弱递增的不可替代性. 至于其必要性, 上面第2点也已经可以看出来了. 因为我们只关心对 `_≈_` 合同的 (congruent) 函数, 而弱递增蕴含这一点.

```agda
open import Function.Definitions (_≈_) (_≈_) using (Congruent)

≤-inc→cong : ≤-increasing F → Congruent F
≤-inc→cong ≤-inc = λ { (≤ , ≥) → ≤-inc ≤ , ≤-inc ≥ }
```

从根本上可以说, 弱递增的必要性来源于本构筑所依赖的类型论基础的构造主义性和内涵性.

### 强递增

我们用强递增取代后继递增是为了省去良构条件. 若不然, 需要将相关性质都限制成良构版如下[^1].

[^1]: _ 当然我们也可以用一个 record 类型封装良构条件, 但还是没有上面的处理简单.

```agda
wf-<-increasing : (Ord → Ord) → Set
wf-<-increasing F = ∀ {α β} → wellFormed α → wellFormed β → α < β → F α < F β

wf-suc-increasing : (Ord → Ord) → Set
wf-suc-increasing F = ∀ {α} → wellFormed α → F α < F (suc α)

wf-normal : (Ord → Ord) → Set
wf-normal F = ≤-increasing F × wf-suc-increasing F × lim-continuous F
```

可以证明用 `wf-suc-increasing` 取代 `<-increasing` 定义的 `wf-normal` 蕴含 `wf-<-increasing`.

```agda
wf-nml→<-inc : wf-normal F → wf-<-increasing F

wf-nml→<-inc nml@(≤-inc , suc-inc , _) {β = suc β} wfα wfβ α<s
  = ≤-<-trans
    (≤-inc (<s→≤ α<s)) {- F α ≤ F β -}
    (suc-inc wfβ)      {- F β < F (suc β) -}

wf-nml→<-inc nml@(_ , _ , lim-ct) {β = lim f} wfα wfβ@(wfn , inc) α<l
  with ∃[n]<fn inc α<l
...  | (n , α<fn) = <-trans
        (wf-nml→<-inc nml wfα wfn α<fn)       {- F α < F (f n) -}
        (<-respʳ-≈ (≈-sym (lim-ct f)) helper) {- F (f n) < F (lim f) -}
  {- F (f n) < lim (F ∘ f) -}
  where helper = f<l λ m<n → wf-nml→<-inc nml wfn wfn (inc m<n)
```

也就是说, 限定在良构序数的情况下[^2], 传统定义蕴含我们的定义. 另一方面, 显然地, 由 `<-increasing` 蕴含 `suc-increasing`, 我们的定义也蕴含传统定义. 这就说明了两者的等价性.

[^2]: _ 且忽略上一小节所述由构造主义和内涵类型论所造成的微妙区别
 