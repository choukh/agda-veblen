---
title: Agda大序数(2*) 经典序数
zhihu-tags: Agda, 序数, 大数数学
zhihu-url: https://zhuanlan.zhihu.com/p/575362583
---

# Agda大序数(2*) 经典序数

> 交流Q群: 893531731  
> 总目录: [Everything.html](https://choukh.github.io/agda-lvo/Everything.html)  
> 本文源码: [Ordinal/Classic.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/Ordinal/Classic.lagda.md)  
> 高亮渲染: [Ordinal.Classic.html](https://choukh.github.io/agda-lvo/Ordinal.Classic.html)  
> 如果你在知乎看到本文: 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

本章假设排中律并证明良构序数上的 `_≤_` 是线序, 该内容与主线无关, 仅作为学习上的参考. 因为有排中律, 所以非 `--safe`.

```agda
{-# OPTIONS --without-K #-}

module Ordinal.Classic where
```

本章内容上延续前两章, 其他依赖都是标准库的常规模块.

```agda
open import Ordinal
open Ordinal.≤-Reasoning
open import Ordinal.WellFormed using (wellFormed; z<l; s<l; f<l; fn<fsn)
open import Data.Nat using (ℕ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
```

## 经典逻辑

标准库提供排中律的定义, 它是用 `Dec` 定义的, 所以还导入了 `Dec` 相关模块. 关于 `Dec` 的好处在 [PLFA](https://agda-zh.github.io/PLFA-zh/) part1 有讲, 当然这里完全不需要用到那部分特性.

```agda
open import Axiom.ExcludedMiddle
open import Relation.Nullary using (¬_; Dec; _because_; ofʸ; ofⁿ)
```

导入排中律模块并不会自动假设排中律, 还需要显式 `postulate`. Agda 的排中律是宇宙多态的, 我们把宇宙等级设为隐式参数, 让 Agda 自己推断.

```agda
postulate
  LEM : ∀ {ℓ} → ExcludedMiddle ℓ
```

由排中律立即得到双重否定消去, 我们把它当做反证法使用.

```agda
¬¬-elim : ∀ {P : Set} → ¬ ¬ P → P
¬¬-elim {P} ¬¬p with LEM {P = P}
... | _ because ofʸ  p = p
... | _ because ofⁿ ¬p = ⊥-elim (¬¬p ¬p)
```

两次反证法即可证"非全部满足则存在不满足".

```agda
¬∀⇒∃¬ : ∀ {A : Set} {P : A → Set} → ¬ (∀ x → P x) → ∃[ x ] ¬ P x
¬∀⇒∃¬ {P = P} ¬∀ = ¬¬-elim λ ¬∃¬ → ¬∀ (λ x → ¬¬-elim (λ ¬p → ¬∃¬ (x , ¬p)))
```

## `≤` 线序

第一章已证 `_≤_` 是偏序, 我们只证完全性 (total). 简单起见我们不再另外定义良构序数的 record 类型, 仅把良构条件作为前件带上.

```agda
≤-total : ∀ {α β} → wellFormed α → wellFormed β → α ≤ β ⊎ β ≤ α
```

即使有排中律, 该证明也不简单. 实际上, 我们使用了 Agda 的[互递归](https://agda.readthedocs.io/en/v2.6.2.2/language/mutual-recursion.html)特性, 即同时证明上述命题以及以下命题. 两个命题分别在自己的归纳证明过程中调用了对方, 所以叫互递归.

```agda
≤-split : ∀ {α β} → wellFormed α → wellFormed β → α ≤ β → α < β ⊎ α ≈ β
```

我们先证 `≤-total`, 有七种情况. 两边有任何一边是零的时候都是显然的.

```agda
≤-total {zero}  {β}    _ _ = inj₁ z≤
≤-total {suc α} {zero} _ _ = inj₂ z≤
≤-total {lim f} {zero} _ _ = inj₂ z≤
```

两边都是后继的情况, 用归纳假设, 对两个分支分别用 `s≤s` 即可.

```agda
≤-total {suc α} {suc β} wfα wfβ with ≤-total wfα wfβ
... | inj₁ α≤β = inj₁ (s≤s α≤β)
... | inj₂ β≤α = inj₂ (s≤s β≤α)
```

左边是后继右边是极限的情况, 用归纳假设得到两个分支.

- 若 `α ≤ lim f`, 对它用 `≤-split`, 注意这里是互递归调用
  - 若 `α < lim f`, 由上一章的 `s<l` 可知 `suc α < lim f`, 所以 `suc α ≤ lim f`
  - 若 `α ≈ lim f`, 有 `lim f ≤ α ≤ suc α`
- 若 `lim f ≤ α`, 有 `lim f ≤ α ≤ suc α`

```agda
≤-total {suc α} {lim f} wfα wfβ with ≤-total wfα wfβ
... | inj₁ α≤l with ≤-split wfα wfβ α≤l
...   | inj₁ α<l = inj₁ (begin suc α <⟨ s<l (proj₂ wfβ) α<l ⟩ lim f ∎)
...   | inj₂ α≈l = inj₂ (begin lim f ≤⟨ proj₂ α≈l ⟩ α ≤⟨ ≤s ⟩ suc α ∎)
≤-total {suc α} {lim f} wfα wfβ
    | inj₂ l≤α = inj₂ (≤⇒≤s l≤α)
```

左边是极限右边是后继的情况与上一种对称, 同样也互递归调用了 `≤-split`.

```agda
≤-total {lim f} {suc β} wfα wfβ with ≤-total wfα wfβ
... | inj₁ l≤β = inj₁ (≤⇒≤s l≤β)
... | inj₂ β≤l with ≤-split wfβ wfα β≤l
...   | inj₁ β<l = inj₂ (begin suc β <⟨ s<l (proj₂ wfα) β<l ⟩ lim f ∎)
...   | inj₂ β≈l = inj₁ (begin lim f ≤⟨ proj₂ β≈l ⟩ β ≤⟨ ≤s ⟩ suc β ∎)
```

最后一种两边都是极限的情况必须要排中律, 因为对抽象的 `f` 和 `g` 没有计算方法可以得到诸如 `∀ n → f n ≤ lim g`.

- 若 `∀ n → f n ≤ lim g`, 由 `_≤_` 的构造子 `l≤` 即得 `lim f ≤ lim g`.
- 若不然, 由 `¬∀⇒∃¬`, 存在 `n` 使得 `f n ≰ lim g`. 对 `lim g` 和 `f n` 使用归纳假设.
  - 若 `lim g ≤ f n`, 有 `lim g ≤ f n ≤ lim f`.
  - 若 `f n ≤ lim g`, 与前提矛盾.

```agda
≤-total {lim f} {lim g} wfα wfβ with LEM {P = ∀ n → f n ≤ lim g}
... | _ because ofʸ fn≤l = inj₁ (l≤ fn≤l)
... | _ because ofⁿ fn≰l with ¬∀⇒∃¬ fn≰l
...   | (n , fn≰l) with ≤-total wfβ (proj₁ wfα)
...     | inj₁ l≤fn = inj₂ (≤f⇒≤l l≤fn)
...     | inj₂ fn≤l = ⊥-elim (fn≰l fn≤l)
```

在证明 `≤-split` 之前我们先用 `≤-total` 证一些引理. 没错, 互递归之间可以插入一些依赖两者的引理. 首先由 `≤-total` 立即有 `≰⇒≥`.

```agda
≰⇒≥ : ∀ {α} {β} → wellFormed α → wellFormed β → α ≰ β → α ≥ β
≰⇒≥ wfα wfβ ≰ with ≤-total wfα wfβ
... | inj₁ ≤ = ⊥-elim (≰ ≤)
... | inj₂ ≥ = ≥
```

下面是第二章 [`<ω⊎≥ω`](Ordinal.WellFormed.html#6418) 的推广, 前两个分支的证法与之类似.

```agda
<l⊎≥l : ∀ {α g} → wellFormed α → wellFormed (lim g) → α < lim g ⊎ α ≥ lim g
<l⊎≥l {zero} _ (_ , mono) = inj₁ (z<l mono)
<l⊎≥l {suc α} wfα wfβ with <l⊎≥l wfα wfβ
... | inj₁ <l = inj₁ (s<l (proj₂ wfβ) <l)
... | inj₂ ≥l = inj₂ (≤⇒≤s ≥l)
```

第三个分支, 要证 `lim f < lim g ⊎ lim f ≥ lim g`. 我们用排中律.

- 若 `∀ n → g n ≤ lim f`, 由 `_≤_` 的构造子 `l≤` 即得 `lim g ≤ lim f`.
- 若不然, 由 `¬∀⇒∃¬`, 存在 `n` 使得 `g n ≰ lim f`. 对 `g n` 和 `lim f` 使用归纳假设.
  - 若 `g n < lim f`, 即 `g n ≤ lim f`, 与前提矛盾.
  - 若 `g n ≥ lim f`, 有 `lim f ≤ g n < lim g`.

```agda
<l⊎≥l {lim f} {g} wfα wfβ with LEM {P = ∀ n → g n ≤ lim f}
... | _ because ofʸ gn≤l = inj₂ (l≤ gn≤l)
... | _ because ofⁿ gn≰l with ¬∀⇒∃¬ gn≰l
...   | (n , gn≰l) with <l⊎≥l {g n} {f} (proj₁ wfβ) wfα
...     | inj₁ gn<l = ⊥-elim (gn≰l (<⇒≤ gn<l))
...     | inj₂ l≤gn = inj₁ (begin-strict lim f ≤⟨ l≤gn ⟩
                                         g n   <⟨ f<l (proj₂ wfβ) ⟩
                                         lim g ∎)
```

下面是第二章 [`ω≤s⇒ω≤`](Ordinal.WellFormed.html#6745) 的推广, 证法也与它完全一样.

```agda
l≤s⇒l≤ : ∀ {α f} → wellFormed α → wellFormed (lim f) → lim f ≤ suc α → lim f ≤ α
l≤s⇒l≤ wfα wfβ l≤s with <l⊎≥l wfα wfβ
... | inj₁ <l = ⊥-elim (≤⇒≯ l≤s (s<l (proj₂ wfβ) <l))
... | inj₂ ≥l = ≥l
```

终于, 可以证明 `≤-split` 了. 首先是比较简单的五种情况.

```agda
≤-split {zero}  {zero}  _   _   _   = inj₂ ≈-refl
≤-split {zero}  {suc β} _   _   _   = inj₁ (z<s β)
≤-split {zero}  {lim f} _   wfβ _   = inj₁ (z<l (proj₂ wfβ))
≤-split {suc α} {zero}  _   _   s≤z = ⊥-elim (s≰z s≤z)
≤-split {lim f} {zero}  _   _   l≤β = inj₂ (≤z⇒≈z l≤β)
```

两边都是后继的情况, 用归纳假设, 对两个分支分别用 `s<s` 和 `s≈s` 即可.

```agda
≤-split {suc α} {suc β} wfα wfβ s≤s
  with ≤-split wfα wfβ (s≤s⇒≤ s≤s)
... | inj₁ α<β = inj₁ (s<s α<β)
... | inj₂ α≈β = inj₂ (s≈s α≈β)
```

左边是后继右边是极限的情况, 反演 `suc α ≤ lim f` 得 `α ≤ f n ∸ d ≤ f n`, 对它使用归纳假设得到两个分支.

- 若 `α < f n`, 有 `suc α < f n < lim f`.
- 若 `α ≈ f n`, 有 `α ≈ f n < lim f`, 所以同样有 `suc α < lim f`.

```agda
≤-split {suc α} {lim f} wfα (wfn , mono) (s≤ α≤fn∸d)
  with ≤-split wfα wfn (≤∸⇒≤ α≤fn∸d)
... | inj₁ α<fn = inj₁ (s<l mono (<f⇒<l α<fn))
... | inj₂ α≈fn = inj₁ (s<l mono (begin-strict α ≤⟨ proj₁ α≈fn ⟩ _ <⟨ f<l mono ⟩ lim f ∎))
```

左边是极限右边是后继的情况, 对 `lim f ≤ suc β` 使用引理 `l≤s⇒l≤` 得到 `lim f ≤ β`, 对它使用归纳假设得到两个分支.

- 若 `lim f < β`, 有 `lim f < β < suc β`.
- 若 `lim f ≈ β`, 同样有 `lim f ≈ β < suc β`.

```agda
≤-split {lim f} {suc β} wfα wfβ l≤β
  with ≤-split wfα wfβ (l≤s⇒l≤ wfβ wfα l≤β)
... | inj₁ l<β = inj₁ (begin-strict lim f <⟨ l<β ⟩ β <⟨ <s ⟩ suc β ∎)
... | inj₂ l≈β = inj₁ (≤⇒<s (proj₁ l≈β))
```

最后一种两边都是极限的情况, 与 `≤-total` 类似, 我们用排中律.

- 若 `∀ n → g n ≤ lim f`, 即 `lim g ≤ lim f`. 结合前提 `lim f ≤ lim g` 即 `lim f ≈ lim g`.
- 若不然, 存在 `n` 使得 `g n ≰ lim f`, 由引理 `≰⇒≥` 即 `lim f ≤ g n`. 又 `g n < lim g`, 所以 `lim f < lim g`. 注意 `≰⇒≥` 使用了 `≤-total`, 所以这里也是互递归调用.

```agda
≤-split {lim f} {lim g} wfα wfβ f≤g with LEM {P = ∀ n → g n ≤ lim f}
... | _ because ofʸ gn≤l = inj₂ (f≤g , l≤ gn≤l)
... | _ because ofⁿ gn≰l with ¬∀⇒∃¬ gn≰l
...   | (n , gn≰l) = inj₁ (begin-strict lim f ≤⟨ ≰⇒≥ (proj₁ wfβ) wfα gn≰l ⟩
                                        g n   <⟨ f<l (proj₂ wfβ) ⟩
                                        lim g ∎)
```
