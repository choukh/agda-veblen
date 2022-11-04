---
title: Agda大序数(6) 迭代幂次
zhihu-tags: Agda, 序数, 大数数学
zhihu-url: https://zhuanlan.zhihu.com/p/580526275
---

# Agda大序数(6) 迭代幂次

> 交流Q群: 893531731  
> 总目录: [Everything.html](https://choukh.github.io/agda-lvo/Everything.html)  
> 本文源码: [Ordinal/Tetration.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/Ordinal/Tetration.lagda.md)  
> 高亮渲染: [Ordinal.Tetration.html](https://choukh.github.io/agda-lvo/Ordinal.Tetration.html)  
> 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

本章打开了 [*实验性有损合一化*](https://agda.readthedocs.io/en/v2.6.2.2/language/lossy-unification.html) 特性, 它可以减少显式标记隐式参数的需要, 而且跟 `--safe` 是兼容的. 当然它也有一些缺点, 具体这里不会展开.

```agda
{-# OPTIONS --without-K --safe --experimental-lossy-unification #-}

module Ordinal.Tetration where
```

## 前置

本章在内容上延续前五章.

```agda
open import Ordinal
open Ordinal.≤-Reasoning
open import Ordinal.WellFormed
open import Ordinal.Function using (≤-monotonic; <-monotonic)
open import Ordinal.Recursion using (rec_from_by_; rec-by-mono-≤)
open import Ordinal.Arithmetic
```

以下标准库依赖在前几章都出现过.

```agda
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (refl; cong)
```

上一章讲了序数算术. 将后继视作第零级运算, 通过迭代超限递归, 我们定义了三个级别的运算: 加法, 乘法和幂运算. 朴素的想法是可以这样一直迭代下去, 得到越来越高等级的运算. 本章的主要目的是展示这样的朴素想法是行不通的.

有两种可能的方法定义第四级运算, 一种是递归左侧幂运算 `_^`, 一种是递归右侧幂运算 `^_`. 回想上一章我们知道左侧 `_^` 强增长而右侧 `^_` 不是, 于是我们先来尝试递归左侧.

## 递归左侧

模块名已经剧透了, 这种运算不是我们真正想要的第四级运算.

```agda
private module NotTetration where
```

不妨以左元 `α` 为初始值, 递归 `_^`.

```
  _^^_ : Ord → Ord → Ord
  α ^^ β = rec (_^ α) from α by β
```

问题在于, 这种运算完全可以用上一级运算表示, 而没有真正的突破.

```agda
  naïve : ∀ α β → α ^^ β ≈ α ^ (α ^ β)
  naïve α zero    = begin-equality
    α ^^ zero       ≡⟨⟩
    α               ≈˘⟨ ^-identityʳ _ ⟩
    α ^ ⌜ 1 ⌝       ≡⟨ cong (α ^_) refl ⟩
    α ^ (α ^ zero)  ∎
  naïve α (suc β) = begin-equality
    α ^^ suc β      ≡⟨⟩
    α ^^ β ^ α      ≈⟨ ^-congʳ (naïve _ _) ⟩
    α ^ (α ^ β) ^ α ≈⟨ ^-*-assoc _ _ _ ⟩
    α ^ (α ^ β * α) ≡⟨⟩
    α ^ (α ^ suc β) ∎
  naïve α (lim f) = l≈l (naïve α (f _))
```

## 迭代幂次

我们真正想要的第四级运算叫做迭代幂次, 由右侧幂运算 `^_` 递归得到. 与前三级不同的是, 迭代幂次的初始值具有一些讨论的价值[^1], 我们定义以下记法, 把初始值也作为参数, 写在方括号中.

[^1]: _ 我们后面会看到, 相同的序数可以有不同初始值的迭代幂次表示.

```agda
_^^[_]_ : Ord → Ord → Ord → Ord
α ^^[ τ ] β = rec (α ^_) from τ by β
```

直观上迭代幂次是一个指数塔 $α^{α^{α^{.^{.^{.^{τ}}}}}}$, `τ` 是塔顶的数字, `β` 是幂运算总共进行的次数. 特别地, 若 `τ = α`, 则简记作 `α ^^ β`.

```agda
infixl 9 _^^_

_^^_ : Ord → Ord → Ord
α ^^ β = α ^^[ α ] β
```

它们有如下基本关系: 最顶层可以换成其 `⌜ 1 ⌝` 次幂而值不变. 非形式地, $α^{α^{.^{.^{.^{α}}}}}$ ≈ $α^{α^{.^{.^{.^{α^{1}}}}}}$.

```agda
^^≈^^[1]s : ∀ α β → α ≥ ⌜ 1 ⌝ → α ^^ β ≈ α ^^[ ⌜ 1 ⌝ ] suc β
^^≈^^[1]s α zero    α≥1 = ≈-sym (^-identityʳ α)
^^≈^^[1]s α (suc β) α≥1 = ^-congˡ α≥1 (^^≈^^[1]s α β α≥1)
^^≈^^[1]s α (lim f) α≥1 = l≈l (^^≈^^[1]s α (f _) α≥1)
```

另外, 当迭代次数有限的时候, `α ^^[ _ ] n` 单调.

```agda
^^[]-mono-≤ : ∀ α n → α ≥ ⌜ 1 ⌝ → ≤-monotonic (α ^^[_] ⌜ n ⌝)
^^[]-mono-≤ α zero    _   ≤ = ≤
^^[]-mono-≤ α (suc n) α≥1 ≤ = ^-monoʳ-≤ α α≥1 (^^[]-mono-≤ α n α≥1 ≤)

^^[]-mono-< : ∀ α n → α > ⌜ 1 ⌝ → <-monotonic (α ^^[_] ⌜ n ⌝)
^^[]-mono-< α zero    _   < = <
^^[]-mono-< α (suc n) α>1 < = ^-monoʳ-< α α>1 (^^[]-mono-< α n α>1 <)
```

由此可知将最顶层换成大于 `⌜ 1 ⌝` 的幂将使值增长.

```agda
^^≤^^[]s : ∀ α τ n → α ≥ ⌜ 1 ⌝ → τ ≥ ⌜ 1 ⌝ → α ^^ ⌜ n ⌝ ≤ α ^^[ τ ] ⌜ suc n ⌝
^^≤^^[]s α τ n α≥1 τ≥1  = begin
  α ^^ ⌜ n ⌝              ≈⟨ ^^≈^^[1]s α ⌜ n ⌝ α≥1 ⟩
  α ^^[ ⌜ 1 ⌝ ] ⌜ suc n ⌝ ≤⟨ ^^[]-mono-≤ α (suc n) α≥1 τ≥1 ⟩
  α ^^[ τ ] ⌜ suc n ⌝     ∎

^^<^^[]s : ∀ α τ n → α > ⌜ 1 ⌝ → τ > ⌜ 1 ⌝ → α ^^ ⌜ n ⌝ < α ^^[ τ ] ⌜ suc n ⌝
^^<^^[]s α τ n α>1 τ>1  = begin-strict
  α ^^ ⌜ n ⌝              ≈⟨ ^^≈^^[1]s α ⌜ n ⌝ (<⇒≤ α>1) ⟩
  α ^^[ ⌜ 1 ⌝ ] ⌜ suc n ⌝ <⟨ ^^[]-mono-< α (suc n) α>1 τ>1 ⟩
  α ^^[ τ ] ⌜ suc n ⌝     ∎
```

而当迭代次数达到 `ω` 的时候, 不大于底数的初始值将无关紧要.

```agda
^^≈^^[]ω : ∀ α τ → ⌜ 1 ⌝ ≤ τ → τ ≤ α → α ^^ ω ≈ α ^^[ τ ] ω
^^≈^^[]ω α τ 1≤τ τ≤α =
    l≤ (λ n → begin
      α ^^ ⌜ n ⌝          ≤⟨ ^^≤^^[]s α τ n (≤-trans 1≤τ τ≤α) 1≤τ ⟩
      α ^^[ τ ] ⌜ suc n ⌝ ≤⟨ f≤l {n = suc n} ⟩
      α ^^[ τ ] ω         ∎)
  , l≤ (λ n → begin
      α ^^[ τ ] ⌜ n ⌝     ≤⟨ ^^[]-mono-≤ α n (≤-trans 1≤τ τ≤α) τ≤α ⟩
      α ^^ ⌜ n ⌝          ≤⟨ f≤l ⟩
      α ^^ ω              ∎)
```

再加一层也无济于事.

```agda
^^≈^^[]sω : ∀ α τ → α ≥ τ → τ ≥ ⌜ 1 ⌝ → α ^^ suc ω ≈ α ^^[ τ ] suc ω
^^≈^^[]sω α τ α≥τ τ≥1 = ^-congˡ (≤-trans τ≥1 α≥τ) (^^≈^^[]ω α τ τ≥1 α≥τ)
```

这就导致迭代幂次到 `ω` 层就卡住了.

```agda
^^-stuck : ∀ α → α ≥ ⌜ 1 ⌝ → α ^^ suc ω ≈ α ^^ ω
^^-stuck α α≥1 = begin-equality
  α ^^ suc ω          ≈⟨ ^^≈^^[]sω α ⌜ 1 ⌝ α≥1 ≤-refl ⟩
  α ^^[ ⌜ 1 ⌝ ] suc ω ≈˘⟨ ^^≈^^[1]s α ω α≥1 ⟩
  α ^^ ω              ∎
```

而且迭代幂次的超限层全部卡住了. 这与 `^_` 不保证强增长是一致的. 我们现在知道精确的节点, 就是到 `ω` 层之后就不再增长.

```agda
^^-monoʳ-≤ : ∀ α → α > ⌜ 1 ⌝ → ≤-monotonic (α ^^_)
^^-monoʳ-≤ α α>1 = rec-by-mono-≤ (^-monoʳ-≤ α (<⇒≤ α>1)) (λ β → ^-incrʳ-≤ β α α>1)

^^-stuck-forever : ∀ α β → α > ⌜ 1 ⌝ → wellFormed β → β ≥ ω → α ^^ β ≈ α ^^ ω
^^-stuck-forever α zero    α>1 wfβ β≥ω = ⊥-elim (≤⇒≯ β≥ω z<ω)
^^-stuck-forever α (suc β) α>1 wfβ β≥ω = (begin
    α ^^ suc β                            ≡⟨⟩
    α ^ α ^^ β                            ≤⟨ ^-monoʳ-≤ α (<⇒≤ α>1) (proj₁ IH) ⟩
    α ^ α ^^ ω                            ≡⟨⟩
    α ^^ suc ω                            ≈⟨ ^^-stuck α (<⇒≤ α>1) ⟩
    α ^^ ω                                ∎)
  , ^^-monoʳ-≤ α α>1 β≥ω
    where IH = ^^-stuck-forever α β α>1 wfβ (ω≤s⇒ω≤ wfβ β≥ω)
^^-stuck-forever α (lim f) α>1 (wfn , mono) β≥ω = l≤ helperˡ , l≤ helperʳ where
  helperˡ : ∀ n → α ^^ f n ≤ α ^^ ω
  helperˡ n with <ω⊎≥ω (wfn {n})
  ...       | inj₁ fn<ω with ⌜⌝-surjective fn<ω wfn
  ...                   | (m , eq) =      begin
    α ^^ f n                              ≡⟨ cong (α ^^_) eq ⟩
    α ^^ ⌜ m ⌝                            ≤⟨ f≤l ⟩
    α ^^ ω                                ∎
  helperˡ n | inj₂ ω<fn =                 begin
    α ^^ f n                              ≤⟨ proj₁ IH ⟩
    α ^^ ω                                ∎ where
    IH = ^^-stuck-forever α (f n) α>1 wfn ω<fn
  helperʳ : ∀ n → α ^^ ⌜ n ⌝ ≤ α ^^ lim f
  helperʳ n with <ω⊎≥ω (wfn {n})
  ...       | inj₁ fn<ω =                 begin
    α ^^ ⌜ n ⌝                            ≤⟨ ^^-monoʳ-≤ α α>1 (⌜n⌝≤fn mono) ⟩
    α ^^ f n                              ≤⟨ f≤l ⟩
    α ^^ lim f                            ∎
  ...       | inj₂ ω<fn = begin
    α ^^ ⌜ n ⌝                            ≤⟨ ^^-monoʳ-≤ α α>1 (<⇒≤ n<ω) ⟩
    α ^^ ω                                ≤⟨ proj₂ IH ⟩
    α ^^ f n                              ≤⟨ f≤l ⟩
    α ^^ lim f                            ∎ where
    IH = ^^-stuck-forever α (f n) α>1 wfn ω<fn
```

现在我们陷入两难的境地. 一方面 `_^` 保证强增长, 但增长地很慢; 另一方面 `^_` 在有限层增长地很快, 但不在超限层的增长. 实际上 `α ^^ ω` 是一个 Veblen 不动点, 我们将在下一章介绍跳出不动点的方法.
