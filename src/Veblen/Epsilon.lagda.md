---
title: Agda大序数(8) ε层级, ζ层级, η层级
zhihu-tags: Agda, 序数, 大数数学
zhihu-url: https://zhuanlan.zhihu.com/p/582661842
---

# Agda大序数(8) ε层级, ζ层级, η层级

> 交流Q群: 893531731  
> 总目录: [Everything.html](https://choukh.github.io/agda-lvo/Everything.html)  
> 本文源码: [Veblen/Epsilon.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/Veblen/Epsilon.lagda.md)  
> 高亮渲染: [Veblen.Epsilon.html](https://choukh.github.io/agda-lvo/Veblen.Epsilon.html)  
> 如果你在知乎看到本文: 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

```agda
{-# OPTIONS --without-K --safe --experimental-lossy-unification #-}
{-# OPTIONS --no-qualified-instances #-}

module Veblen.Epsilon where
```

## 前置

```agda
open import Ordinal
open Ordinal.≤-Reasoning
open import Ordinal.WellFormed hiding (wf⇒wf)
open import Ordinal.Function using (normal; wf-preserving; zero-increasing; suc-increasing)
open import Ordinal.Recursion using (rec_from_by_)
open import Ordinal.Arithmetic
open import Ordinal.Tetration using (_^^ω; _^^ω[_]; ^^≈^^[]ω; ^^-stuck; ^-^^[]-comm)
open import Veblen.Fixpoint

open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
```

## 引理

本小节统一列出本章所需关于 `ω ^_` 的一些平凡的引理.

```agda
ω^-normal : normal (ω ^_)
ω^-normal = ^-normal ω

ω^-wfp : wf-preserving (ω ^_)
ω^-wfp = ^-wfp ω-wellFormed

ω^-zero-incr : zero-increasing (ω ^_)
ω^-zero-incr =        begin-strict
  zero                <⟨ <s ⟩
  ⌜ 1 ⌝               ≡⟨⟩
  ω ^ zero            ∎

ω^-suc-incr : suc-increasing (ω ^_)
ω^-suc-incr α with ≡z⊎>z α
... | inj₁ refl =     begin-strict
  ⌜ 1 ⌝               <⟨ n<ω ⟩
  ω                   ≈˘⟨ ^-identityʳ ω ⟩
  ω ^ ⌜ 1 ⌝           ∎
... | inj₂ α>0 =      begin-strict
  suc α               ≤⟨ +-monoʳ-≤ α (<⇒s≤ α>0) ⟩
  α + α               ≈˘⟨ α*2≈α+α α ⟩
  α * ⌜ 2 ⌝           <⟨ *-monoʳ-< α ⦃ α>0 ⦄ (n<ω {2}) ⟩
  α * ω               ≤⟨ *-monoˡ-≤ ω (^-incrʳ-≤ α ω) ⟩
  ω ^ α * ω           ∎
```

## ε层级

`ε` 定义为对函数 `ω ^_` 的不动点的枚举. 由于 `ω ^_` 是序数嵌入, 所以 `ε` 也是序数嵌入, 且对任意 `α` 有 `ω ^ ε α ≈ ε α`.

```agda
ε : Ord → Ord
ε = (ω ^_) ′

ε-normal : normal ε
ε-normal = ′-normal ω^-normal

ε-fp : ∀ α → ε α isFixpointOf (ω ^_)
ε-fp α = ′-fp ω^-normal α
```

由 `ω ^_` 以及 `_′` 的相关引理可证 `ε` 保良构.

```agda
ε-wfp : wf-preserving ε
ε-wfp = ′-wfp ω^-normal ω^-zero-incr ω^-suc-incr ω^-wfp
```

`ε zero` 是无穷层的 ω 指数塔.

$$ε_{0} = ω^{ω^{.^{.^{.^{ω}}}}}$$

```agda
ε₀ : ε zero ≈ ω ^^ω
ε₀ =                  begin-equality
  ε zero              ≈˘⟨ ε-fp zero ⟩
  ω ^ ω ^^ω[ zero ]   ≈⟨ ^-^^[]-comm ω zero ω ⟩
  ω ^^ω[ ω ^ zero ]   ≡⟨⟩
  ω ^^ω[ ⌜ 1 ⌝ ]      ≈˘⟨ ^^≈^^[]ω ω ⌜ 1 ⌝ n≤ω ⦃ ≤-refl ⦄ ⟩
  ω ^^ω               ∎
```

后继的情况:

$$ε_{α+1} = ω^{ω^{.^{.^{.^{ε_{α}}}}}}$$

```agda
_ : ∀ α → ε (suc α) ≡ ω ^^ω[ suc (ε α) ]
_ = λ α → refl
```

极限的情况:

$$ε_{\lim f} = \sup \{ε_{f(0)},ε_{f(1)},ε_{f(2)},...\}$$

```agda
_ : ∀ f → ε (lim f) ≡ lim (λ n → ε (f n))
_ = λ f → refl
```

## `ε` 的另一种表示

可以证明对任意良构 `α` 有 [`ε (suc α) ≈ ε α ^^ ω`](Veblen.Epsilon.Alternative.html#5145).

## ζ层级

由于 `ε` 是序数嵌入, 它也存在不动点, 这些不动点组成了 ζ层级, 且 `ζ` 也是序数嵌入.

```agda
ζ : Ord → Ord
ζ = ε ′

ζ-normal : normal ζ
ζ-normal = ′-normal ε-normal
```

对任意 `α` 有 `ε (ζ α) ≈ ζ α`.

```agda
ζ-fp : ∀ α → ζ α isFixpointOf ε
ζ-fp α = ′-fp ε-normal α
```

`ζ` 保良构.

```agda
ε-zero-incr : zero-increasing ε
ε-zero-incr = ′-zero-incr ω^-zero-incr

ε-suc-incr : suc-increasing ε
ε-suc-incr = ′-suc-incr ω^-normal ω^-suc-incr

ζ-wfp : wf-preserving ζ
ζ-wfp = ′-wfp ε-normal ε-zero-incr ε-suc-incr ε-wfp
```

$$ζ_0 = ε_{ε_{._{._{ε_0}}}}$$

```agda
_ : ζ zero ≡ ε ⋱ zero
_ = refl
```

$$ζ_{α+1} = ε_{ε_{._{._{{ζ_α}+1}}}}$$

```agda
_ : ∀ α → ζ (suc α) ≡ ε ⋱ suc (ζ α)
_ = λ α → refl
```

$$ζ_{\lim f} = \sup \{ζ_{f(0)},ζ_{f(1)},ζ_{f(2)},...\}$$

```agda
_ : ∀ f → ζ (lim f) ≡ lim (λ n → ζ (f n))
_ = λ f → refl
```

## η层级

由于 `ζ` 是序数嵌入, 它也存在不动点, 这些不动点组成了 η层级, 且 `η` 也是序数嵌入.

```agda
η : Ord → Ord
η = ζ ′

η-normal : normal η
η-normal = ′-normal ζ-normal
```

对任意 `α` 有 `ζ (η α) ≈ η α`.

```agda
η-fp : ∀ α → η α isFixpointOf ζ
η-fp α = ′-fp ζ-normal α
```

`η` 的保良构.

```agda
ζ-zero-incr : zero-increasing ζ
ζ-zero-incr = ′-zero-incr ε-zero-incr

ζ-suc-incr : suc-increasing ζ
ζ-suc-incr = ′-suc-incr ε-normal ε-suc-incr

η-wfp : wf-preserving η
η-wfp = ′-wfp ζ-normal ζ-zero-incr ζ-suc-incr ζ-wfp
```

$$η_0 = ζ_{ζ_{._{._{ζ_0}}}}$$

```agda
_ : η zero ≡ ζ ⋱ zero
_ = refl
```

$$η_{α+1} = ζ_{ζ_{._{._{{ζ_α}+1}}}}$$

```agda
_ : ∀ α → η (suc α) ≡ ζ ⋱ suc (η α)
_ = λ α → refl
```

$$η_{\lim f} = \sup \{η_{f(0)},η_{f(1)},η_{f(2)},...\}$$

```agda
_ : ∀ f → η (lim f) ≡ lim (λ n → η (f n))
_ = λ f → refl
```

符号是有限的, 不可能这样一直命名下去. 但是, 将 `ω ^_`, `ε`, `ζ`, `η` 分别看作第0, 1, 2, 3层级, 可以将其推广到任意序数层级, 从而得到著名的 Veblen 函数, 我们将在下一章介绍.
