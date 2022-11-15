---
title: Agda大序数(9) 二元Veblen函数
zhihu-tags: Agda, 序数, 大数数学
---

# Agda大序数(9) 二元Veblen函数

> 交流Q群: 893531731  
> 总目录: [Everything.html](https://choukh.github.io/agda-lvo/Everything.html)  
> 本文源码: [Veblen/Function.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/Veblen/Function.lagda.md)  
> 高亮渲染: [Veblen.Function.html](https://choukh.github.io/agda-lvo/Veblen.Function.html)  
> 如果你在知乎看到本文: 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

**(本章施工中)**

```agda
{-# OPTIONS --without-K --safe #-}

module Veblen.Function where
```

## 前置

```agda
open import Ordinal
open Ordinal.≤-Reasoning
open import Ordinal.WellFormed using (ω; ⌜_⌝)
open import Ordinal.Function
open import Ordinal.Recursion
open import Ordinal.Arithmetic using (_^_)
open import Veblen.Fixpoint
open import Veblen.Epsilon using (ω^-normal; ε; ζ; η)

open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Function using (_∘_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
```

## 定义

上一章讲到, 将 `ω ^_`, `ε`, `ζ`, `η` 分别看作第0, 1, 2, 3层级, 可以推广到任意序数层级, 从而得到二元 Veblen 函数.

形式上, 我们需要辅助函数 `veblen`, 它是一个高阶函数, 接受一个序数函数 `F` 作为初始值, 并接受一个序数 `α` 作为 `_′` 的迭代次数, 返回迭代后的序数函数. 于是 `φ` 就定义为以 `ω ^_` 为初始值的 `_′` 迭代.

**注意** 极限情况下的形式较为复杂. naive地看似乎 `F ∘ₗ f` 就够了, 但为了更好的性质以及更高的增长率要再套一层 `_⁺`.

```agda
veblen : (Ord → Ord) → Ord → (Ord → Ord)
_∘ₗ_ : (Ord → Ord) → (ℕ → Ord) → (Ord → Ord)

veblen F zero    = F
veblen F (suc α) = (veblen F α) ′
veblen F (lim f) = (F ∘ₗ f) ⁺
F ∘ₗ f = λ α → lim (λ n → veblen F (f n) α)

φ : Ord → Ord → Ord
φ = veblen (ω ^_)
```

由定义有

$$φ_{0}(α) = ω^α$$

```agda
_ : φ ⌜ 0 ⌝ ≡ ω ^_
_ = refl
```
&nbsp;

$$φ_{1}(α) = ε_α$$

```agda
_ : φ ⌜ 1 ⌝ ≡ ε
_ = refl
```
&nbsp;

$$φ_{2}(α) = ζ_α$$

```agda
_ : φ ⌜ 2 ⌝ ≡ ζ
_ = refl
```
&nbsp;

$$φ_{3}(α) = η_α$$

```agda
_ : φ ⌜ 3 ⌝ ≡ η
_ = refl
```
&nbsp;

$$φ_{α+1}(β) = {φ_{α}}'(β)$$

```agda
_ : ∀ α → φ (suc α) ≡ (φ α) ′
_ = λ _ → refl
```

第一个参数是极限时又按第二个参数分三种情况:

$$φ_{\lim f}(0) = \sup\{φ_{f(0)}(0), φ_{f(1)}(0), φ_{f(2)}(0), ...\}$$

或者按基本序列记作

$$φ_{γ}(0)[n] = φ_{γ[n]}(0)$$

我们今后都采用这种非形式记法.

```agda
_ : ∀ f → φ (lim f) ⌜ 0 ⌝ ≡ lim (λ n → φ (f n) ⌜ 0 ⌝)
_ = λ _ → refl
```

后继的情况有

$$φ_{γ}(α+1)[n] = φ_{γ[n]}(φ_{γ}(α)+1)$$

```agda
_ : ∀ f α → φ (lim f) (suc α) ≡ lim (λ n → φ (f n) (suc (φ (lim f) α)))
_ = λ _ _ → refl
```

两个参数都是极限的情况:

$$φ_{α}(γ)[n] = φ_{α}(γ[n])$$

```agda
_ : ∀ f g → φ (lim f) (lim g) ≡ lim (λ n → φ (lim f) (g n))
_ = λ _ _ → refl
```

## 性质

如所期望的那样, 每个 `φ α` 都是序数嵌入.

```agda
φ-normal : ∀ α → normal (φ α)
φ-normal zero    = ω^-normal
φ-normal (suc α) = ′-normal (φ-normal α)
φ-normal (lim f) = ⁺-normal ((ω ^_) ∘ₗ f) ≤-mono <-incr where
  ≤-mono : ≤-monotonic ((ω ^_) ∘ₗ f ∘ suc)
  ≤-mono {α} {β} ≤ = l≤ (λ n →  begin
    φ (f n) (suc α)             ≤⟨ proj₁ (φ-normal (f n)) (s≤s ≤) ⟩
    φ (f n) (suc β)             ≤⟨ f≤l ⟩
    ((ω ^_) ∘ₗ f) (suc β)       ∎)
  <-incr : <-increasing ((ω ^_) ∘ₗ f ∘ suc)
  <-incr α =                    begin-strict
    α                           <⟨ <s ⟩
    suc α                       ≤⟨ normal⇒≤-incr (φ-normal (f 0)) (suc α) ⟩
    φ (f 0) (suc α)             ≤⟨ f≤l ⟩
    ((ω ^_) ∘ₗ f) (suc α)       ∎
```

由此可知每个 `φ (suc α) β` 也是 `φ α` 的不动点.

$$φ_α(φ_{α+1}(β))=φ_{α+1}(β)$$

```agda
φ-fp-suc : ∀ α β → (φ (suc α) β) isFixpointOf (φ α)
φ-fp-suc α β = ′-fp (φ-normal α) β
```
