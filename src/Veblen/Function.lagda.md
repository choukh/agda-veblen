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
{-# OPTIONS --without-K --safe --experimental-lossy-unification #-}

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

给定一个序数嵌入 `F`.

```agda
module Properties F (nml@(≤-mono , <-mono , lim-ct) : normal F) where
```

对 `veblen` 来说, 如果初始函数 `F` 是序数嵌入, 那么每个迭代 `veblen F α` 都是序数嵌入.

```agda
  veblen-normal : ∀ α → normal (veblen F α)
  veblen-normal zero    = nml
  veblen-normal (suc α) = ′-normal (veblen-normal α)
  veblen-normal (lim f) = ⁺-normal (F ∘ₗ f) mono incr where
    mono : ≤-monotonic (F ∘ₗ f)
    mono {α} {β} ≤ = l≤l (λ n → begin
      veblen F (f n) (α)        ≤⟨ proj₁ (veblen-normal (f n)) ≤ ⟩
      veblen F (f n) (β)        ∎)
    incr : ≤-increasing (F ∘ₗ f)
    incr α =                    begin
      α                         ≤⟨ normal⇒≤-incr (veblen-normal (f 0)) α ⟩
      veblen F (f 0) α          ≤⟨ f≤l ⟩
      (F ∘ₗ f) α                ∎
```

由此可知每个 `veblen F (suc α) γ` 也是 `veblen F α` 的不动点.

```agda
  veblen-fp-suc : ∀ α γ → (veblen F (suc α) γ) isFixpointOf (veblen F α)
  veblen-fp-suc α γ = ′-fp (veblen-normal α) γ
```

我们想把上面的事实推广到任意满足 `α < β` 的两个序数. 这需要一系列引理. 首先最基本的是 `veblen F` 对第一个参数的合同性, 而这又直接依赖于单调性.

```agda
  interleaved mutual
    veblen-monoˡ-≤ : ∀ γ → ≤-monotonic (λ α → veblen F α γ)
    veblen-monoˡ-≤l : ∀ f α → F α ≤ veblen F (lim f) α

    veblen-monoˡ-≤ γ {zero} {zero}  z≤ =        ≤-refl
    veblen-monoˡ-≤ γ {zero} {suc β} z≤ =        begin
      veblen F ⌜ 0 ⌝ γ                          ≤⟨ veblen-monoˡ-≤ γ z≤ ⟩
      veblen F β γ                              ≤⟨ ′-incrʰ-≤ (veblen-normal β) γ ⟩
      veblen F (suc β) γ                        ∎

    veblen-monoˡ-≤ γ {zero} {lim f} z≤ =        veblen-monoˡ-≤l f γ
    veblen-monoˡ-≤l f zero    =                 begin
      veblen F ⌜ 0 ⌝ ⌜ 0 ⌝                      ≤⟨ veblen-monoˡ-≤ ⌜ 0 ⌝ z≤ ⟩
      veblen F (f 0) ⌜ 0 ⌝                      ≤⟨ f≤l ⟩
      (F ∘ₗ f) ⌜ 0 ⌝                            ∎
    veblen-monoˡ-≤l f (suc α) =                 begin
      veblen F ⌜ 0 ⌝ (suc α)                    ≤⟨ veblen-monoˡ-≤ (suc α) z≤ ⟩
      veblen F (f 0) (suc α)                    ≤⟨ proj₁ (veblen-normal (f 0)) (s≤s ≤) ⟩
      veblen F (f 0) (suc (veblen F (lim f) α)) ≤⟨ f≤l ⟩
      (F ∘ₗ f) (suc (veblen F (lim f) α))       ∎ where
        ≤ : α ≤ veblen F (lim f) α
        ≤ = normal⇒≤-incr (veblen-normal (lim f)) α
    veblen-monoˡ-≤l f (lim g) =                 begin
      F (lim g)                                 ≈⟨ lim-ct g ⟩
      lim (λ n → F (g n))                       ≤⟨ l≤l (λ n → veblen-monoˡ-≤l f (g n)) ⟩
      lim (λ n → veblen F (lim f) (g n))        ∎

    veblen-monoˡ-≤ γ {suc α} {suc β} (s≤ α≤β) = begin
      veblen F (suc α) γ                        ≤⟨ ′-monoʰ-≤ (proj₁ (veblen-normal α)) IH ⟩
      veblen F (suc β) γ                        ∎ where
        IH = λ {γ} → veblen-monoˡ-≤ γ (<s⇒≤ (_ , α≤β))
    veblen-monoˡ-≤ γ {suc α} {lim f} (s≤ α<f) = {!   !}
    veblen-monoˡ-≤ γ {lim f} {β}     (l≤ f≤β) = {!   !}
```

最后, 我们将 `veblen` 的性质实例化到 `φ`.

```agda
open Properties (ω ^_) ω^-normal
```

每个 `φ α` 都是序数嵌入.

```agda
φ-normal : ∀ α → normal (φ α)
φ-normal = veblen-normal
```

$$φ_α(φ_{α+1}(β))=φ_{α+1}(β)$$

```agda
φ-fp-suc : ∀ α β → (φ (suc α) β) isFixpointOf (φ α)
φ-fp-suc = veblen-fp-suc
```

`φ` 对第一个参数的单调性.

```agda
φ-monoˡ-≤ : ∀ γ → ≤-monotonic (λ α → φ α γ)
φ-monoˡ-≤ = veblen-monoˡ-≤
```
