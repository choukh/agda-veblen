---
title: Agda大序数(2) 良构序数
zhihu-tags: Agda, 序数, 大数数学
zhihu-url: https://zhuanlan.zhihu.com/p/573846653
---

# Agda大序数(2) 良构序数

> 交流Q群: 893531731  
> 总目录: [Everything.html](https://choukh.github.io/agda-lvo/Everything.html)  
> 本文源码: [Ordinal/WellFormed.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/Ordinal/WellFormed.lagda.md)  
> 高亮渲染: [Ordinal.WellFormed.html](https://choukh.github.io/agda-lvo/Ordinal.WellFormed.html)  
> 如果你在知乎看到本文: 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

```agda
{-# OPTIONS --without-K --safe #-}

module Ordinal.WellFormed where
```

## 前置

本章在内容上延续上一章.

```agda
open import Ordinal
open Ordinal.≤-Reasoning
```

标准库依赖大部分都在上一章出现过. 注意 Agda 有构造子重载, `ℕ` 的 `zero` 和 `suc` 与 `Ord` 的同名, 但只要类型明确就没有问题. `_↩_` 表示存在左逆, 其强度介于等价和同构之间. `Monotonic₁` 是函数对序关系的单调性.

```agda
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Nat.Properties as ℕ using (m≤n⇒m<n∨m≡n)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Function using (_↩_)
open import Relation.Binary using (Monotonic₁)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst)
```

## 良构

我们说序列 `f : ℕ → Ord` **单调**, 如果 `f` *保持* `ℕ.<` 到 `Ord.<`.

```agda
monotonic : (ℕ → Ord) → Set
monotonic f = Monotonic₁ ℕ._<_ _<_ f
```

由单调序列的极限构成的序数我们称为**良构**序数. 注意这是递归定义, 序列的每一项也要求良构. 平凡地, 零以及良构序数的后继也是良构序数.

```agda
wellFormed : Ord → Set
wellFormed zero    = ⊤
wellFormed (suc α) = wellFormed α
wellFormed (lim f) = (∀ {n} → wellFormed (f n)) × monotonic f
```

## 有限序数与 `ω`

我们看几个简单的例子. 把 `ℕ` 嵌入到 `Ord` 可以得到有限序数 `⌜n⌝`.

```agda
⌜_⌝ : ℕ → Ord
⌜ zero ⌝ = zero
⌜ suc n ⌝ = suc ⌜ n ⌝
```

定义 `ω` 为嵌入函数 `⌜_⌝` 的极限.

```agda
ω : Ord
ω = lim ⌜_⌝
```

简单的归纳法即可证明任意有限序数良构.

```agda
⌜_⌝-wellFormed : ∀ n → wellFormed ⌜ n ⌝
⌜ zero ⌝-wellFormed  = tt
⌜ suc n ⌝-wellFormed = ⌜ n ⌝-wellFormed
```

**引理** `⌜_⌝` 是单调的.  
**证明** 即证 `m < n` 蕴含 `⌜m⌝ < ⌜n⌝`. 只需考虑 `n` 是后继的情况, 即 `m < suc n`, 拆开分别讨论 `m < n` 和 `m = n` 并用归纳假设即可. ∎

```agda
⌜⌝-monotonic : monotonic ⌜_⌝
⌜⌝-monotonic {m} {suc n} (ℕ.s≤s m≤n) with (m≤n⇒m<n∨m≡n m≤n)
... | inj₁ m<n  = begin-strict ⌜ m ⌝ <⟨ ⌜⌝-monotonic m<n ⟩ ⌜ n ⌝ <⟨ <s ⟩ suc ⌜ n ⌝ ∎
... | inj₂ refl = begin-strict ⌜ m ⌝ <⟨ <s ⟩ suc ⌜ m ⌝ ∎
```

以上两条引理说明 `ω` 是良构序数.

```agda
ω-wellFormed : wellFormed ω
ω-wellFormed = (λ {n} → ⌜ n ⌝-wellFormed) , ⌜⌝-monotonic
```

### `ω` 的性质

以下三条引理表明 `ω` 严格大于任意有限序数.

```agda
z<ω : zero < ω
z<ω = (1 , inj₁ tt) , z≤

s<ω : ∀ {α} → α < ω → suc α < ω
s<ω {α} ((n , d) , ≤) = (suc n , inj₁ tt) ,
  (begin suc α ≤⟨ s≤s ≤ ⟩ suc (⌜ n ⌝ ∸ d) ≤⟨ s∸≤ ⟩ ⌜ n ⌝ ∎)

n<ω : ∀ {n} → ⌜ n ⌝ < ω
n<ω {zero}  = z<ω
n<ω {suc n} = s<ω n<ω
```

以下引理将 `monotonic` 的 `f m < f n` 结论特化到 `f n < f (suc n)`, 因为它在接下来的证明中经常用到.

```agda
fn<fsn : ∀ {f n} → monotonic f → f n < f (suc n)
fn<fsn mono = mono (ℕ.s≤s ℕ.≤-refl)
```

**引理** 单调序列的第 `n` 项不会小于 `n` 自身.

```agda
⌜n⌝≤fn : ∀ {f n} → monotonic f → ⌜ n ⌝ ≤ f n
⌜n⌝≤fn     {n = zero}  mono = z≤
⌜n⌝≤fn {f} {n = suc n} mono = begin
  suc ⌜ n ⌝ ≤⟨ s≤s (⌜n⌝≤fn mono) ⟩
  suc (f n) ≤⟨ <⇒s≤ (fn<fsn mono) ⟩
  f (suc n) ∎
```

我们称单调序列的极限为单调极限序数, 它比良构极限序数更宽泛, 但足以证明一些良好的性质. 如:

**引理** `ω` 是最小的单调极限序数.

```agda
ω≤l : ∀ {f} → monotonic f → ω ≤ lim f
ω≤l mono = l≤ λ n → ≤f⇒≤l (⌜n⌝≤fn mono)
```

### 等价性

**引理** `⌜_⌝` 是自然数到良构序数的单射.

```agda
⌜⌝-injective : ∀ {m n} → ⌜ m ⌝ ≡ ⌜ n ⌝ → m ≡ n
⌜⌝-injective {zero}  {zero}  eq = refl
⌜⌝-injective {suc m} {suc n} eq = cong suc (⌜⌝-injective (suc-injective eq))
```

**引理** 小于 `ω` 的良构序数被 `⌜_⌝` 满射.

```agda
⌜⌝-surjective : ∀ {α} → α < ω → wellFormed α → ∃[ n ] α ≡ ⌜ n ⌝
⌜⌝-surjective {zero}  _  _ = 0 , refl
⌜⌝-surjective {suc α} s<ω wf
  with ⌜⌝-surjective α<ω wf
  where α<ω = begin-strict α <⟨ <s ⟩ suc α <⟨ s<ω ⟩ ω ∎
... | n , ≡⌜n⌝ = suc n , cong suc ≡⌜n⌝
⌜⌝-surjective {lim f} l<ω (_ , mono) = ⊥-elim (<⇒≱ l<ω (ω≤l mono))
```

**推论** 小于 `ω` 的良构序数与自然数等价.

```agda
∃[<ω]wf↩ℕ : (∃[ α ] α < ω × wellFormed α) ↩ ℕ
∃[<ω]wf↩ℕ = record
  { to        = λ (α , <ω , wf) → proj₁ (⌜⌝-surjective <ω wf)
  ; from      = λ n → ⌜ n ⌝ , n<ω , ⌜ n ⌝-wellFormed
  ; to-cong   = λ{ refl → refl }
  ; from-cong = λ{ refl → refl }
  ; inverseˡ   = λ n → ⌜⌝-injective (sym (proj₂ (⌜⌝-surjective n<ω ⌜ n ⌝-wellFormed)))
  }
```

## 单调极限序数的性质

**引理** 任意单调极限序数严格大于零.

```agda
z<l : ∀ {f} → monotonic f → zero < lim f
z<l {f} mono = begin-strict zero <⟨ z<ω ⟩ ω ≤⟨ ω≤l mono ⟩ lim f ∎
```

`f<l` 是上一章 [`f≤l`](Ordinal.html#7698) 的 `_<_` 版, 它要求 `f` 单调.

```agda
f<l : ∀ {f n} → monotonic f → f n < lim f
f<l {f} {n} mono = begin-strict f n <⟨ fn<fsn mono ⟩ f (suc n) ≤⟨ f≤l ⟩ lim f ∎
```

**引理** 单调序列在其极限内有任意大的项.  
**证明**

- 对于零, 我们有 `f 1` 大于它.
- 对于后继序数 `suc α`, 由归纳假设我们有 `f n` 大于 `α`, 由传递性有 `f (suc n)` 大于 `suc α`.
- 对于极限序数 `lim g`, 存在 `f n` 大于 `lim g`. ∎

```agda
∃[n]<fn : ∀ {α f} → monotonic f → α < lim f → ∃[ n ] α < f n
∃[n]<fn {zero}  {f} mono _ = 1 ,
  (begin-strict zero ≤⟨ z≤ ⟩ f 0 <⟨ fn<fsn mono ⟩ f 1 ∎)
∃[n]<fn {suc α} {f} mono s<l
  with ∃[n]<fn mono (begin-strict α <⟨ <s ⟩ suc α <⟨ s<l ⟩ lim f ∎)
... | n , <f = suc n ,
  (begin-strict suc α ≤⟨ <⇒s≤ <f ⟩ f n <⟨ fn<fsn mono ⟩ f (suc n) ∎)
∃[n]<fn {lim g} mono ((n , d) , l<f) = n , d , l<f
```

**引理** 可以将 `s<ω` 的结论一般化到任意单调极限序数.  
**证明** 由上一条, 存在 `n` 使得 `α < f n`, 即 `suc α ≤ f n`, 又 `f n < f (suc n) < lim f`, 由传递性即证. ∎

```agda
s<l : ∀ {α f} → monotonic f → α < lim f → suc α < lim f
s<l {α} {f} mono < with ∃[n]<fn mono <
... | n , <f = begin-strict suc α ≤⟨ <⇒s≤ <f ⟩ f n <⟨ f<l mono ⟩ lim f ∎
```

## 良构序数的性质

良构序数允许我们建立内涵等词与序关系的联系. 如:

**引理** 非零良构序数大于零.

```agda
≢z⇒>z : ∀ {α} → wellFormed α → α ≢ zero → α > zero
≢z⇒>z {zero}  _          z≢z = ⊥-elim (z≢z refl)
≢z⇒>z {suc α} _          _   = inj₁ tt , z≤
≢z⇒>z {lim f} (_ , mono) _   = z<l mono
```

**引理** 外延等于零的良构序数就是零.

```agda
≈z⇒≡z : ∀ {α} → wellFormed α → α ≈ zero → α ≡ zero
≈z⇒≡z {zero}  _          _         = refl
≈z⇒≡z {suc α} _          (s≤z , _) = ⊥-elim (s≰z s≤z)
≈z⇒≡z {lim f} (_ , mono) (l≤z , _) = ⊥-elim (<⇒≱ (z<l mono) l≤z)
```

**引理** 小于等于零的良构序数就是零.

```agda
≤z⇒≡z : ∀ {α} → wellFormed α → α ≤ zero → α ≡ zero
≤z⇒≡z wf ≤z = ≈z⇒≡z wf (≤z , z≤)
```

良构序数还允许我们证明貌似要排中律才能得到的结果. 如:

**引理** 良构序数要么是零, 要么大于零.

```agda
≡z⊎>z : ∀ {α} → wellFormed α → α ≡ zero ⊎ α > zero
≡z⊎>z {zero}  _          = inj₁ refl
≡z⊎>z {suc α} _          = inj₂ (z<s α)
≡z⊎>z {lim f} (_ , mono) = inj₂ (z<l mono)
```

**引理** 良构序数要么有限, 要么无限.

```agda
<ω⊎≥ω : ∀ {α} → wellFormed α → α < ω ⊎ α ≥ ω
<ω⊎≥ω {zero}  _                = inj₁ z<ω
<ω⊎≥ω {suc α} wf with <ω⊎≥ω wf
...                 | inj₁ <ω  = inj₁ (s<ω <ω)
...                 | inj₂ ≥ω  = inj₂ (≤⇒≤s ≥ω)
<ω⊎≥ω {lim f} (_ , mono)       = inj₂ (ω≤l mono)
```

**引理** 良构无限后继序数的直接前驱也是无限序数.  
**证明** 这是上一条的简单推论. ∎

```agda
ω≤s⇒ω≤ : ∀ {α} → wellFormed α → ω ≤ suc α → ω ≤ α
ω≤s⇒ω≤ wf ω≤s with <ω⊎≥ω wf
...                  | inj₁ <ω = ⊥-elim (≤⇒≯ ω≤s (s<ω <ω))
...                  | inj₂ ≥ω = ≥ω
```

## 经典序数

在良构序数的基础上加入排中律可以得到经典序数, 可证 `_≤_` 的线序性. 这部分内容与主线无关, 且非 `--safe`, 我们把它放在了[独立的一章](Ordinal.Classic.html).
