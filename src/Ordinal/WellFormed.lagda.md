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
> 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

```agda
{-# OPTIONS --without-K --safe #-}

module Ordinal.WellFormed where
```

我们导入第一章的内容和标准库的常规模块. 注意 Agda 有构造子重载, `ℕ` 的 `zero` 和 `suc` 与 `Ord` 的同名, 但只要类型明确就没有问题.

```agda
open import Ordinal
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Nat.Properties as ℕ using (m≤n⇒m<n∨m≡n)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst)
open import Function using (_↩_)
```

## 良构

我们说序列 `f : ℕ → Ord` **递增**, 如果 `f` *保持* `ℕ.<` 到 `Ord.<`.

```agda
increasing : (ℕ → Ord) → Set
increasing f = ∀ {m n} → m ℕ.< n → f m < f n
```

由递增序列的极限构成的序数我们称为**良构**序数. 注意这是递归定义, 序列的每一项也要求良构. 平凡地, 零以及良构序数的后继也是良构序数.

```agda
wellFormed : Ord → Set
wellFormed zero    = ⊤
wellFormed (suc α) = wellFormed α
wellFormed (lim f) = (∀ {n} → wellFormed (f n)) × increasing f
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

**引理** `⌜_⌝` 是递增的.  
**证明** 即证 `m < n` 蕴含 `⌜m⌝ < ⌜n⌝`. 只需考虑 `n` 是后继的情况, 即 `m < suc n`, 拆开分别讨论 `m < n` 和 `m = n` 并用归纳假设即可. ∎

```agda
⌜⌝-increasing : increasing ⌜_⌝
⌜⌝-increasing {m} {suc n} (ℕ.s≤s m≤n) with (m≤n⇒m<n∨m≡n m≤n)
... | inj₁ m<n = <-trans (⌜⌝-increasing m<n) <s
... | inj₂ refl = <s
```

以上两条引理说明 `ω` 是良构序数.

```agda
ω-wellFormed : wellFormed ω
ω-wellFormed = (λ {n} → ⌜ n ⌝-wellFormed) , ⌜⌝-increasing
```

### `ω` 的性质

以下三条引理表明 `ω` 严格大于任意有限序数.

```agda
z<ω : zero < ω
z<ω = (1 , inj₁ tt) , z≤

s<ω : ∀ {α} → α < ω → suc α < ω
s<ω ((n , d) , ≤) = (suc n , inj₁ tt) , ≤-trans (s≤s ≤) s∸≤

n<ω : ∀ {n} → ⌜ n ⌝ < ω
n<ω {zero}  = z<ω
n<ω {suc n} = s<ω n<ω
```

以下引理将 `increasing` 的 `f m < f n` 结论特化到 `f n < f (suc n)`, 因为它在接下来的证明中经常用到.

```agda
fn<fsn : ∀ {f n} → increasing f → f n < f (suc n)
fn<fsn inc = inc (ℕ.s≤s ℕ.≤-refl)
```

**引理** 递增序列的第 `n` 项不会小于 `n` 自身.

```agda
⌜n⌝≤fn : ∀ {f n} → increasing f → ⌜ n ⌝ ≤ f n
⌜n⌝≤fn {n = zero}  inc = z≤
⌜n⌝≤fn {n = suc n} inc = ≤-trans (s≤s (⌜n⌝≤fn inc)) (<→s≤ (fn<fsn inc))
```

我们称递增序列的极限为递增极限序数, 它比良构极限序数更宽泛, 但足以证明一些良好的性质. 如:

**引理** `ω` 是最小的递增极限序数.

```agda
ω≤l : ∀ {f} → increasing f → ω ≤ lim f
ω≤l inc = l≤ (λ n → ≤→≤l (⌜n⌝≤fn inc))
```

### 等价性

**引理** `⌜_⌝` 是自然数到良构序数的单射.

```agda
⌜⌝-injective : ∀ {m n} → ⌜ m ⌝ ≡ ⌜ n ⌝ → m ≡ n
⌜⌝-injective {zero} {zero} eq = refl
⌜⌝-injective {suc m} {suc n} eq = cong suc (⌜⌝-injective (suc-injective eq))
```

**引理** 小于 `ω` 的良构序数被 `⌜_⌝` 满射.

```agda
⌜⌝-surjective : ∀ {α} → α < ω → wellFormed α → ∃[ n ] α ≡ ⌜ n ⌝
⌜⌝-surjective {zero}  _  _          = 0 , refl
⌜⌝-surjective {suc α} <ω wf with ⌜⌝-surjective (<-trans <s <ω) wf
... | n , ≡⌜n⌝                      = (suc n) , cong suc ≡⌜n⌝
⌜⌝-surjective {lim f} <ω (_ , inc) = ⊥-elim (<⇒≱ <ω (ω≤l inc))
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

## 递增极限序数的性质

**引理** 任意递增极限序数严格大于零.

```agda
z<l : ∀ {f} → increasing f → zero < lim f
z<l inc = <-≤-trans z<ω (ω≤l inc)
```

`f<l` 是上一章 [`f≤l`](Ordinal.html#7694) 的 `_<_` 版, 它要求 `f` 递增.

```agda
f<l : ∀ {f n} → increasing f → f n < lim f
f<l inc = <-≤-trans (fn<fsn inc) f≤l
```

**引理** 递增序列在其极限内有任意大的项.  
**证明**
- 对于零, 我们有 `f 1` 大于它.
- 对于后继序数 `suc α`, 由归纳假设我们有 `f n` 大于 `α`, 取 `f (suc n)`, 由传递性可证它大于 `suc α`.
- 对于极限序数 `lim g`, 存在 `f n` 大于 `lim g`. ∎

```agda
∃[n]<fn : ∀ {α f} → increasing f → α < lim f → ∃[ n ] α < f n
∃[n]<fn {zero}  inc _ = 1 , (≤-<-trans z≤ (fn<fsn inc))
∃[n]<fn {suc α} inc s<l with ∃[n]<fn inc (<-trans <s s<l)
... | n , <f = (suc n) , (≤-<-trans (<→s≤ <f) (fn<fsn inc))
∃[n]<fn {lim g} inc ((n , d) , l<f) = n , d , l<f
```

**引理** 可以将 `s<ω` 的结论一般化到任意递增极限序数.  
**证明** 由上一条, 存在 `n` 使得 `α < f n`, 即 `suc α ≤ f n`, 又 `f n < f (suc n) < lim f`, 由传递性即证. ∎

```agda
s<l : ∀ {α f} → increasing f → α < lim f → suc α < lim f
s<l inc < with ∃[n]<fn inc <
... | n , <f = ≤-<-trans (<→s≤ <f) (f<l inc)
```

## 良构序数的性质

良构序数允许我们建立内涵等词与序关系的联系. 如:

**引理** 非零良构序数大于零.

```agda
≢z→>z : ∀ {α} → wellFormed α → α ≢ zero → α > zero
≢z→>z {zero}  _         z≢z = ⊥-elim (z≢z refl)
≢z→>z {suc α} _         _   = (inj₁ tt) , z≤
≢z→>z {lim f} (_ , inc) _   = z<l inc
```

**引理** 外延等于零的良构序数就是零.

```agda
≈z→≡z : ∀ {α} → wellFormed α → α ≈ zero → α ≡ zero
≈z→≡z {zero}  _         _         = refl
≈z→≡z {suc α} _         (s≤z , _) = ⊥-elim (s≰z s≤z)
≈z→≡z {lim f} (_ , inc) (l≤z , _) = ⊥-elim (<⇒≱ (z<l inc) l≤z)
```

**引理** 小于等于零的良构序数就是零.

```agda
≤z→≡z : ∀ {α} → wellFormed α → α ≤ zero → α ≡ zero
≤z→≡z wf ≤z = ≈z→≡z wf (≤z , z≤)
```

良构序数还允许我们证明貌似要排中律才能得到的结果. 如:

**引理** 良构序数要么是零, 要么大于零.

```agda
≡z⊎>z : ∀ {α} → wellFormed α → α ≡ zero ⊎ α > zero
≡z⊎>z {zero}  _         = inj₁ refl
≡z⊎>z {suc α} _         = inj₂ (z<s α)
≡z⊎>z {lim f} (_ , inc) = inj₂ (z<l inc)
```

**引理** 良构序数要么有限, 要么无限.

```agda
<ω⊎≥ω : ∀ {α} → wellFormed α → α < ω ⊎ α ≥ ω
<ω⊎≥ω {zero}  _               = inj₁ z<ω
<ω⊎≥ω {suc α} wf with <ω⊎≥ω wf
...                 | inj₁ <ω = inj₁ (s<ω <ω)
...                 | inj₂ ≥ω = inj₂ (≤-trans ≥ω ≤s)
<ω⊎≥ω {lim f} (_ , inc)       = inj₂ (ω≤l inc)
```

**引理** 良构无限后继序数的直接前驱也是无限序数.  
**证明** 这是上一条的简单推论. ∎

```agda
ω≤s→ω≤ : ∀ {α} → wellFormed α → ω ≤ suc α → ω ≤ α
ω≤s→ω≤ wf ω≤s with <ω⊎≥ω wf
...                  | inj₁ <ω = ⊥-elim (≤⇒≯ ω≤s (s<ω <ω))
...                  | inj₂ ≥ω = ≥ω
```

## 经典序数

在良构序数的基础上加入排中律可以得到经典序数, 可证 `_≤_` 的线序性. 这部分内容与主线无关, 且非 `--safe`, 我们把它放在了[独立的一章](Ordinal.Classic.html).
