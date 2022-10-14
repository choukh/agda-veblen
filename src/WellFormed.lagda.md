---
title: Agda大序数(2) 良构序数
zhihu-tags: Agda, 序数, 大数数学
---

# Agda大序数(2) 良构序数

> 交流Q群: 893531731  
> 本文源码: [WellFormed.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/WellFormed.lagda.md)  
> GitHub Pages: [WellFormed.html](https://choukh.github.io/agda-lvo/WellFormed.html)  
> 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

```agda
{-# OPTIONS --without-K --safe #-}

module WellFormed where
```

我们完整导入了第一章的内容. 其他都是常规模块. 只是注意 Agda 有构造子重载, `ℕ` 的 `zero` 和 `suc` 与 `Ord` 的同名, 但只要类型明确就没有问题.

```agda
open import Ordinal
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Nat.Properties as ℕ using (m≤n⇒m<n∨m≡n)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; cong; subst)
```

## 良构

我们说序列 `f : ℕ → Ord` **单调**, 如果 `f` *保持* `ℕ.<` 到 `Ord.<`.

```agda
monotonic : (ℕ → Ord) → Set
monotonic f = ∀ {m n} → m ℕ.< n → f m < f n
```

由单调序列的极限构成的序数我们称为**良构**序数. 注意这是递归定义, 序列的每一项也要求良构. 此外平凡地, 零以及良构序数的后继也是良构序数.

```agda
wellFormed : Ord → Set
wellFormed zero    = ⊤
wellFormed (suc α) = wellFormed α
wellFormed (lim f) = (∀ {n} → wellFormed (f n)) × monotonic f
```

### 有限序数与ω

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

`⌜_⌝` 是单调的, 即 `m < n` 蕴含 `⌜m⌝ < ⌜n⌝`. 只需考虑 `n` 是后继的情况, 即 `m < suc n`, 拆开分别讨论 `m < n` 和 `m = n` 用归纳假设即可.

```agda
⌜⌝-monotonic : monotonic ⌜_⌝
⌜⌝-monotonic {m} {suc n} (ℕ.s≤s m≤n) with (m≤n⇒m<n∨m≡n m≤n)
... | inj₁ m<n = <-trans (⌜⌝-monotonic m<n) <s
... | inj₂ refl = <s
```

以上两条引理说明 `ω` 是良构序数.

```agda
ω-wellFormed : wellFormed ω
ω-wellFormed = (λ {n} → ⌜ n ⌝-wellFormed) , ⌜⌝-monotonic
```

我们来证明以下关于 `ω` 的引理. 以下三条表明 `ω` 严格大于任意有限序数.

```agda
z<ω : zero < ω
z<ω = (1 , inj₁ tt) , z≤

s<ω : ∀ {α} → α < ω → suc α < ω
s<ω ((n , d) , ≤) = (suc n , inj₁ tt) , ≤-trans (s≤s ≤) s∸≤

n<ω : ∀ {n} → ⌜ n ⌝ < ω
n<ω {zero } = z<ω
n<ω {suc n} = s<ω n<ω
```

下面的引理将 `monotonic` 的 `f m < f n` 结论特化到 `f n < f (suc n)`, 因为它在接下来的证明中经常用到.

```agda
fn<fsn : ∀ {f n} → monotonic f → f n < f (suc n)
fn<fsn mono = mono (ℕ.s≤s ℕ.≤-refl)
```

以下引理表明将任意 `n` 输入进单调的 `f` 得到的结果不会小于 `n` 自身.

```agda
⌜n⌝≤fn : ∀ {f n} → monotonic f → ⌜ n ⌝ ≤ f n
⌜n⌝≤fn {n = zero}  mono = z≤
⌜n⌝≤fn {n = suc n} mono = ≤-trans (s≤s (⌜n⌝≤fn mono)) (<→s≤ (fn<fsn mono))

ω≤l : ∀ {f} → monotonic f → ω ≤ lim f
ω≤l mono = l≤ (λ n → ≤→≤l (⌜n⌝≤fn mono))

z<l : ∀ {f} → monotonic f → zero < lim f
z<l mono = <→≤→< z<ω (ω≤l mono)
```

```agda
∃[n]<fn : ∀ {α f} → monotonic f → α < lim f → ∃[ n ] α < f n
∃[n]<fn {zero}  mono _ = 1 , (≤→<→< z≤ (mono ℕ.z<s))
∃[n]<fn {suc α} mono s<l with ∃[n]<fn mono (<-trans <s s<l)
... | n , <f = (suc n) , (≤→<→< (<→s≤ <f) (fn<fsn mono))
∃[n]<fn {lim g} mono ((n , d) , l<f) = n , (≤→<→< l<f (d , ≤-refl))
```

```agda
s<l : ∀ {α f} → monotonic f → α < lim f → suc α < lim f
s<l mono < with ∃[n]<fn mono <
... | n , <f with (fn<fsn mono)
... | d , f<fs = ((suc n) , d) , ≤-trans (<→s≤ <f) f<fs
```

```agda
f<l : ∀ {f n} → monotonic f → f n < lim f
f<l mono = <→≤→< (fn<fsn mono) f≤l
```

```agda
f1≢z : ∀ {f} → monotonic f → f 1 ≢ zero
f1≢z {f} mono f1≡z = proj₁ (subst (f 0 <_) f1≡z (fn<fsn mono))
```

```agda
≢z→>z : ∀ {α} → wellFormed α → α ≢ zero → α > zero
≢z→>z {zero}  _ ≢z = ⊥-elim (≢z refl)
≢z→>z {suc α} _ _ = (inj₁ tt) , z≤
≢z→>z {lim f} (wf , mono) ≢z = <→<l (≢z→>z wf (f1≢z mono))
```

```agda
≈z→≡z : ∀ {α} → wellFormed α → α ≈ zero → α ≡ zero
≈z→≡z {zero} _ _ = refl
≈z→≡z {suc α} _ (≤z , _) = ⊥-elim (s≰z ≤z)
≈z→≡z {lim f} (wf , mono) (≤z , _) = ⊥-elim (<⇒≱ (≢z→>z wf (f1≢z mono)) (l≤→≤ ≤z))
```

```agda
≤z→≡z : ∀ {α} → wellFormed α → α ≤ zero → α ≡ zero
≤z→≡z wf ≤z = ≈z→≡z wf (≤z , z≤)
```

```agda
≡z⊎>z : ∀ {α} → wellFormed α → α ≡ zero ⊎ α > zero
≡z⊎>z {zero}  _           = inj₁ refl
≡z⊎>z {suc α} _           = inj₂ (z<s α)
≡z⊎>z {lim f} (wf , mono) = inj₂ (<→<l (≢z→>z wf (f1≢z mono)))
```

```agda
<ω⊎≥ω : ∀ {α} → wellFormed α → α < ω ⊎ α ≥ ω
<ω⊎≥ω {zero}  _               = inj₁ z<ω
<ω⊎≥ω {suc α} wf with <ω⊎≥ω wf
...                 | inj₁ <ω = inj₁ (s<ω <ω)
...                 | inj₂ ≥ω = inj₂ (≤-trans ≥ω ≤s)
<ω⊎≥ω {lim f} (_ , mono)      = inj₂ (ω≤l mono)
```

```agda
ω≤s→ω≤ : ∀ {α} → wellFormed α → ω ≤ suc α → ω ≤ α
ω≤s→ω≤ {α} wf ω≤s with <ω⊎≥ω wf
...                  | inj₁ <ω = ⊥-elim (≤⇒≯ ω≤s (s<ω <ω))
...                  | inj₂ ≥ω = ≥ω
```

```agda
∃[n]≡⌜n⌝ : ∀ {α} → wellFormed α → α < ω → ∃[ n ] α ≡ ⌜ n ⌝
∃[n]≡⌜n⌝ {zero} _ _ = 0 , refl
∃[n]≡⌜n⌝ {suc α} wf <ω with ∃[n]≡⌜n⌝ wf (<-trans <s <ω)
... | n , ≡⌜n⌝ = (suc n) , cong suc ≡⌜n⌝
∃[n]≡⌜n⌝ {lim f} (_ , mono) <ω = ⊥-elim (<⇒≱ <ω (ω≤l mono))
```
