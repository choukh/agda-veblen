---
title: Agda大序数(1-2) 良构序数
zhihu-tags: Agda, 序数, 大数数学
zhihu-url: https://zhuanlan.zhihu.com/p/573846653
---

# Agda大序数(1-2) 良构序数

> 交流Q群: 893531731  
> 目录: [NonWellFormed.html](https://choukh.github.io/agda-lvo/NonWellFormed.html)  
> 本文源码: [WellFormed.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/NonWellFormed/WellFormed.lagda.md)  
> 高亮渲染: [WellFormed.html](https://choukh.github.io/agda-lvo/NonWellFormed.WellFormed.html)  
> 如果你在知乎看到本文: 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

```agda
{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --overlapping-instances #-}

module NonWellFormed.WellFormed where
```

## 前置

本章在内容上延续上一章.

```agda
open import NonWellFormed.Ordinal
open NonWellFormed.Ordinal.≤-Reasoning
```

标准库依赖大部分都在上一章出现过. 注意 Agda 有构造子重载, `ℕ` 的 `zero` 和 `suc` 与 `Ord` 的同名, 但只要类型明确就没有问题. `_↩_` 表示存在左逆, 其强度介于等价和同构之间. `MonoSequence₁` 是函数对序关系的单调性.

```agda
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat as ℕ using (ℕ; zero; suc; z≤n)
open import Data.Nat.Properties as ℕ using (m≤n⇒m<n∨m≡n)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Function using (_∘_; _↩_; it)
open import Relation.Binary using (Monotonic₁)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; _≢_; refl; sym; cong; subst)
```

## 良构

我们说序列 `f : ℕ → Ord` **单调**, 如果 `f` *保持* `ℕ.<` 到 `Ord.<`.

```agda
monoSequence : (ℕ → Ord) → Set
monoSequence = Monotonic₁ ℕ._<_ _<_
```

由于要作为 [instance参数](https://agda.readthedocs.io/en/v2.6.2.2.20221106/language/instance-arguments.html), 形式上做了一层 record 封装.

```agda
record MonoSequence (f : ℕ → Ord) : Set where
  constructor wrap
  field unwrap : monoSequence f

fm<fn : ∀ {f} → ⦃ MonoSequence f ⦄ → monoSequence f
fm<fn = MonoSequence.unwrap it
```

由单调序列的极限构成的序数我们称为**良构**序数. 注意这是递归定义, 序列的每一项也要求良构. 平凡地, 零以及良构序数的后继也是良构序数.

```agda
WellFormed : Ord → Set
WellFormed zero    = ⊤
WellFormed (suc α) = WellFormed α
WellFormed (lim f) = (∀ {n} → WellFormed (f n)) × MonoSequence f
```

以下 instance 用于从良构极限序数推出其序列每一项良构以及序列单调.

```agda
instance
  wf⇒wf : ∀ {f} → ⦃ WellFormed (lim f) ⦄ → ∀ {n} → WellFormed (f n)
  wf⇒wf ⦃ wf ⦄ = proj₁ wf

  wf⇒mono : ∀ {f} → ⦃ WellFormed (lim f) ⦄ → MonoSequence f
  wf⇒mono ⦃ wf ⦄ = proj₂ wf
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
⌜_⌝-wellFormed : ∀ n → WellFormed ⌜ n ⌝
⌜ zero ⌝-wellFormed  = tt
⌜ suc n ⌝-wellFormed = ⌜ n ⌝-wellFormed
```

**引理** `⌜_⌝` 是单调的.  
**证明** 即证 `m < n` 蕴含 `⌜m⌝ < ⌜n⌝`. 只需考虑 `n` 是后继的情况, 即 `m < suc n`, 拆开分别讨论 `m < n` 和 `m = n` 并用归纳假设即可. ∎

```agda
⌜⌝-monoSequence : MonoSequence ⌜_⌝
⌜⌝-monoSequence = wrap mono where
  mono : monoSequence ⌜_⌝
  mono {m} {suc n} (ℕ.s≤s m≤n) with (m≤n⇒m<n∨m≡n m≤n)
  ... | inj₁ m<n  = begin-strict ⌜ m ⌝ <⟨ mono m<n ⟩ ⌜ n ⌝ <⟨ <s ⟩ suc ⌜ n ⌝ ∎
  ... | inj₂ refl = begin-strict ⌜ m ⌝ <⟨ <s ⟩ suc ⌜ m ⌝ ∎
```

以上两条引理说明 `ω` 是良构序数.

```agda
ω-wellFormed : WellFormed ω
ω-wellFormed = (λ {n} → ⌜ n ⌝-wellFormed) , ⌜⌝-monoSequence
```

### `ω` 的性质

以下三条引理表明 `ω` 严格大于任意有限序数.

```agda
z<ω : zero < ω
z<ω = (1 , inj₁ tt) , z≤

s<ω : ∀ {α} → α < ω → suc α < ω
s<ω {α} ((n , d) , ≤) = (suc n , inj₁ tt) ,
  (begin suc α ≤⟨ s≤s ≤ ⟩ suc (⌜ n ⌝ ∸ d) ≤⟨ s∸≤ ⟩ ⌜ n ⌝ ∎)

instance
  n<ω : ∀ {n} → ⌜ n ⌝ < ω
  n<ω {zero}  = z<ω
  n<ω {suc n} = s<ω n<ω

  n≤ω : ∀ {n} → ⌜ n ⌝ ≤ ω
  n≤ω = <⇒≤ n<ω
```

以下引理将 `monoSequence` 的 `f m < f n` 结论特化到 `f n < f (suc n)`, 因为它在接下来的证明中经常用到.

```agda
fn<fsn : ∀ {f n} → ⦃ MonoSequence f ⦄ → f n < f (suc n)
fn<fsn ⦃ wrap mono ⦄ = mono (ℕ.s≤s ℕ.≤-refl)
```

**引理** 单调序列的第 `n` 项不会小于 `n` 自身.

```agda
⌜n⌝≤fn : ∀ {f n} → ⦃ MonoSequence f ⦄ → ⌜ n ⌝ ≤ f n
⌜n⌝≤fn {f} {zero}  = z≤
⌜n⌝≤fn {f} {suc n} = begin
  suc ⌜ n ⌝          ≤⟨ s≤s ⌜n⌝≤fn ⟩
  suc (f n)          ≤⟨ <⇒s≤ fn<fsn ⟩
  f (suc n)          ∎
```

我们称单调序列的极限为单调极限序数, 它比良构极限序数更宽泛, 但足以证明一些良好的性质. 如:

**引理** `ω` 是最小的单调极限序数.

```agda
ω≤l : ∀ {f} → ⦃ MonoSequence f ⦄ → ω ≤ lim f
ω≤l = l≤ λ n → ≤f⇒≤l ⌜n⌝≤fn
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
⌜⌝-surjective : ∀ {α} → ⦃ WellFormed α ⦄ → α < ω → ∃[ n ] α ≡ ⌜ n ⌝
⌜⌝-surjective {zero} _ = 0 , refl
⌜⌝-surjective {suc α} s<ω with ⌜⌝-surjective (<-trans <s s<ω)
... | n , ≡⌜n⌝ = suc n , cong suc ≡⌜n⌝
⌜⌝-surjective {lim f} l<ω = ⊥-elim (<⇒≱ l<ω ω≤l)
```

**推论** 小于 `ω` 的良构序数与自然数等价.

```agda
∃[<ω]wf↩ℕ : (∃[ α ] α < ω × WellFormed α) ↩ ℕ
∃[<ω]wf↩ℕ = record
  { to        = λ (α , <ω , wf) → proj₁ (⌜⌝-surjective ⦃ wf ⦄ <ω)
  ; from      = λ n → ⌜ n ⌝ , n<ω , ⌜ n ⌝-wellFormed
  ; to-cong   = λ{ refl → refl }
  ; from-cong = λ{ refl → refl }
  ; inverseˡ   = λ n → ⌜⌝-injective (sym (proj₂ (⌜⌝-surjective ⦃ ⌜ n ⌝-wellFormed ⦄ n<ω)))
  }
```

## 单调极限序数的性质

**引理** 任意单调极限序数严格大于零.

```agda
z<l : ∀ {f} → ⦃ MonoSequence f ⦄ → zero < lim f
z<l = <-≤-trans z<ω ω≤l
```

`f<l` 是上一章 [`f≤l`](Ordinal.html#7884) 的 `_<_` 版, 它要求 `f` 单调.

```agda
f<l : ∀ {f n} → ⦃ MonoSequence f ⦄ → f n < lim f
f<l = <-≤-trans fn<fsn f≤l
```

**引理** 单调序列在其极限内有任意大的项.  
**证明**

- 对于零, 我们有 `f 1` 大于它.
- 对于后继序数 `suc α`, 由归纳假设我们有 `f n` 大于 `α`, 由传递性有 `f (suc n)` 大于 `suc α`.
- 对于极限序数 `lim g`, 存在 `f n` 大于 `lim g`. ∎

```agda
∃[n]<fn : ∀ {α f} → ⦃ MonoSequence f ⦄ → α < lim f → ∃[ n ] α < f n
∃[n]<fn {zero} {f} _ = 1 , ≤-<-trans z≤ fn<fsn
∃[n]<fn {suc α} {f} s<l with ∃[n]<fn (<-trans <s s<l)
... | n , <f = suc n , (begin-strict
  suc α                 ≤⟨ <⇒s≤ <f ⟩
  f n                   <⟨ fn<fsn ⟩
  f (suc n)             ∎)
∃[n]<fn {lim g} ((n , d) , l<f) = n , d , l<f
```

**推论** 两个单调极限序数的序关系可以反演到它们的序列项.  
**证明** 由 `lim f ≤ lim g` 有 `f n < f (suc n) ≤ lim g`, 套入上一条即得. ∎

```agda
module _ {f g} ⦃ f-mono : MonoSequence f ⦄ ⦃ g-mono : MonoSequence g ⦄ where
  ∃[m]fn<gm : lim f ≤ lim g → ∀ n → ∃[ m ] f n < g m
  ∃[m]fn<gm (l≤ fn≤l) n = ∃[n]<fn (begin-strict
    f n                            <⟨ fn<fsn ⟩
    f (suc n)                      ≤⟨ fn≤l (suc n) ⟩
    lim g                          ∎)
```

**推论** 可以将 `s<ω` 的结论一般化到任意单调极限序数.  
**证明** 由 `∃[n]<fn`, 存在 `n` 使得 `α < f n`, 即 `suc α ≤ f n`, 又 `f n < f (suc n) < lim f`, 由传递性即证. ∎

```agda
<l⇒s<l : ∀ {α f} → ⦃ MonoSequence f ⦄ → α < lim f → suc α < lim f
<l⇒s<l {α} {f} ⦃ mono ⦄ < with ∃[n]<fn <
... | n , <f = begin-strict suc α ≤⟨ <⇒s≤ <f ⟩ f n <⟨ f<l ⟩ lim f ∎
```

**引理** 上一条的逆否命题成立.  
**证明** 与 `∃[m]fn<gm` 类似的思路. ∎

```agda
l≤s⇒l≤ : ∀ {f α} → ⦃ MonoSequence f ⦄ → lim f ≤ suc α → lim f ≤ α
l≤s⇒l≤ {f} {α} ⦃ mono ⦄ (l≤ fn≤s) = l≤ λ n → <s⇒≤ (begin-strict
  f n       <⟨ fn<fsn ⟩
  f (suc n) ≤⟨ fn≤s (suc n) ⟩
  suc α     ∎)
```

**推论** 后继无限序数的直接前驱也是无限序数.  
**证明** 这是上一条的直接推论. ∎

```agda
ω≤s⇒ω≤ : ∀ {α} → ω ≤ suc α → ω ≤ α
ω≤s⇒ω≤ ω≤s = l≤s⇒l≤ ⦃ ⌜⌝-monoSequence ⦄ ω≤s
```

### ≤-单调

还有一种更弱的单调序列, 叫做非严格单调.

```agda
≤-monoSequence : (ℕ → Ord) → Set
≤-monoSequence = Monotonic₁ ℕ._≤_ _≤_
```

**事实** 非严格单调蕴含严格单调.

```agda
<⇒≤-mono : ∀ {f} → ⦃ MonoSequence f ⦄ → ≤-monoSequence f
<⇒≤-mono ⦃ wrap mono ⦄ ≤ with m≤n⇒m<n∨m≡n ≤
... | inj₁ < = <⇒≤ (mono <)
... | inj₂ refl = ≤-refl
```

**事实** 非严格单调序列的极限与起始无关.  
**证明** 这可看作是上一章 `l≈ls` 的推广, 用类似思路可证. ∎

```agda
module _ {f h} (≤-mono : ≤-monoSequence f) (incr : ∀ n → n ℕ.< h n) where
  l≈l∘ : lim f ≈ lim (f ∘ h)
  l≈l∘ = l≤ (λ { ℕ.zero   → ≤f⇒≤l {n = 0} (≤-mono z≤n)
              ; (ℕ.suc n) → ≤f⇒≤l (≤-mono (incr n)) })
      , l≤ λ n → ≤f⇒≤l (≤-mono (ℕ.<⇒≤ (incr (h n))))
```

## 良构序数的性质

良构序数允许我们建立内涵等词与序关系的联系. 如:

**引理** 非零良构序数大于零.

```agda
≢z⇒>z : ∀ {α} → ⦃ WellFormed α ⦄ → α ≢ zero → α > zero
≢z⇒>z {zero}  z≢z = ⊥-elim (z≢z refl)
≢z⇒>z {suc α} _   = inj₁ tt , z≤
≢z⇒>z {lim f} _   = z<l
```

**引理** 外延等于零的良构序数就是零.

```agda
≈z⇒≡z : ∀ {α} → ⦃ WellFormed α ⦄ → α ≈ zero → α ≡ zero
≈z⇒≡z {zero}  _         = refl
≈z⇒≡z {suc α} (s≤z , _) = ⊥-elim (s≰z s≤z)
≈z⇒≡z {lim f} (l≤z , _) = ⊥-elim (<⇒≱ z<l l≤z)
```

**引理** 小于等于零的良构序数就是零.

```agda
≤z⇒≡z : ∀ {α} → ⦃ WellFormed α ⦄ → α ≤ zero → α ≡ zero
≤z⇒≡z ≤z = ≈z⇒≡z (≤z , z≤)
```

良构序数还允许我们证明貌似要排中律才能得到的结果. 如:

**引理** 良构序数要么是零, 要么大于零.

```agda
≡z⊎>z : ∀ α → ⦃ WellFormed α ⦄ → α ≡ zero ⊎ α > zero
≡z⊎>z zero    = inj₁ refl
≡z⊎>z (suc α) = inj₂ z<s
≡z⊎>z (lim f) = inj₂ (z<l)
```

**引理** 良构序数要么有限, 要么无限.

```agda
<ω⊎≥ω : ∀ α → ⦃ WellFormed α ⦄ → α < ω ⊎ α ≥ ω
<ω⊎≥ω zero     = inj₁ z<ω
<ω⊎≥ω (suc α) with <ω⊎≥ω α
... | inj₁ <ω  = inj₁ (s<ω <ω)
... | inj₂ ≥ω  = inj₂ (≤⇒≤s ≥ω)
<ω⊎≥ω (lim f)  = inj₂ ω≤l
```

## 经典序数

在良构序数的基础上加入排中律可以得到经典序数, 可证 `_≤_` 的线序性. 这部分内容与主线无关, 且非 `--safe`, 我们把它放在了[独立的一章](Ordinal.Classic.html).
