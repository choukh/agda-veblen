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
{-# OPTIONS --overlapping-instances #-}

module Veblen.Function where
```

## 前置

```agda
open import Ordinal
open import Ordinal.WellFormed
open import Ordinal.Function
open import Ordinal.Recursion
open import Ordinal.Arithmetic using (_^_)
open import Veblen.Fixpoint
open import Veblen.Epsilon using (ω^-normal; ε; ζ; η)

open Ordinal.≤-Reasoning
open Ordinal.WellFormed.NonStrictMono
  using (l≈l∘; <⇒≤-mono) renaming (≤-monotonic to ≤-mono-sequence)

open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Nat.Properties as ℕ using (m≤m+n; m<n+m)
open import Function using (_∘_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function.Definitions (_≈_) (_≈_) using (Congruent)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
```

## 定义

上一章讲到, 将 `ω ^_`, `ε`, `ζ`, `η` 分别看作第0, 1, 2, 3层级, 可以推广到任意序数层级, 从而得到二元 Ψ 函数.

形式上, 我们需要辅助函数 `Ψ`, 它是一个高阶函数, 接受一个序数函数 `F` 作为初始值, 并接受一个序数 `α` 作为 `_′` 的迭代次数, 返回迭代后的序数函数. 于是 `φ` 就定义为以 `ω ^_` 为初始值的 `_′` 迭代.

**注意** 极限情况下的形式较为复杂. naive地看似乎 `F ∘ₗ f` 就够了, 但为了更好的性质以及更高的增长率要再套一层 `_⁺`.

```agda
Ψ : (Ord → Ord) → Ord → (Ord → Ord)
_∘ₗ_ : (Ord → Ord) → (ℕ → Ord) → (Ord → Ord)

Ψ F zero    = F
Ψ F (suc α) = (Ψ F α) ′
Ψ F (lim f) = (F ∘ₗ f) ⁺
F ∘ₗ f = λ α → lim (λ n → Ψ F (f n) α)

φ : Ord → Ord → Ord
φ = Ψ (ω ^_)
```

由定义有

$$φ_{0}(α) = ω^α$$

```agda
_ : φ zero ≡ ω ^_
_ = refl
```

$$φ_{1}(α) = ε_α$$

```agda
_ : φ ⌜ 1 ⌝ ≡ ε
_ = refl
```

$$φ_{2}(α) = ζ_α$$

```agda
_ : φ ⌜ 2 ⌝ ≡ ζ
_ = refl
```

$$φ_{3}(α) = η_α$$

```agda
_ : φ ⌜ 3 ⌝ ≡ η
_ = refl
```

$$φ_{α+1}(β) = {φ_{α}}'(β)$$

```agda
_ : ∀ α → φ (suc α) ≡ (φ α) ′
_ = λ _ → refl
```

第一个参数是极限时又按第二个参数分三种情况:

$$φ_{γ}(0) = \sup\{φ_{γ[0]}(0), φ_{γ[1]}(0), φ_{γ[2]}(0), ...\}$$

或者按基本序列记作

$$φ_{γ}(0)[n] = φ_{γ[n]}(0)$$

我们今后都采用这种非形式记法.

```agda
_ : ∀ f → φ (lim f) zero ≡ lim (λ n → φ (f n) zero)
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

### 嵌入性, 单调性

**定理** 对 `Ψ` 来说, 如果初始函数 `F` 是序数嵌入, 那么每个迭代 `Ψ F α` 都是序数嵌入.

```agda
  Ψ-normal : ∀ α → normal (Ψ F α)

  Ψ-monoʳ-≤ : ∀ α → ≤-monotonic (Ψ F α)
  Ψ-monoʳ-≤ α = proj₁ (Ψ-normal α)

  Ψ-incrʳ-≤ : ∀ α → ≤-increasing (Ψ F α)
  Ψ-incrʳ-≤ α = normal⇒≤-incr (Ψ-normal α)

  Ψ-normal zero    = nml
  Ψ-normal (suc α) = ′-normal (Ψ-normal α)
  Ψ-normal (lim f) = ⁺-normal (F ∘ₗ f) mono incr where
    mono : ≤-monotonic (F ∘ₗ f)
    mono {α} {β} ≤ = l≤l λ n →  begin
      Ψ F (f n) (α)             ≤⟨ Ψ-monoʳ-≤ (f n) ≤ ⟩
      Ψ F (f n) (β)             ∎
    incr : ≤-increasing (F ∘ₗ f)
    incr α =                    begin
      α                         ≤⟨ Ψ-incrʳ-≤ (f 0) α ⟩
      Ψ F (f 0) α               ≤⟨ f≤l ⟩
      (F ∘ₗ f) α                ∎
```

**推论** `Ψ F` 对第二个参数满足合同性.

```agda
  Ψ-cong² : ∀ α → Congruent (Ψ F α)
  Ψ-cong² α = ≤-mono⇒cong (Ψ-monoʳ-≤ α)
```

**推论** `Ψ F` 对第二个参数满足极限连续.

```agda
  Ψ-lim-ct : ∀ α → lim-continuous (Ψ F α)
  Ψ-lim-ct α = proj₂ (proj₂ (Ψ-normal α))
```

**引理** 每个 `Ψ F (suc α) γ` 也是 `Ψ F α` 的不动点.

```agda
  Ψ-fp-suc : ∀ α γ → (Ψ F (suc α) γ) isFixpointOf (Ψ F α)
  Ψ-fp-suc α γ = ′-fp (Ψ-normal α) γ
```

我们想把上述事实推广到任意满足 `α < β` 的两个序数, 这需要先证明 `Ψ F` 对第一个参数的单调性.

**引理** `Ψ F` 对第一个参数满足单调性.

该命题较为繁琐. 首先在表述上, 参数要求是良构序数. 证明上, 要同时讨论 `_≤_` 的两边, 这就分出了九种情况, 然后还衍生出一个互递归命题又分出五种情况.

```agda
  Ψ-monoˡ-≤ : ∀ {α β γ} → ⦃ wellFormed α ⦄ → ⦃ wellFormed β ⦄ →
    α ≤ β → Ψ F α γ ≤ Ψ F β γ
  Ψ-monoˡ-≤l : ∀ {α f n γ} → ⦃ wellFormed α ⦄ → ⦃ ∀ {n} → wellFormed (f n) ⦄ →
    α ≤ f n → Ψ F α γ ≤ Ψ F (lim f) γ
```

**证明** 我们先证衍生命题. `γ` 为零或后继时都要递归调用主命题, 后继的情况还用到了第二个参数的序数嵌入条件.

```agda
  Ψ-monoˡ-≤l {α} {f} {n} {zero} α≤fn =    begin
    Ψ F α zero                            ≤⟨ Ψ-monoˡ-≤ α≤fn ⟩
    Ψ F (f n) zero                        ≤⟨ f≤l ⟩
    (F ∘ₗ f) zero                         ∎

  Ψ-monoˡ-≤l {α} {f} {n} {suc γ} α≤fn =   begin
    Ψ F α (suc γ)                         ≤⟨ Ψ-monoˡ-≤ α≤fn ⟩
    Ψ F (f n) (suc γ)                     ≤⟨ Ψ-monoʳ-≤ (f n) (s≤s (Ψ-incrʳ-≤ (lim f) γ)) ⟩
    Ψ F (f n) (suc (Ψ F (lim f) γ))       ≤⟨ f≤l ⟩
    (F ∘ₗ f) (suc (Ψ F (lim f) γ))        ∎
```

`γ` 为极限时要看 `α`. `α` 为零或后继时都要递归调用衍生命题, 为后继时还要递归调用主命题. `α` 为极限的情况使用 `_⁺` 的高阶单调性得证.

```agda
  Ψ-monoˡ-≤l {zero} {f} {n} {lim γ} z≤fn = begin
    F (lim γ)                             ≈⟨ lim-ct γ ⟩
    lim (λ n → F (γ n))                   ≤⟨ l≤l (λ n → Ψ-monoˡ-≤l {n = n} z≤) ⟩
    lim (λ n → Ψ F (lim f) (γ n))         ∎
  Ψ-monoˡ-≤l {suc α} {f} {n} {lim γ} sα≤fn = l≤l λ m → begin
    Ψ F (suc α) (γ m)                     ≤⟨ Ψ-monoˡ-≤ sα≤fn ⟩
    Ψ F (f n) (γ m)                       ≤⟨ Ψ-monoˡ-≤l ≤-refl ⟩
    Ψ F (lim f) (γ m)                     ∎
  Ψ-monoˡ-≤l {lim α} {β} {n} (l≤ α≤βn) = ⁺-monoʰ-≤ mono (l≤ ≤) where
    mono : ≤-monotonic (F ∘ₗ α)
    mono ≤ = l≤l λ _ → Ψ-monoʳ-≤ (α _) ≤
    ≤ : ∀ {ξ} m → Ψ F (α m) ξ ≤ (F ∘ₗ β) ξ
    ≤ {ξ} m =                             begin
      Ψ F (α m) ξ                         ≤⟨ Ψ-monoˡ-≤ (α≤βn m) ⟩
      Ψ F (β n) ξ                         ≤⟨ f≤l ⟩
      (F ∘ₗ β) ξ                          ∎
```

接着证明主命题. `α` 和 `β` 都为零时显然成立. `α` 为零 `β` 为后继时递归调用自身, 并使用 `_′` 的高阶增长性得证.

```agda
  Ψ-monoˡ-≤ {zero} {zero}      z≤ =       ≤-refl
  Ψ-monoˡ-≤ {zero} {suc β} {γ} z≤ =       begin
    Ψ F zero γ                            ≤⟨ Ψ-monoˡ-≤ z≤ ⟩
    Ψ F β γ                               ≤⟨ ′-incrʰ-≤ (Ψ-normal β) γ ⟩
    Ψ F (suc β) γ                         ∎
```

以下两种情况递归调用衍生命题得证.

```agda
  Ψ-monoˡ-≤ {zero} {lim f} z≤ = Ψ-monoˡ-≤l {n = 0} z≤
  Ψ-monoˡ-≤ {suc α} {lim f} (s≤ {d = n , d} α<fn) = Ψ-monoˡ-≤l {suc α} (<⇒s≤ (d , α<fn))
```

`α` 和 `β` 都为后继时使用 `_′` 的高阶单调性得证.

```agda
  Ψ-monoˡ-≤ {suc α} {suc β} {γ} (s≤ α<s) = begin
    Ψ F (suc α) γ                         ≤⟨ ′-monoʰ-≤ (Ψ-monoʳ-≤ α) IH ⟩
    Ψ F (suc β) γ                         ∎ where
      IH : ∀ {γ} → Ψ F α γ ≤ Ψ F β γ
      IH = Ψ-monoˡ-≤ (<s⇒≤ (_ , α<s))
```

后继小于等于零的情况不存在, 且对良构序数来说极限小于等于零的情况也不存在.

```agda
  Ψ-monoˡ-≤ {lim α} {zero} (l≤ αn≤β) with ≤z⇒≡z (l≤ αn≤β)
  ... | ()
```

`α` 为极限 `β` 为后继的情况与 `α` 为零 `β` 为后继的情况类似. 递归调用自身, 并使用 `_′` 的高阶增长性得证. 注意这里使用了良构序数特有的性质 `l≤s⇒l≤`.

```agda
  Ψ-monoˡ-≤ {lim α} {suc β} {γ} (l≤ αn≤β) = begin
    Ψ F (lim α) γ                         ≤⟨ Ψ-monoˡ-≤ (l≤s⇒l≤ (l≤ αn≤β)) ⟩
    Ψ F β γ                               ≤⟨ ′-incrʰ-≤ (Ψ-normal β) γ ⟩
    Ψ F (suc β) γ                         ∎
```

`α` 和 `β` 都为极限时使用 `_⁺` 的高阶单调性得证. 注意这里使用了良构序数特有的性质 `∃[m]fn<gm`. ∎

```agda
  Ψ-monoˡ-≤ {lim α} {lim β} (l≤ αn≤β) = ⁺-monoʰ-≤ mono (l≤ ≤) where
    mono : ≤-monotonic (F ∘ₗ α)
    mono ≤ = l≤l λ _ → Ψ-monoʳ-≤ (α _) ≤
    ≤ : ∀ {ξ} n → Ψ F (α n) ξ ≤ (F ∘ₗ β) ξ
    ≤ {ξ} n with ∃[m]fn<gm (l≤ αn≤β) n
    ... | (m , <) =                       begin
      Ψ F (α n) ξ                         ≤⟨ Ψ-monoˡ-≤ (<⇒≤ <) ⟩
      Ψ F (β m) ξ                         ≤⟨ f≤l ⟩
      (F ∘ₗ β) ξ                          ∎
```

**推论** `Ψ F` 对第一个参数满足合同性.

```agda
  module _ {α β γ} ⦃ wfα : wellFormed α ⦄ ⦃ wfβ : wellFormed β ⦄ where
    Ψ-cong¹ : α ≈ β → Ψ F α γ ≈ Ψ F β γ
    Ψ-cong¹ (≤ , ≥) = (Ψ-monoˡ-≤ ≤) , (Ψ-monoˡ-≤ ≥)
```

### 不动点性

**引理** 对任意良构 `α ≤ β`, 每个 `Ψ F (suc β) γ` 也是 `Ψ F α` 的不动点.

```agda
    Ψ-fp-suc-≤ : α ≤ β → (Ψ F (suc β) γ) isFixpointOf (Ψ F α)
    Ψ-fp-suc-≤ ≤ = helper , Ψ-incrʳ-≤ α _ where
      helper =                            begin
        Ψ F α ((Ψ F β ′) γ)               ≤⟨ Ψ-monoˡ-≤ ≤ ⟩
        Ψ F β ((Ψ F β ′) γ)               ≈⟨ Ψ-fp-suc β γ ⟩
        (Ψ F β ′) γ                       ∎
```

**定理** 对任意良构 `α < β`, 每个 `Ψ F β γ` 也是 `Ψ F α` 的不动点.

```agda
  Ψ-fp : ∀ {α β γ} → ⦃ wellFormed α ⦄ → ⦃ wellFormed β ⦄
    → α < β → (Ψ F β γ) isFixpointOf (Ψ F α)

  module _ f n ⦃ (_ , wrap mono) : wellFormed (lim f) ⦄ where
    Ψ-fp-lim : ∀ γ → (Ψ F (lim f) γ) isFixpointOf (Ψ F (f n))
    Ψ-fp-fn : ∀ γ → lim (λ n → Ψ F (f n) γ) isFixpointOf (Ψ F (f n))

    Ψ-fp-fn γ =                                       begin-equality
      Ψ F (f n) (lim (λ m → Ψ F (f m) γ))             ≈⟨ Ψ-cong² (f n) (l≈l∘ ≤-mono-seq m<smn) ⟩
      Ψ F (f n) (lim (λ m → Ψ F (f (suc m ℕ.+ n)) γ)) ≈⟨ Ψ-lim-ct (f n) _ ⟩
      lim (λ m → Ψ F (f n) (Ψ F (f (suc m ℕ.+ n)) γ)) ≈⟨ l≈l (Ψ-fp fn<fsmn) ⟩
      lim (λ m → Ψ F (f (suc m ℕ.+ n)) γ)             ≈˘⟨ l≈l∘ ≤-mono-seq m<smn ⟩
      lim (λ m → Ψ F (f m) γ)                         ∎ where
        ≤-mono-seq : ≤-mono-sequence (λ m → Ψ F (f m) γ)
        ≤-mono-seq ≤ = Ψ-monoˡ-≤ (<⇒≤-mono ≤)
        m<smn : ∀ m → m ℕ.< suc m ℕ.+ n
        m<smn m = ℕ.s≤s (m≤m+n m n)
        fn<fsmn : ∀ {m} → f n < f (suc m ℕ.+ n)
        fn<fsmn = mono (m<n+m n ℕ.z<s)

    Ψ-fp-lim zero = Ψ-fp-fn zero
    Ψ-fp-lim (suc γ) = Ψ-fp-fn (suc (Ψ F (lim f) γ))
    Ψ-fp-lim (lim γ) =                          begin-equality
      Ψ F (f n) (lim (λ m → Ψ F (lim f) (γ m))) ≈⟨ Ψ-lim-ct (f n) _ ⟩
      lim (λ m → Ψ F (f n) (Ψ F (lim f) (γ m))) ≈⟨ l≈l (Ψ-fp-lim (γ _)) ⟩
      lim (λ m → Ψ F (lim f) (γ m))             ∎

  Ψ-fp {α} {suc β}     (inj₁ _ , ≤) = Ψ-fp-suc-≤ ≤
  Ψ-fp {α} {suc β} {γ} (inj₂ d , ≤) = begin-equality
    Ψ F α (Ψ F (suc β) γ)             ≈˘⟨ Ψ-cong² α (Ψ-fp-suc β γ) ⟩
    Ψ F α (Ψ F β (Ψ F (suc β) γ))     ≈⟨ Ψ-fp (d , ≤) ⟩
    Ψ F β (Ψ F (suc β) γ)             ≈⟨ Ψ-fp-suc β γ ⟩
    Ψ F (suc β) γ                     ∎
  Ψ-fp {α} {lim f} {γ} α<l with ∃[n]<fn α<l
  ... | (n , α<fn) = begin-equality
    Ψ F α (Ψ F (lim f) γ)             ≈˘⟨ Ψ-cong² α (Ψ-fp-lim f n γ) ⟩
    Ψ F α (Ψ F (f n) (Ψ F (lim f) γ)) ≈⟨ Ψ-fp α<fn ⟩
    Ψ F (f n) (Ψ F (lim f) γ)         ≈⟨ Ψ-fp-lim f n γ ⟩
    Ψ F (lim f) γ                     ∎
```

## 特化

以 `ω ^_` 实例化 Properties 模块即可特到 `φ` 的性质.

```agda
open Properties (ω ^_) ω^-normal
```

我们只列出主要结论.

**事实** 每个 `φ α` 都是序数嵌入.

```agda
φ-normal : ∀ α → normal (φ α)
φ-normal = Ψ-normal
```

**事实** `φ` 对第一个参数满足单调性与合同性.

```agda
module _ {α β γ} ⦃ wfα : wellFormed α ⦄ ⦃ wfβ : wellFormed β ⦄ where

  φ-monoˡ-≤ : α ≤ β → φ α γ ≤ φ β γ
  φ-monoˡ-≤ = Ψ-monoˡ-≤

  φ-cong¹-≤ : α ≈ β → φ α γ ≈ φ β γ
  φ-cong¹-≤ = Ψ-cong¹
```

**事实** 高阶不动点同时也是低阶不动点.

```agda
  φ-fp : α < β → (φ β γ) isFixpointOf (φ α)
  φ-fp = Ψ-fp
```
