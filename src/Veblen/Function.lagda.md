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
open import Ordinal.WellFormed using (wellFormed; ω; ⌜_⌝; ≤z⇒≡z; l≤s⇒l≤; ∃[m]fn<gm)
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

$$φ_{\lim f}(0) = \sup\{φ_{f(0)}(0), φ_{f(1)}(0), φ_{f(2)}(0), ...\}$$

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

**引理** 对 `veblen` 来说, 如果初始函数 `F` 是序数嵌入, 那么每个迭代 `veblen F α` 都是序数嵌入.

```agda
  veblen-normal : ∀ α → normal (veblen F α)
  veblen-normal zero    = nml
  veblen-normal (suc α) = ′-normal (veblen-normal α)
  veblen-normal (lim f) = ⁺-normal (F ∘ₗ f) mono incr where
    mono : ≤-monotonic (F ∘ₗ f)
    mono {α} {β} ≤ = l≤l λ n → begin
      veblen F (f n) (α)        ≤⟨ proj₁ (veblen-normal (f n)) ≤ ⟩
      veblen F (f n) (β)        ∎
    incr : ≤-increasing (F ∘ₗ f)
    incr α =                    begin
      α                         ≤⟨ normal⇒≤-incr (veblen-normal (f 0)) α ⟩
      veblen F (f 0) α          ≤⟨ f≤l ⟩
      (F ∘ₗ f) α                ∎
```

**引理** 每个 `veblen F (suc α) γ` 也是 `veblen F α` 的不动点.

```agda
  veblen-fp-suc : ∀ α γ → (veblen F (suc α) γ) isFixpointOf (veblen F α)
  veblen-fp-suc α γ = ′-fp (veblen-normal α) γ
```

我们想把上述事实推广到任意满足 `α < β` 的两个序数. 这需要一系列引理. 其中最基本的是 `veblen F` 对第一个参数的合同性, 而这又直接依赖于单调性.

**引理** `veblen F` 对第一个参数满足单调性.

该命题较为繁琐. 首先在表述上, 参数要求是良构序数. 证明上, 要同时讨论 `_≤_` 的两边, 这就分出了九种情况, 然后还衍生出一个互递归命题又分出五种情况.

```agda
  veblen-monoˡ-≤ : ∀ {α β γ} → ⦃ wellFormed α ⦄ → ⦃ wellFormed β ⦄ →
    α ≤ β → veblen F α γ ≤ veblen F β γ
  veblen-monoˡ-≤l : ∀ {α f n γ} → ⦃ wellFormed α ⦄ → ⦃ ∀ {n} → wellFormed (f n) ⦄ →
    α ≤ f n → veblen F α γ ≤ veblen F (lim f) γ
```

**证明** 我们先证衍生出的命题. `γ` 为零或后继时都要递归调用主命题, 后继的情况还用到了第二个参数的序数嵌入条件.

```agda
  veblen-monoˡ-≤l {α} {f} {n} {zero} α≤fn =   begin
    veblen F α zero                           ≤⟨ veblen-monoˡ-≤ α≤fn ⟩
    veblen F (f n) zero                       ≤⟨ f≤l ⟩
    (F ∘ₗ f) zero                             ∎

  veblen-monoˡ-≤l {α} {f} {n} {suc γ} α≤fn =  begin
    veblen F α (suc γ)                        ≤⟨ veblen-monoˡ-≤ α≤fn ⟩
    veblen F (f n) (suc γ)                    ≤⟨ proj₁ (veblen-normal (f n)) (s≤s ≤) ⟩
    veblen F (f n) (suc (veblen F (lim f) γ)) ≤⟨ f≤l ⟩
    (F ∘ₗ f) (suc (veblen F (lim f) γ))       ∎ where
      ≤ : γ ≤ veblen F (lim f) γ
      ≤ = normal⇒≤-incr (veblen-normal (lim f)) γ
```

`γ` 为极限时要看 `α`. `α` 为零或后继时都要递归调用衍生命题, 为后继时还要递归调用主命题. `α` 为极限的情况使用 `_⁺` 的高阶单调性得证.

```agda
  veblen-monoˡ-≤l {zero} {f} {n} {lim γ} z≤fn = begin
    F (lim γ)                                 ≈⟨ lim-ct γ ⟩
    lim (λ n → F (γ n))                       ≤⟨ l≤l (λ n → veblen-monoˡ-≤l {n = n} z≤) ⟩
    lim (λ n → veblen F (lim f) (γ n))        ∎
  veblen-monoˡ-≤l {suc α} {f} {n} {lim γ} sα≤fn = l≤l λ m → begin
    veblen F (suc α) (γ m)                    ≤⟨ veblen-monoˡ-≤ sα≤fn ⟩
    veblen F (f n) (γ m)                      ≤⟨ veblen-monoˡ-≤l ≤-refl ⟩
    veblen F (lim f) (γ m)                    ∎
  veblen-monoˡ-≤l {lim α} {β} {n} ⦃ wfα ⦄ (l≤ α≤βn) = ⁺-monoʰ-≤ mono (l≤ ≤) where
    mono : ≤-monotonic (F ∘ₗ α)
    mono ≤ = l≤l λ _ → proj₁ (veblen-normal (α _)) ≤
    ≤ : ∀ {ξ} m → veblen F (α m) ξ ≤ (F ∘ₗ β) ξ
    ≤ {ξ} m =                                 begin
      veblen F (α m) ξ                        ≤⟨ veblen-monoˡ-≤ ⦃ proj₁ wfα ⦄ (α≤βn m) ⟩
      veblen F (β n) ξ                        ≤⟨ f≤l ⟩
      (F ∘ₗ β) ξ                              ∎
```

接着证明主命题. `α` 和 `β` 都为零时显然成立. `α` 为零 `β` 为后继时递归调用自身, 并使用 `_′` 的高阶增长性得证.

```agda
  veblen-monoˡ-≤ {zero} {zero}      z≤ =      ≤-refl
  veblen-monoˡ-≤ {zero} {suc β} {γ} z≤ =      begin
    veblen F zero γ                           ≤⟨ veblen-monoˡ-≤ z≤ ⟩
    veblen F β γ                              ≤⟨ ′-incrʰ-≤ (veblen-normal β) γ ⟩
    veblen F (suc β) γ                        ∎
```

以下两种情况递归调用衍生命题得证.

```agda
  veblen-monoˡ-≤ {zero} {lim f} ⦃ _ ⦄ ⦃ wfβ ⦄ z≤
    = veblen-monoˡ-≤l {n = 0} ⦃ _ ⦄ ⦃ proj₁ wfβ ⦄ z≤
  veblen-monoˡ-≤ {suc α} {lim f} ⦃ wfα ⦄ ⦃ wfβ ⦄ (s≤ {d = n , d} α<fn)
    = veblen-monoˡ-≤l {suc α} ⦃ wfα ⦄ ⦃ proj₁ wfβ ⦄ (<⇒s≤ (d , α<fn))
```

`α` 和 `β` 都为后继时使用 `_′` 的高阶单调性得证.

```agda
  veblen-monoˡ-≤ {suc α} {suc β} {γ} (s≤ α<s) = begin
    veblen F (suc α) γ                        ≤⟨ ′-monoʰ-≤ (proj₁ (veblen-normal α)) IH ⟩
    veblen F (suc β) γ                        ∎ where
      IH : ∀ {γ} → veblen F α γ ≤ veblen F β γ
      IH = veblen-monoˡ-≤ (<s⇒≤ (_ , α<s))
```

后继小于等于零的情况不存在, 且对良构序数来说极限小于等于零的情况也不存在.

```agda
  veblen-monoˡ-≤ {lim α} {zero}      ⦃ wfα ⦄ (l≤ αn≤β) with ≤z⇒≡z wfα (l≤ αn≤β)
  ... | ()
```

`α` 为极限 `β` 为后继的情况与 `α` 为零 `β` 为后继的情况类似. 递归调用自身, 并使用 `_′` 的高阶增长性得证. 注意这里使用了良构序数特有的性质 `l≤s⇒l≤`.

```agda
  veblen-monoˡ-≤ {lim α} {suc β} {γ} ⦃ wfα ⦄ (l≤ αn≤β) = begin
    veblen F (lim α) γ                        ≤⟨ veblen-monoˡ-≤ (l≤s⇒l≤ (proj₂ wfα) (l≤ αn≤β)) ⟩
    veblen F β γ                              ≤⟨ ′-incrʰ-≤ (veblen-normal β) γ ⟩
    veblen F (suc β) γ                        ∎
```

`α` 和 `β` 都为极限时使用 `_⁺` 的高阶单调性得证. 注意这里使用了良构序数特有的性质 `∃[m]fn<gm`. ∎

```agda
  veblen-monoˡ-≤ {lim α} {lim β} ⦃ wfα , mα ⦄ ⦃ wfβ , mβ ⦄ (l≤ αn≤β) = ⁺-monoʰ-≤ mono (l≤ ≤) where
    mono : ≤-monotonic (F ∘ₗ α)
    mono ≤ = l≤l λ _ → proj₁ (veblen-normal (α _)) ≤
    ≤ : ∀ {ξ} n → veblen F (α n) ξ ≤ (F ∘ₗ β) ξ
    ≤ {ξ} n with ∃[m]fn<gm mα mβ (l≤ αn≤β) n
    ... | (m , <) =                           begin
      veblen F (α n) ξ                        ≤⟨ veblen-monoˡ-≤ ⦃ wfα ⦄ ⦃ wfβ ⦄ (<⇒≤ <) ⟩
      veblen F (β m) ξ                        ≤⟨ f≤l ⟩
      (F ∘ₗ β) ξ                              ∎
```

**推论** `veblen F` 对第一个参数满足合同性.

```agda
  module _ {α β γ} ⦃ wfα : wellFormed α ⦄ ⦃ wfβ : wellFormed β ⦄ where
    veblen-congˡ-≤ : α ≈ β → veblen F α γ ≈ veblen F β γ
    veblen-congˡ-≤ (≤ , ≥) = (veblen-monoˡ-≤ ≤) , (veblen-monoˡ-≤ ≥)
```

最后, 我们将 `veblen` 的性质实例化到 `φ`.

```agda
open Properties (ω ^_) ω^-normal
```

**事实** 每个 `φ α` 都是序数嵌入.

```agda
φ-normal : ∀ α → normal (φ α)
φ-normal = veblen-normal
```

**事实** $φ_α(φ_{α+1}(β))=φ_{α+1}(β)$.

```agda
φ-fp-suc : ∀ α β → (φ (suc α) β) isFixpointOf (φ α)
φ-fp-suc = veblen-fp-suc
```

**事实** `φ` 对第一个参数满足单调性与合同性.

```agda
module _ {α β γ} ⦃ wfα : wellFormed α ⦄ ⦃ wfβ : wellFormed β ⦄ where

  φ-monoˡ-≤ : α ≤ β → φ α γ ≤ φ β γ
  φ-monoˡ-≤ = veblen-monoˡ-≤

  φ-congˡ-≤ : α ≈ β → φ α γ ≈ φ β γ
  φ-congˡ-≤ = veblen-congˡ-≤
```
