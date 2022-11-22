---
title: Agda大序数(1-9) 二元Veblen函数
zhihu-tags: Agda, 序数, 大数数学
zhihu-url: https://zhuanlan.zhihu.com/p/585851679
---

# Agda大序数(1-9) 二元Veblen函数

> 交流Q群: 893531731  
> 目录: [NonWellFormed.html](https://choukh.github.io/agda-lvo/NonWellFormed.html)  
> 本文源码: [VeblenFunction.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/NonWellFormed/VeblenFunction.lagda.md)  
> 高亮渲染: [VeblenFunction.html](https://choukh.github.io/agda-lvo/NonWellFormed.VeblenFunction.html)  
> 如果你在知乎看到本文: 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

```agda
{-# OPTIONS --without-K --safe --experimental-lossy-unification #-}
{-# OPTIONS --overlapping-instances #-}

module NonWellFormed.VeblenFunction where
```

## 前置

```agda
open import NonWellFormed.Ordinal
open NonWellFormed.Ordinal.≤-Reasoning
open import NonWellFormed.WellFormed
open import NonWellFormed.Function
open import NonWellFormed.Recursion
open import NonWellFormed.Arithmetic using (_^_)
open import NonWellFormed.Fixpoint
open import NonWellFormed.Epsilon

open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Nat.Properties as ℕ using (m≤m+n; m<n+m)
open import Function using (_∘_; λ-; it)
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function.Definitions (_≈_) (_≈_) using (Congruent)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
```

## 定义

上一章讲到, 将 `ω ^_`, `ε`, `ζ`, `η` 分别看作第0, 1, 2, 3层级, 可以推广到任意序数层级, 从而得到二元 Ψ 函数.

形式上, 我们需要辅助函数 `Ψ`, 它是一个高阶函数, 接受一个序数函数 `F` 作为初始值, 并接受一个序数 `α` 作为 `_′` 的迭代次数, 返回迭代后的序数函数. 于是二元Veblen函数 `φ` 就定义为以 `ω ^_` 为初始值的 `_′` 迭代. 注意极限情况下的形式比较复杂. naive地看似乎 `λ α → lim (λ n → Ψ F (f n) α)` 就够了, 但为了更好的性质要再套一层 `_⁺`.

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
_ = λ- refl
```

第一个参数是极限时又按第二个参数分三种情况:

$$φ_{γ}(0) = \sup\{φ_{γ[0]}(0), φ_{γ[1]}(0), φ_{γ[2]}(0), ...\}$$

或者按基本序列记作

$$φ_{γ}(0)[n] = φ_{γ[n]}(0)$$

我们今后都采用这种非形式记法.

```agda
_ : ∀ f → φ (lim f) zero ≡ lim (λ n → φ (f n) zero)
_ = λ- refl
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

### 嵌入性

**定理** 对 `Ψ` 来说, 如果初始函数 `F` 是序数嵌入, 那么每个迭代 `Ψ F α` 都是序数嵌入.

```agda
  Ψ-normal² : ∀ α → normal (Ψ F α)

  Ψ-mono²-≤ : ∀ α → ≤-monotonic (Ψ F α)
  Ψ-mono²-≤ α = proj₁ (Ψ-normal² α)

  Ψ-incr²-≤ : ∀ α → ≤-increasing (Ψ F α)
  Ψ-incr²-≤ α = normal⇒≤-incr (Ψ-normal² α)

  Ψ-normal² zero    = nml
  Ψ-normal² (suc α) = ′-normal (Ψ-normal² α)
  Ψ-normal² (lim f) = ⁺-normal (F ∘ₗ f) mono incr where
    mono : ≤-monotonic (F ∘ₗ f)
    mono {α} {β} ≤ = l≤l λ n →  begin
      Ψ F (f n) (α)             ≤⟨ Ψ-mono²-≤ (f n) ≤ ⟩
      Ψ F (f n) (β)             ∎
    incr : ≤-increasing (F ∘ₗ f)
    incr α =                    begin
      α                         ≤⟨ Ψ-incr²-≤ (f 0) α ⟩
      Ψ F (f 0) α               ≤⟨ f≤l ⟩
      (F ∘ₗ f) α                ∎
```

**推论** `Ψ F` 对第二个参数满足合同性.

```agda
  Ψ-cong² : ∀ α → Congruent (Ψ F α)
  Ψ-cong² α = ≤-mono⇒cong (Ψ-mono²-≤ α)
```

**推论** `Ψ F` 对第二个参数满足 <-单调.

```agda
  Ψ-mono²-< : ∀ α → <-monotonic (Ψ F α)
  Ψ-mono²-< α = proj₁ (proj₂ (Ψ-normal² α))
```

**推论** `Ψ F` 对第二个参数满足极限连续.

```agda
  Ψ-lim-ct : ∀ α → lim-continuous (Ψ F α)
  Ψ-lim-ct α = proj₂ (proj₂ (Ψ-normal² α))
```

**引理** 每个 `Ψ F (suc α) γ` 也是 `Ψ F α` 的不动点.

```agda
  Ψ-fp-suc : ∀ α γ → (Ψ F (suc α) γ) isFixpointOf (Ψ F α)
  Ψ-fp-suc α γ = ′-fp (Ψ-normal² α) γ
```

我们想把上述事实推广到任意满足 `α < β` 的两个序数, 这需要先证明 `Ψ F` 对第一个参数的单调性.

### 单调性

**引理** `Ψ F` 对第一个参数满足单调性.

该命题较为繁琐. 首先在表述上, 参数要求是良构序数. 证明上, 要同时讨论 `_≤_` 的两边, 这就分出了九种情况, 然后还衍生出一个互递归命题又分出五种情况.

```agda
  Ψ-mono¹-≤ : ∀ {α β γ} → ⦃ WellFormed α ⦄ → ⦃ WellFormed β ⦄ →
    α ≤ β → Ψ F α γ ≤ Ψ F β γ
  Ψ-mono¹-≤l : ∀ {α f n γ} → ⦃ WellFormed α ⦄ → ⦃ ∀ {n} → WellFormed (f n) ⦄ →
    α ≤ f n → Ψ F α γ ≤ Ψ F (lim f) γ
```

**证明** 我们先证衍生命题. `γ` 为零或后继时都要递归调用主命题, 后继的情况还用到了第二个参数的序数嵌入条件.

```agda
  Ψ-mono¹-≤l {α} {f} {n} {zero} α≤fn =    begin
    Ψ F α zero                            ≤⟨ Ψ-mono¹-≤ α≤fn ⟩
    Ψ F (f n) zero                        ≤⟨ f≤l ⟩
    (F ∘ₗ f) zero                         ∎

  Ψ-mono¹-≤l {α} {f} {n} {suc γ} α≤fn =   begin
    Ψ F α (suc γ)                         ≤⟨ Ψ-mono¹-≤ α≤fn ⟩
    Ψ F (f n) (suc γ)                     ≤⟨ Ψ-mono²-≤ (f n) (s≤s (Ψ-incr²-≤ (lim f) γ)) ⟩
    Ψ F (f n) (suc (Ψ F (lim f) γ))       ≤⟨ f≤l ⟩
    (F ∘ₗ f) (suc (Ψ F (lim f) γ))        ∎
```

`γ` 为极限时要看 `α`. `α` 为零或后继时都要递归调用衍生命题, 为后继时还要递归调用主命题. `α` 为极限的情况使用 `_⁺` 的高阶单调性得证.

```agda
  Ψ-mono¹-≤l {zero} {f} {n} {lim γ} z≤fn = begin
    F (lim γ)                             ≈⟨ lim-ct γ ⟩
    lim (λ n → F (γ n))                   ≤⟨ l≤l (λ n → Ψ-mono¹-≤l {n = n} z≤) ⟩
    lim (λ n → Ψ F (lim f) (γ n))         ∎
  Ψ-mono¹-≤l {suc α} {f} {n} {lim γ} sα≤fn = l≤l λ m → begin
    Ψ F (suc α) (γ m)                     ≤⟨ Ψ-mono¹-≤ sα≤fn ⟩
    Ψ F (f n) (γ m)                       ≤⟨ Ψ-mono¹-≤l ≤-refl ⟩
    Ψ F (lim f) (γ m)                     ∎
  Ψ-mono¹-≤l {lim α} {β} {n} (l≤ α≤βn) = ⁺-monoʰ-≤ mono (l≤ ≤) where
    mono : ≤-monotonic (F ∘ₗ α)
    mono ≤ = l≤l λ _ → Ψ-mono²-≤ (α _) ≤
    ≤ : ∀ {ξ} m → Ψ F (α m) ξ ≤ (F ∘ₗ β) ξ
    ≤ {ξ} m =                             begin
      Ψ F (α m) ξ                         ≤⟨ Ψ-mono¹-≤ (α≤βn m) ⟩
      Ψ F (β n) ξ                         ≤⟨ f≤l ⟩
      (F ∘ₗ β) ξ                          ∎
```

接着证明主命题. `α` 和 `β` 都为零时显然成立. `α` 为零 `β` 为后继时递归调用自身, 并使用 `_′` 的高阶增长性得证.

```agda
  Ψ-mono¹-≤ {zero} {zero}      z≤ =       ≤-refl
  Ψ-mono¹-≤ {zero} {suc β} {γ} z≤ =       begin
    Ψ F zero γ                            ≤⟨ Ψ-mono¹-≤ z≤ ⟩
    Ψ F β γ                               ≤⟨ ′-incrʰ-≤ (Ψ-normal² β) γ ⟩
    Ψ F (suc β) γ                         ∎
```

以下两种情况递归调用衍生命题得证.

```agda
  Ψ-mono¹-≤ {zero} {lim f} z≤ = Ψ-mono¹-≤l {n = 0} z≤
  Ψ-mono¹-≤ {suc α} {lim f} (s≤ {d = n , d} α<fn) = Ψ-mono¹-≤l {suc α} (<⇒s≤ (d , α<fn))
```

`α` 和 `β` 都为后继时使用 `_′` 的高阶单调性得证.

```agda
  Ψ-mono¹-≤ {suc α} {suc β} {γ} (s≤ α<s) = begin
    Ψ F (suc α) γ                         ≤⟨ ′-monoʰ-≤ (Ψ-mono²-≤ α) IH ⟩
    Ψ F (suc β) γ                         ∎ where
      IH : ∀ {γ} → Ψ F α γ ≤ Ψ F β γ
      IH = Ψ-mono¹-≤ (<s⇒≤ (_ , α<s))
```

后继小于等于零的情况不存在, 且对良构序数来说极限小于等于零的情况也不存在.

```agda
  Ψ-mono¹-≤ {lim α} {zero} (l≤ αn≤β) with ≤z⇒≡z (l≤ αn≤β)
  ... | ()
```

`α` 为极限 `β` 为后继的情况与 `α` 为零 `β` 为后继的情况类似. 递归调用自身, 并使用 `_′` 的高阶增长性得证. 注意这里使用了良构序数特有的性质 `l≤s⇒l≤`.

```agda
  Ψ-mono¹-≤ {lim α} {suc β} {γ} (l≤ αn≤β) = begin
    Ψ F (lim α) γ                         ≤⟨ Ψ-mono¹-≤ (l≤s⇒l≤ (l≤ αn≤β)) ⟩
    Ψ F β γ                               ≤⟨ ′-incrʰ-≤ (Ψ-normal² β) γ ⟩
    Ψ F (suc β) γ                         ∎
```

`α` 和 `β` 都为极限时使用 `_⁺` 的高阶单调性得证. 注意这里使用了良构序数特有的性质 `∃[m]fn<gm`. ∎

```agda
  Ψ-mono¹-≤ {lim α} {lim β} (l≤ αn≤β) = ⁺-monoʰ-≤ mono (l≤ ≤) where
    mono : ≤-monotonic (F ∘ₗ α)
    mono ≤ = l≤l λ _ → Ψ-mono²-≤ (α _) ≤
    ≤ : ∀ {ξ} n → Ψ F (α n) ξ ≤ (F ∘ₗ β) ξ
    ≤ {ξ} n with ∃[m]fn<gm (l≤ αn≤β) n
    ... | (m , <) =                       begin
      Ψ F (α n) ξ                         ≤⟨ Ψ-mono¹-≤ (<⇒≤ <) ⟩
      Ψ F (β m) ξ                         ≤⟨ f≤l ⟩
      (F ∘ₗ β) ξ                          ∎
```

**推论** `Ψ F` 对第一个参数满足合同性.

```agda
  module _ {α β γ} ⦃ wfα : WellFormed α ⦄ ⦃ wfβ : WellFormed β ⦄ where
    Ψ-cong¹ : α ≈ β → Ψ F α γ ≈ Ψ F β γ
    Ψ-cong¹ (≤ , ≥) = (Ψ-mono¹-≤ ≤) , (Ψ-mono¹-≤ ≥)
```

### 不动点性

**引理** 对任意良构 `α ≤ β`, 每个 `Ψ F (suc β) γ` 也是 `Ψ F α` 的不动点.

```agda
    Ψ-fp-suc-≤ : α ≤ β → (Ψ F (suc β) γ) isFixpointOf (Ψ F α)
    Ψ-fp-suc-≤ ≤ = helper , Ψ-incr²-≤ α _ where
      helper =                            begin
        Ψ F α ((Ψ F β ′) γ)               ≤⟨ Ψ-mono¹-≤ ≤ ⟩
        Ψ F β ((Ψ F β ′) γ)               ≈⟨ Ψ-fp-suc β γ ⟩
        (Ψ F β ′) γ                       ∎
```

**定理** 对任意良构 `α < β`, 每个 `Ψ F β γ` 也是 `Ψ F α` 的不动点.

```agda
  Ψ-fp : ∀ {α β γ} → ⦃ WellFormed α ⦄ → ⦃ WellFormed β ⦄
    → α < β → (Ψ F β γ) isFixpointOf (Ψ F α)
```

**证明** 这是一个三重互递归证明. 我们需要以下两个衍生命题.

```agda
  module _ f n ⦃ (_ , wrap mono) : WellFormed (lim f) ⦄ where
    Ψ-fp-lim : ∀ γ → (Ψ F (lim f) γ) isFixpointOf (Ψ F (f n))
    Ψ-fp-fn : ∀ γ → lim (λ n → Ψ F (f n) γ) isFixpointOf (Ψ F (f n))
```

先证 `Ψ-fp-fn`. 核心步骤是用 `l≈l∘` 将序列的起始项后移, 从而为递归调用主命题 `Ψ-fp` 创造条件. 这要求 `λ m → Ψ F (f m) γ` 为非严格单调序列, 由引理 `Ψ-mono¹-≤` 保证.

```agda
    Ψ-fp-fn γ =                                       begin-equality
      Ψ F (f n) (lim (λ m → Ψ F (f m) γ))             ≈⟨ Ψ-cong² (f n) (l≈l∘ ≤-seq m<smn) ⟩
      Ψ F (f n) (lim (λ m → Ψ F (f (suc m ℕ.+ n)) γ)) ≈⟨ Ψ-lim-ct (f n) _ ⟩
      lim (λ m → Ψ F (f n) (Ψ F (f (suc m ℕ.+ n)) γ)) ≈⟨ l≈l (Ψ-fp fn<fsmn) ⟩
      lim (λ m → Ψ F (f (suc m ℕ.+ n)) γ)             ≈˘⟨ l≈l∘ ≤-seq m<smn ⟩
      lim (λ m → Ψ F (f m) γ)                         ∎ where
        ≤-seq : ≤-monoSequence (λ m → Ψ F (f m) γ)
        ≤-seq ≤ = Ψ-mono¹-≤ (<⇒≤-mono ≤)
        m<smn : ∀ m → m ℕ.< suc m ℕ.+ n
        m<smn m = ℕ.s≤s (m≤m+n m n)
        fn<fsmn : ∀ {m} → f n < f (suc m ℕ.+ n)
        fn<fsmn = mono (m<n+m n ℕ.z<s)
```

接着证 `Ψ-fp-lim`. `γ` 为零或后继的时候递归调用 `Ψ-fp-fn` 即证. `γ` 为极限时递归调用自身得证.

```agda
    Ψ-fp-lim zero = Ψ-fp-fn zero
    Ψ-fp-lim (suc γ) = Ψ-fp-fn (suc (Ψ F (lim f) γ))
    Ψ-fp-lim (lim γ) =                          begin-equality
      Ψ F (f n) (lim (λ m → Ψ F (lim f) (γ m))) ≈⟨ Ψ-lim-ct (f n) _ ⟩
      lim (λ m → Ψ F (f n) (Ψ F (lim f) (γ m))) ≈⟨ l≈l (Ψ-fp-lim (γ _)) ⟩
      lim (λ m → Ψ F (lim f) (γ m))             ∎
```

最后是主命题的证明. `β` 不可能为零. `β` 为后继时使用引理 `Ψ-fp-suc` 并递归调用主命题得证. `β` 为极限时递归调用衍生命题 `Ψ-fp-lim` 和主命题得证. ∎

```agda
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

### 序关系

**推论** 对任意 `α` `β` `γ` `δ`, 有三种情况可以建立 `Ψ F α β < Ψ F γ δ` 关系. 一种是 `α ≈ γ` 且 `β < δ`, 这由 `Ψ-cong¹` 和 `Ψ-mono²-<` 可以立即得到.

```agda
  module _ {α β γ δ} ⦃ wfα : WellFormed α ⦄ ⦃ wfγ : WellFormed γ ⦄ where
    Ψ-≈⇒< : α ≈ γ → β < δ → Ψ F α β < Ψ F γ δ
    Ψ-≈⇒< α≈γ β<δ =     begin-strict
      Ψ F α β           ≈⟨ Ψ-cong¹ α≈γ ⟩
      Ψ F γ β           <⟨ Ψ-mono²-< γ β<δ ⟩
      Ψ F γ δ           ∎
```

第二种是 `α < γ` 且 `β < Ψ F γ δ`.

```agda
    Ψ-<⇒< : α < γ → β < Ψ F γ δ → Ψ F α β < Ψ F γ δ
    Ψ-<⇒< α<γ β<ΨFγδ =  begin-strict
      Ψ F α β           <⟨ Ψ-mono²-< α β<ΨFγδ ⟩
      Ψ F α (Ψ F γ δ)   ≈⟨ Ψ-fp α<γ ⟩
      Ψ F γ δ           ∎
```

第三种是 `Ψ F α β < δ`.

```agda
    Ψ->⇒< : Ψ F α β < δ → Ψ F α β < Ψ F γ δ
    Ψ->⇒< ΨFαβ<δ =      begin-strict
      Ψ F α β           <⟨ ΨFαβ<δ ⟩
      δ                 ≤⟨ Ψ-incr²-≤ γ δ ⟩
      Ψ F γ δ           ∎
```

在经典逻辑中可以强化到有且**仅**有以上三种情况可以推出 `Ψ F α β < Ψ F γ δ`, 只是第三种情况要增加 `α > γ` 条件, 以利用 `<` 的三歧性.

### 保良构

**引理** 如果 `F` 在零处增长, 那么任意 `Ψ F α` 也在零处增长.

```agda
  module _ (z-incr : zero-increasing F) where
    Ψ-zero-incr : ∀ α → zero-increasing (Ψ F α)
    Ψ-zero-incr zero    = z-incr
    Ψ-zero-incr (suc α) = ′-zero-incr (Ψ-zero-incr α)
    Ψ-zero-incr (lim f) = <f⇒<l {n = 0} (Ψ-zero-incr (f 0))
```

**引理** 如果 `F` 在良构后继处增长, 那么任意良构 `Ψ F α` 也在良构后继处增长.

```agda
  module _ (s-incr : suc-increasing F) where
    Ψ-suc-incr : ∀ α → ⦃ WellFormed α ⦄ → suc-increasing (Ψ F α)
    Ψ-suc-incr zero    = s-incr
    Ψ-suc-incr (suc α) = ′-suc-incr (Ψ-normal² α) (Ψ-suc-incr α)
    Ψ-suc-incr (lim f) β = <f⇒<l {n = 0} (begin-strict
      suc β                               <⟨ Ψ-suc-incr (f 0) β ⟩
      Ψ F (f 0) (suc β)                   ≤⟨ Ψ-mono²-≤ _ (s≤s (Ψ-incr²-≤ _ _)) ⟩
      Ψ F (f 0) (suc (Ψ F (lim f) β))     ∎)
```

**定理** 如果 `F` 在零处增长, 且在良构后继处增长, 且保良构, 那么任意良构 `Ψ F α` 也保良构.

```agda
  module _ (z-incr : zero-increasing F) (s-incr : suc-increasing F) (wfp₀ : wf-preserving F) where
    Ψ-wfp² : ∀ α → ⦃ WellFormed α ⦄ → wf-preserving (Ψ F α)
    Ψ-wfp² zero    wfβ = wfp₀ wfβ
    Ψ-wfp² (suc α) wfβ = ′-wfp (Ψ-normal² α) (Ψ-zero-incr z-incr α) (Ψ-suc-incr s-incr α) (Ψ-wfp² α) wfβ
    Ψ-wfp² (lim f) wfβ = rec-wfp wf mono incr wfp wfβ where
      wf : WellFormed (Ψ F (lim f) zero)
      wf = Ψ-wfp² (f _) tt , wrap (λ < → Ψ-<⇒< (fm<fn <) (Ψ-zero-incr z-incr (f _)))
      mono : ≤-monotonic (F ∘ₗ f ∘ suc)
      mono ≤ = l≤l (λ n → Ψ-mono²-≤ (f n) (s≤s ≤))
      incr : <-increasing (F ∘ₗ f ∘ suc)
      incr α =            begin-strict
        α                 <⟨ <s ⟩
        suc α             ≤⟨ ≤f⇒≤l (Ψ-incr²-≤ (f 0) _) ⟩
        (F ∘ₗ f ∘ suc) α  ∎
      wfp : wf-preserving (F ∘ₗ f ∘ suc)
      wfp {α} wfα = (λ {n} → Ψ-wfp² (f n) {suc α} wfα)
                  , wrap (λ < → Ψ-<⇒< (fm<fn <) (Ψ-suc-incr s-incr _ _ ⦃ wfα ⦄))
```

**推论** `Ψ F` 对两个参数保良构.

```agda
    Ψ-wfp¹ : ∀ β → ⦃ WellFormed β ⦄ → wf-preserving (λ α → Ψ F α β)
    Ψ-wfp¹ β {α} wfα = Ψ-wfp² α ⦃ wfα ⦄ it

    Ψ-wfp₂ : ∀ α β → ⦃ WellFormed α ⦄ → ⦃ WellFormed β ⦄ → WellFormed (Ψ F α β)
    Ψ-wfp₂ α β = Ψ-wfp² α it
```

### 实例化

以 `ω ^_` 实例化 Properties 模块即可得到 `φ` 的性质.

```agda
open Properties (ω ^_) ω^-normal
```

我们只列出主要结论.

**事实** 每个 `φ α` 都是序数嵌入.

```agda
φ-normal : ∀ α → normal (φ α)
φ-normal = Ψ-normal²
```

**事实** `φ` 对第一个参数满足单调性与合同性.

```agda
module _ {α β γ} ⦃ wfα : WellFormed α ⦄ ⦃ wfβ : WellFormed β ⦄ where

  φ-mono¹-≤ : α ≤ β → φ α γ ≤ φ β γ
  φ-mono¹-≤ = Ψ-mono¹-≤

  φ-cong¹-≤ : α ≈ β → φ α γ ≈ φ β γ
  φ-cong¹-≤ = Ψ-cong¹
```

**事实** 高阶不动点同时也是低阶不动点.

```agda
  φ-fp : α < β → (φ β γ) isFixpointOf (φ α)
  φ-fp = Ψ-fp
```

**事实** 以下三种情况可以建立 `φ α β < φ γ δ` 关系.

```agda
module _ {α β γ δ} ⦃ wfα : WellFormed α ⦄ ⦃ wfγ : WellFormed γ ⦄ where

  φ-≈⇒< : α ≈ γ → β < δ → φ α β < φ γ δ
  φ-≈⇒< = Ψ-≈⇒<

  φ-<⇒< : α < γ → β < φ γ δ → φ α β < φ γ δ
  φ-<⇒< = Ψ-<⇒<

  φ->⇒< : φ α β < δ → φ α β < φ γ δ
  φ->⇒< = Ψ->⇒<
```

**事实** `φ` 对两个参数保良构.

```agda
module _ {α β} ⦃ wfα : WellFormed α ⦄ ⦃ wfβ : WellFormed β ⦄ where
  φ-wfp₂ : WellFormed (φ α β)
  φ-wfp₂ = Ψ-wfp₂ ω^-zero-incr ω^-suc-incr ω^-wfp α β
```

## 突破 Feferman–Schütte 屏障

我们向更高阶进发, 这需要突破二元Veblen函数的极限, 也叫 Feferman–Schütte 屏障, 因为它是一些较弱系统的上限. 但 Agda 可以轻易突破, 只需取 `λ α → φ α zero` 的不动点枚举, 得到所谓 `Γ` 层级.

```agda
  Γ : Ord → Ord
  Γ = (λ α → φ α zero) ′
```

最小的 `Γ` 数是

$$Γ_0 = φ_{φ_{φ_{φ_{...}(0)}(0)}(0)}(0)$$

```agda
  _ : Γ zero ≡ (λ α → φ α zero) ⋱ zero
  _ = refl
```

`Γ` 确实是对 `λ α → φ α zero` 的不动点的枚举, 因为 `λ α → φ α zero` 对任意良构 `α` 是序数嵌入. 这可以从 `Ψ-mono¹-≤` 和 `Ψ-<⇒<` 看出. 这些引理都要求良构序数. 可见, 从 `Γ` 开始, 必须完全限定到良构序数才能继续理论的构筑. 我们就此结束本系列文章的第1卷. 第2卷会从良构序数的 record 类型的定义开始, 然后把第1卷的结果都迁移过去, 再继续向 LVO 进发.
