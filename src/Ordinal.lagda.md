---
title: Agda大序数(1) 序数的定义
zhihu-tags: Agda, 序数, 大数数学
zhihu-url: https://zhuanlan.zhihu.com/p/572691308
---

# Agda大序数(1) 序数的定义

> 交流Q群: 893531731  
> 总目录: [Everything.html](https://choukh.github.io/agda-lvo/Everything.html)  
> 本文源码: [Ordinal.lagda.md](https://github.com/choukh/agda-lvo/blob/main/src/Ordinal.lagda.md)  
> 高亮渲染: [Ordinal.html](https://choukh.github.io/agda-lvo/Ordinal.html)  
> 如果你在知乎看到本文: 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

## 前言

本系列文章介绍一种基于类型论的序数理论, 并以实现大 Veblen 序数, 即 [LVO](https://en.wikipedia.org/wiki/Large_Veblen_ordinal) 的形式化为最终目标. 我们采用标准 Agda 作为基础, 仅依赖于标准库 [agda-stdlib](https://agda.github.io/agda-stdlib/index), 并且打开了社区公认安全 (可期待一致性) 的 flag

```agda
{-# OPTIONS --without-K --safe #-}
```

以实现无公理且构造主义的直谓可计算序数.

具体地, 我们实现了超限归纳法的类型论对应, 以及序数算术和 Veblen 不动点理论, 并以此定义了二元 Veblen 函数, n元 Veblen 函数乃至序数元 Veblen 函数. 得益于其可计算特性, 我们的序数可用于快速增长层级等大数函数,并得到可计算的大数, 如 $f_{LVO}(3)$. 虽然现实中计算不出来, 但其停机性由 Agda 的 [Termination Checking](https://agda.readthedocs.io/en/v2.6.2.2/language/termination-checking.html) 保证.

本文为文学Agda脚本, 既是 markdown 文件, 也是可通过类型检查的 Agda 源码. 原文件托管于本项目的 Github 仓库 [agda-lvo](https://github.com/choukh/agda-lvo).

```agda
module Ordinal where
```

## 前置

- 了解[冯诺依曼序数](https://en.wikipedia.org/wiki/Set-theoretic_definition_of_natural_numbers)
- Agda语言达到 [PLFA](https://agda-zh.github.io/PLFA-zh/) 第一册水平
- 理解以下[标准库](https://agda.github.io/agda-stdlib/index)依赖所涉及的数学概念

我们只使用最底层的宇宙, 因此导入了 `0ℓ` 以实例化库中其他宇宙多态类型. 我们需要自然数来定义序数, 但本章暂不需要关于自然数的理论, 所以只导入了 `ℕ`.

```agda
open import Level using (0ℓ)
open import Data.Nat using (ℕ)
```

接下来是一些基本的逻辑概念. 其中空类型 `⊥` 和单值类型 `⊤` 都将用于序数的定义. 和类型 `_⊎_` 用作析取, 积类型 `_×_` 用作合取, 而存在量词 `∃` 只是 Σ类型上的一种 syntax. 本质上, `_×_` 和 `∃` 都是 Σ类型的特化, 都可以用 `_,_` 解构.

```agda
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
```

`Rel` 用于定义序数上的序关系. 我们将证明这些序关系的性质, 如自反性, 对称性, 等等, 因此导入了相应的定义和引理. 虽然大部分情况下我们都使用 `OrdSetoid` 中的等价关系 `_≈_`, 但我们会尽量尝试建立内涵相等 `_≡_`, 它蕴含我们的 `_≈_`.

```agda
open import Relation.Binary using (Rel; _⇒_)
open import Relation.Binary.Definitions
  using (Reflexive; Symmetric; Transitive; Trans; Irreflexive; Asymmetric)
open import Relation.Binary.Consequences using (trans∧irr⇒asym)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
```

以下三个模块, 第一个以"当且仅当"为等价关系建立了 `⇔-setoid`, 第二个允许我们对 `_⇔_` 等价式做改写推理, 第三个允许我们从 `_⇔_` 中恢复蕴含式.

```agda
open import Function.Equivalence
  using (Equivalence; _⇔_; ⇔-setoid) renaming (equivalence to mk⇔)
open import Relation.Binary.Reasoning.Setoid (⇔-setoid 0ℓ)
  using (begin_; step-≈; _∎)
open import Function.Equality using (_⟨$⟩_)
```

## 序数

我们知道自然数 `ℕ` 有两个构造子: 零和后继. 序数则在此基础上增加了极限构造子 `lim`. 如果 `f` 是 `ℕ` 到序数的函数, 那么 `lim f` 也是序数. 这样的 `f` 又叫做 `lim f` 的基本序列 (fundamental sequence)[^1], 而 `lim f` 则是基本序列 `f` 的极限. 这样的定义允许我们很方便地讨论零, 后继序数, 极限序数三种情况.

[^1]: _ 严格来说基本序列要求典范性, 但我们这里不追求, 转而使用广集来处理多个序列表示同一个序数的问题.

```agda
data Ord : Set where
  zero : Ord
  suc  : Ord → Ord
  lim  : (ℕ → Ord) → Ord
```

严格来说基本序列要求单调性, 因此这里定义的 `Ord` 比真正的序数要宽泛很多. 我们将在下一章引入一个"良构"谓词来解决这个问题. 并且我们会在后续章节证明我们构造的序数函数都是保良构的. 不过现在这点并不影响我们建立序数的序关系, 如果影响的话我们根本就不可能表达单调性.

以下是构造子单射的例行证明.

```agda
suc-injective : ∀ {α β} → suc α ≡ suc β → α ≡ β
suc-injective refl = refl

lim-injective : ∀ {f g} → lim f ≡ lim g → f ≡ g
lim-injective refl = refl
```

## 前驱

为了定义序关系我们需要引入一个辅助概念, 叫做前驱**深度** `Depth`, 它是以序数为索引的类型. 零没有前驱, 因此 `Depth zero` 没有任何可能的取值, 即为 ⊥. 后继序数 `suc α` 的前驱要么是其直接前驱 `α`, 要么是 `α` 的前驱, 因此 `Depth (suc α)` 的可能取值要么是 `tt` 要么是 `Depth α`. 极限序数 `lim f` 的前驱是所有 `f n` 的前驱, 因此 `Depth (lim f)` 的可能取值是 `Depth (f n)` 对 `n` 求和.

```agda
Depth : Ord → Set
Depth zero    = ⊥
Depth (suc α) = ⊤ ⊎ Depth α
Depth (lim f) = ∃[ n ] Depth (f n)
```

现在我们可以定义前驱运算 `_∸_` 了. 对任意序数 `α` 和 `α` 的任意前驱深度 `d : Depth α`, 我们可以计算出 `α` 在深度 `d` 处的前驱 `α ∸ d`. 具体地

- `α` 为零的情况不存在, Agda 可以直接识别出这一点
- 对后继序数 `suc α`, 解构 `d : Depth (suc α)`
  - 若为 `tt`, 那么取直接前驱 `α`
  - 若为 `d : Depth α`, 那么递归计算 `α ∸ d`
- 对极限序数 `lim f`, 解构 `d : Depth (lim f)`, 必然存在 `n : ℕ` 使得 `d : Depth (f n)`, 我们递归计算 `f n ∸ d`

```agda
infixl 6 _∸_

_∸_ : ∀ α → Depth α → Ord
suc α ∸ inj₁ tt = α
suc α ∸ inj₂ d  = α ∸ d
lim f ∸ (n , d) = f n ∸ d
```

## 非严格序

序数上的非严格序 `_≤_` 归纳定义为三种情况. 第一种 `zero ≤ β` 是无条件成立的, 这与 `ℕ` 的 [`z≤n`](https://choukh.github.io/agda-lvo/Data.Nat.Base.html#1547) 一样. 第二种 `suc α ≤ β` 要求存在 `β` 的某个前驱 `β ∸ d` 使得 `α ≤ β ∸ d`. 这类似于自然数的 [`s≤s`](https://choukh.github.io/agda-lvo/Data.Nat.Base.html#1589), 只是右边还包括了极限的情况. 第三种 `lim f ≤ β` 要求 `β` 大于等于基本序列 `f` 的每一个取值.

```agda
infix 4 _≤_ _≥_ _≰_ _≱_

data _≤_ : Rel Ord 0ℓ where
  z≤ : ∀ {β}                        → zero  ≤ β
  s≤ : ∀ {α β d}  → α ≤ β ∸ d       → suc α ≤ β
  l≤ : ∀ {f β}    → (∀ n → f n ≤ β) → lim f ≤ β

_≥_ : Rel Ord 0ℓ
α ≥ β = β ≤ α

_≰_ : Rel Ord 0ℓ
α ≰ β = ¬ α ≤ β

_≱_ : Rel Ord 0ℓ
α ≱ β = ¬ β ≤ α
```

由此定义可以证明以下基本事实.

**引理** 如果 `α` 小于等于 `β` 的任意前驱, 那么 `α ≤ β`.  
**证明** 讨论 `α` 并反演 `≤` 即可. 我们对第二和第三种情况递归调用了要证的命题 `≤∸⇒≤` 本身, 也即用了归纳法. ∎

```agda
≤∸⇒≤ : ∀ {α β d} → α ≤ β ∸ d → α ≤ β
≤∸⇒≤ {zero}  _       = z≤
≤∸⇒≤ {suc α} (s≤ ≤∸) = s≤ (≤∸⇒≤ ≤∸)
≤∸⇒≤ {lim f} (l≤ f≤) = l≤ λ n → ≤∸⇒≤ (f≤ n)
```

**引理** 如果 `α ≤ β`, 那么 `α` 的任意前驱小于等于 `β`.  
**证明** 这次除了讨论 `α` 并反演 `≤` 之外, 还要解构 `α` 的前驱深度 `d`. 看起来组合很多, 但大多数组合都是不可能的, Agda 可以自动识别. 归结下来就 3 种情况:

- `α` 小于等于 `β` 的直接前驱
- `α` 小于等于 `β` 的直接前驱以外的前驱
- `α` 的基本序列的每个取值 `f n` 都小于等于 `β`

第一和第二种情况调用了上一条命题 `≤∸⇒≤`, 第二和第三种情况递归调用了要证的命题 `≤⇒∸≤` 本身. ∎

```agda
≤⇒∸≤ : ∀ {α β d} → α ≤ β → α ∸ d ≤ β
≤⇒∸≤ {suc α} {d = inj₁ tt} (s≤ ≤∸) = ≤∸⇒≤ ≤∸
≤⇒∸≤ {suc α} {d = inj₂ d}  (s≤ ≤∸) = ≤⇒∸≤ (≤∸⇒≤ ≤∸)
≤⇒∸≤ {lim f} {d = n , d}   (l≤ f≤) = ≤⇒∸≤ (f≤ n)
```

用类似的方法, 我们证明了以下四条引理. 其中第一条只是 `≤∸⇒≤` 的特殊情况, 第二和第四条需要讨论 `α` 并反演 `≤`, 第三条只需反演 `≤`.

```agda
s≤⇒≤ : ∀ {α β} → suc α ≤ β → α ≤ β
s≤⇒≤ (s≤ ≤∸) = ≤∸⇒≤ ≤∸

≤⇒≤s : ∀ {α β} → α ≤ β → α ≤ suc β
≤⇒≤s {zero}  _               = z≤
≤⇒≤s {suc α} (s≤ {d = d} ≤∸) = s≤ {d = inj₂ d} ≤∸
≤⇒≤s {lim f} (l≤ f≤)         = l≤ λ n → ≤⇒≤s (f≤ n)

l≤⇒f≤ : ∀ {α f n} → lim f ≤ α → f n ≤ α
l≤⇒f≤ {n = n} (l≤ f≤) = f≤ n

≤f⇒≤l : ∀ {α f n} → α ≤ f n → α ≤ lim f
≤f⇒≤l {zero}  _       = z≤
≤f⇒≤l {suc α} (s≤ ≤∸) = s≤ ≤∸
≤f⇒≤l {lim f} (l≤ f≤) = l≤ λ n → ≤f⇒≤l (f≤ n)
```

接下来是一条重要引理.

**引理** 后继运算 `suc` 保持 `_≤_` 关系.  
**证明** 证明相当简短. 首先调用构造子 `s≤`, 那么只需证对某 `d` 有 `α ≤ suc β ∸ d`. 令 `d` 为 `tt`, 也即取 `suc β` 的直接前驱 `β`, 只需证 `α ≤ β`, 此即前提. ∎

```agda
s≤s : ∀ {α β} → α ≤ β → suc α ≤ suc β
s≤s ≤ = s≤ {d = inj₁ tt} ≤
```

逆命题同样可证, 只需反演 `≤` 并讨论 `d` 即可.

```agda
s≤s⇒≤ : ∀ {α β} → suc α ≤ suc β → α ≤ β
s≤s⇒≤ (s≤ {d = inj₁ tt} ≤ ) = ≤
s≤s⇒≤ (s≤ {d = inj₂ d}  ≤∸) = ≤∸⇒≤ ≤∸
```

结合以上两条, 可知 `suc` *反映* `_≤_`. 该命题是一个 `_⇔_` 等价式, 后续章节我们会用它做改写推理.

```agda
≤⇔s≤s : ∀ {α β} → α ≤ β ⇔ suc α ≤ suc β
≤⇔s≤s = mk⇔ s≤s s≤s⇒≤
```

由引理 `s≤s` 和 `≤f⇒≤l` 不难证明 `≤` 是自反的.

```agda
instance
  ≤-refl : Reflexive _≤_
  ≤-refl {zero}  = z≤
  ≤-refl {suc α} = s≤s ≤-refl
  ≤-refl {lim f} = l≤ λ n → ≤f⇒≤l ≤-refl
```

传递性的证明比较麻烦, 需要讨论 `α`, 并反演两个 `≤` 式, 归结为五种情况, 其中后四种都用了归纳假设.

```agda
≤-trans : Transitive _≤_
≤-trans {zero}  z≤                     _        = z≤
≤-trans {suc α} (s≤ {d = inj₁ tt} α≤β) (s≤ β≤γ) = s≤ (≤-trans α≤β β≤γ)
≤-trans {suc α} (s≤ {d = inj₂ d}  α≤β) (s≤ β≤γ) = s≤ (≤-trans α≤β (≤⇒∸≤ β≤γ))
≤-trans {suc α} (s≤ {d = n , d}   α≤β) (l≤ f≤γ) = ≤-trans (s≤ α≤β) (f≤γ n)
≤-trans {lim f} (l≤ f≤β)               β≤γ      = l≤ λ n → ≤-trans (f≤β n) β≤γ
```

最后证明三条引理结束本小节. 第一条 `≤s` 是因为 `α ≤ α ≡ suc α ∸ inj₁ tt ≤ suc α`. 第二条 `s∸≤` 是说 `α` 的任意前驱的后继都小于等于 `α`, 讨论 `α` 和 `d` 并由上面的一些引理即证. 第三条是 `≤f⇒≤l` 和 `≤-refl` 的直接推论.

```agda
≤s : ∀ {α} → α ≤ suc α
≤s = ≤∸⇒≤ {d = inj₁ tt} ≤-refl

s∸≤ : ∀ {α d} → suc (α ∸ d) ≤ α
s∸≤ {suc α} {d = inj₁ tt} = ≤-refl
s∸≤ {suc α} {d = inj₂ d } = s≤s (≤⇒∸≤ ≤-refl)
s∸≤ {lim f} {d = d}       = s≤ ≤-refl

f≤l : ∀ {f n} → f n ≤ lim f
f≤l = ≤f⇒≤l ≤-refl
```

## 外延相等

`≤-refl` 和 `≤-trans` 说明 `_≤_` 是预序. 我们期望 `_≤_` 是偏序, 现在只缺反对称性, 但我们无法证明 `_≤_` 对内涵等词 `_≡_` 反对称. 实际上, 我们从 `_≤_` 直接定义出满足反对称的 `_≈_`, 我们称之为*序列外延相等*.

```agda
infix 4 _≈_ _≉_

_≈_ : Rel Ord 0ℓ
α ≈ β = α ≤ β × β ≤ α

_≉_ : Rel Ord 0ℓ
α ≉ β = ¬ α ≈ β
```

`_≈_` 的自反性和传递性由 `_≤_` 的相应性质得到, 对称性依定义只需调换两个 `_≤_` 式的先后顺序即可.

```agda
≈-refl : Reflexive _≈_
≈-refl = ≤-refl , ≤-refl

≈-sym : Symmetric _≈_
≈-sym = λ { (α≤β , β≤α) → β≤α , α≤β }

≈-trans : Transitive _≈_
≈-trans = λ { (α≤β , β≤α) (β≤γ , γ≤β) → ≤-trans α≤β β≤γ , ≤-trans γ≤β β≤α }
```

再证一些关于 `_≈_` 的引理. 由 `≈-refl` 立即可知 `_≡_` 蕴含 `_≈_`.

```agda
≡⇒≈ : _≡_ ⇒ _≈_
≡⇒≈ refl = ≈-refl
```

`≤ zero` 蕴含 `≈ zero`, 但要得到 `≡ zero` 则要求下一章的良构条件. 因为比如非良构的 `lim (λ _ → zero)` 外延等于 `zero`, 但显然不是 `zero`.

```agda
≤z⇒≈z : ∀ {α} → α ≤ zero → α ≈ zero
≤z⇒≈z {zero} _ = ≈-refl
≤z⇒≈z {suc α} (s≤ {d = ()} _)
≤z⇒≈z {lim f} ≤ = ≤ , z≤
```

以下三条是 `_≈_` 版本的 `s≤s`, `s≤s⇒≤` 和 `≤⇔s≤s`.

```agda
s≈s : ∀ {α β} → α ≈ β → suc α ≈ suc β
s≈s (α≤β , β≤α) = s≤s α≤β , s≤s β≤α

s≈s⇒≈ : ∀ {α β} → suc α ≈ suc β → α ≈ β
s≈s⇒≈ (sα≤sβ , sβ≤sα) = s≤s⇒≤ sα≤sβ , s≤s⇒≤ sβ≤sα

≈⇔s≈s : ∀ {α β} → α ≈ β ⇔ suc α ≈ suc β
≈⇔s≈s = mk⇔ s≈s s≈s⇒≈
```

如果两个序列逐项相等, 那么它们的极限相等.

```agda
l≈l : ∀ {f g} → (∀ {n} → f n ≈ g n) → lim f ≈ lim g
l≈l ext = l≤ (λ n → ≤f⇒≤l (proj₁ ext))
        , l≤ (λ n → ≤f⇒≤l (proj₂ ext))
```

## 否命题

我们想要引入序数的严格序 `_<_`, 但其性质的证明依赖于 `_≤_` 的一些否定式, 我们先证明它们.

**引理** 后继不小于等于零.  
**证明** 若不然, 可以反演出 ⊥. ∎

```agda
s≰z : ∀ {α} → suc α ≰ zero
s≰z (s≤ {d = ⊥} ≤) = ⊥
```

**引理** `α` 的后继不小于等于 `α`.  
**证明** `α` 为零的情况上面已证, 为后继或极限的情况用归纳假设可证. ∎

```agda
s≰ : ∀ {α} → suc α ≰ α
s≰ {zero} = s≰z
s≰ {suc α} ≤ = s≰ (s≤s⇒≤ ≤)
s≰ {lim f} (s≤ {d = n , d} (l≤ f≤)) = s≰ (s≤ (f≤ n))
```

**引理** 如果 `α` 小于等于 `β`, 那么 `α` 的任意前驱不可能大于等于 `β`.  
**证明** 见代码. ∎

```agda
≤⇒∸≱ : ∀ {α β d} → α ≤ β → α ∸ d ≱ β
≤⇒∸≱ {suc α} {d = inj₁ tt} sα≤β    β≤α   = s≰ (≤-trans sα≤β β≤α)
≤⇒∸≱ {suc α} {d = inj₂ d}  sα≤β    β≤α∸d = ≤⇒∸≱ (s≤⇒≤ sα≤β) β≤α∸d
≤⇒∸≱ {lim f} {d = n , d}   (l≤ f≤) β≤f∸d = ≤⇒∸≱ (f≤ n) β≤f∸d
```

**引理** 任何序数都不小于等于自身的任意前驱.  
**证明** 这是上一条的特化. ∎

```agda
≰∸ : ∀ {α d} → α ≰ α ∸ d
≰∸ = ≤⇒∸≱ ≤-refl
```

## 严格序

我们将 `α` 小于 `β` 定义为 `α` 小于等于 `β` 的某个前驱.

```agda
infix 4 _<_ _>_ _≮_ _≯_

_<_ : Rel Ord 0ℓ
α < β = ∃[ d ] α ≤ β ∸ d
```

注意这里不使用标准库的 [NonStrictToStrict](https://agda.github.io/agda-stdlib/Relation.Binary.Construct.NonStrictToStrict.html) 框架把 `_<_` 定义成 `α ≤ β × α ≉ β`, 理由有三.

1. 在缺少排中律的情况下无法从 `α ≤ β × α ≉ β` 得到 `α ≤ β × α ≱ β`.
2. 即使有 `α ≱ β`, 也无法得到我们的 `_<_`. 因为在缺少排中律的情况下无法从否定式得到存在性命题.
3. 由我们的 `_<_` 和前述引理 `≤⇒∸≱` 可以得到 `α ≱ β`, 见后文的 `<⇒≱`.

总之, 在构造主义中, 我们的定义严格强于 `α ≤ β × α ≉ β`. 它使命题的表述更加直接且符合构造主义, 因为不涉及否定式. 此外, `α ≤ β` 无法分裂成 `α < β ⊎ α ≈ β`, 因为后者严格强于前者, 不过这种论证并不是必须的. 我们在[独立的一章](Ordinal.Classic.html)证明了排中律下两者的等价性.

以下是例行的变体定义.

```agda
_>_ : Rel Ord 0ℓ
α > β = β < α

_≮_ : Rel Ord 0ℓ
α ≮ β = ¬ α < β

_≯_ : Rel Ord 0ℓ
α ≯ β = ¬ β < α
```

由 `_<_` 的定义立即可知零小于任意后继, 因为存在 `d = inj₁ tt` 使得 `zero ≤ suc α ∸ d`. 类似可证, 任意序数小于自身的后继.

```agda
z<s : ∀ α → zero < suc α
z<s α = inj₁ tt , z≤

<s : ∀ {α} → α < suc α
<s = inj₁ tt , ≤-refl
```

由上一小节证明的否定式可以证明 `_<_` 反自反且传递. 其中反自反分两个版本: `_≡_` 版用 refl 反演后即引理 `≰∸`; `_≈_` 版用引理 `≤⇒∸≱` 不难证明.

```agda
<-irrefl-≡ : Irreflexive _≡_ _<_
<-irrefl-≡ refl (d , α≤α∸d) = ≰∸ α≤α∸d

<-irrefl-≈ : Irreflexive _≈_ _<_
<-irrefl-≈ (α≤β , β≤α) (d , α≤β∸d) = ≤⇒∸≱ β≤α α≤β∸d
```

`_<_` 的传递性由 `_≤_` 的传递性而来. 非对称性是反自反和传递性的推论.

```agda
<-trans : Transitive _<_
<-trans (d₁ , α≤β∸d₁) (d₂ , β≤γ∸d₂) = d₂ , ≤-trans (≤∸⇒≤ α≤β∸d₁) β≤γ∸d₂

<-asym : Asymmetric _<_
<-asym = trans∧irr⇒asym {_≈_ = _≈_} ≈-refl <-trans <-irrefl-≈
```

以上就是我们能证明的最好结果. 在构造主义中我们无法证明 `_<_` 的线序性, 但这丝毫不影响后续理论 (Veblen 不动点) 的构筑.

## `<` 与 `≤` 的相互转化

我们顺着 [NonStrictToStrict](https://agda.github.io/agda-stdlib/Relation.Binary.Construct.NonStrictToStrict.html) 补上所需引理. 首先, 显然地, `_<_` 蕴含 `_≤_`.

```agda
<⇒≤ : _<_ ⇒ _≤_
<⇒≤ (d , α≤β∸d) = ≤∸⇒≤ α≤β∸d
```

然后是否命题的转化, 它们的逆命题依赖于 `_≤_` 的线序性和 `_≈_` 的可判定性, 本构筑中都不涉及.

```agda
<⇒≱ : _<_ ⇒ _≱_
<⇒≱ (d , α≤β∸d) β≤α = ≤⇒∸≱ β≤α α≤β∸d

≤⇒≯ : _≤_ ⇒ _≯_
≤⇒≯ α≤β (d , β≤α∸d) = ≤⇒∸≱ α≤β β≤α∸d
```

接着是涉及 `suc` 的两组等价式.

```agda
<⇒s≤ : ∀ {α β} → α < β → suc α ≤ β
<⇒s≤ (d , α≤β∸d) = s≤ α≤β∸d

s≤⇒< : ∀ {α β} → suc α ≤ β → α < β
s≤⇒< (s≤ {d = d} α≤β∸d) = d , α≤β∸d

<⇔s≤ : ∀ {α β} → α < β ⇔ suc α ≤ β
<⇔s≤ = mk⇔ <⇒s≤ s≤⇒<
```

```agda
≤⇒<s : ∀ {α β} → α ≤ β → α < suc β
≤⇒<s α≤β = inj₁ tt , α≤β

<s⇒≤ : ∀ {α β} → α < suc β → α ≤ β
<s⇒≤ (inj₁ tt , α≤β)   = α≤β
<s⇒≤ (inj₂ d  , α≤β∸d) = ≤∸⇒≤ α≤β∸d

≤⇔<s : ∀ {α β} → α ≤ β ⇔ α < suc β
≤⇔<s = mk⇔ ≤⇒<s <s⇒≤
```

由以上两组等价式改写可得 `_<_` 版本的 `≤⇔s≤s`.

```agda
<⇔s<s : ∀ {α β} → α < β ⇔ suc α < suc β
<⇔s<s {α} {β} = begin
  α < β         ≈⟨ <⇔s≤ ⟩
  suc α ≤ β     ≈⟨ ≤⇔<s ⟩
  suc α < suc β ∎

s<s : ∀ {α β} → α < β → suc α < suc β
s<s = _⟨$⟩_ (Equivalence.to <⇔s<s)

s<s⇒< : ∀ {α β} → suc α < suc β → α < β
s<s⇒< = _⟨$⟩_ (Equivalence.from <⇔s<s)
```

由此可得传递性的变体.

```agda
<-≤-trans : Trans _<_ _≤_ _<_
<-≤-trans α<β β≤γ = s≤⇒< (≤-trans (<⇒s≤ α<β) β≤γ)

≤-<-trans : Trans _≤_ _<_ _<_
≤-<-trans α≤β β<γ = s≤⇒< (≤-trans (s≤s α≤β) (<⇒s≤ β<γ))
```

最后是 `_<_` 版本的 `l≤⇒f≤` 和 `≤f⇒≤l`.

```agda
l<⇒f< : ∀ {α f n} → lim f < α → f n < α
l<⇒f< {n = n} (d , l≤ g≤) = d , g≤ n

<f⇒<l : ∀ {α f n} → α < f n → α < lim f
<f⇒<l α<fn = s≤⇒< (≤f⇒≤l (<⇒s≤ α<fn))
```

## 序结构

本小节总结了本章的主要结论. 我们用 `_≈_` 实例化了序结构模块并证明了 `_≤_` 是偏序且 `_<_` 是严格偏序.

```agda
open import Relation.Binary.Structures (_≈_)
  using (IsEquivalence; IsPreorder; IsPartialOrder; IsStrictPartialOrder)

≈-isEquivalence : IsEquivalence
≈-isEquivalence = record
  { refl  = ≈-refl
  ; sym   = ≈-sym
  ; trans = ≈-trans
  }

≤-isPreorder : IsPreorder _≤_
≤-isPreorder = record
  { isEquivalence = ≈-isEquivalence
  ; reflexive = proj₁
  ; trans = ≤-trans
  }

≤-isPartialOrder : IsPartialOrder _≤_
≤-isPartialOrder = record
  { isPreorder = ≤-isPreorder
  ; antisym = λ ≤ ≥ → ≤ , ≥
  }

<-isStrictPartialOrder : IsStrictPartialOrder _<_
<-isStrictPartialOrder = record
  { isEquivalence = ≈-isEquivalence
  ; irrefl = <-irrefl-≈
  ; trans = <-trans
  ; <-resp-≈ = (λ (β≤γ , _) α<β → <-≤-trans α<β β≤γ) ,
                λ (_ , α≤β) β<γ → ≤-<-trans α≤β β<γ
  }
```

由此可得 `_≤_` 和 `_<_` 都尊重 `_≈_`.

```agda
≤-respʳ-≈ = IsPartialOrder.≤-respʳ-≈ ≤-isPartialOrder
≤-respˡ-≈ = IsPartialOrder.≤-respˡ-≈ ≤-isPartialOrder
≤-resp-≈ = IsPartialOrder.≤-resp-≈ ≤-isPartialOrder

<-respʳ-≈ = IsStrictPartialOrder.<-respʳ-≈ <-isStrictPartialOrder
<-respˡ-≈ = IsStrictPartialOrder.<-respˡ-≈ <-isStrictPartialOrder
<-resp-≈ = IsStrictPartialOrder.<-resp-≈ <-isStrictPartialOrder
```

我们用本章所证明的结论来实例化标准库所提供的涉及序关系和等价关系的推理组合子, 并输出为子模块, 后续章节会大量使用它.

```agda
module ≤-Reasoning where
  open import Relation.Binary.Reasoning.Base.Triple
    ≤-isPreorder
    <-trans
    <-resp-≈
    <⇒≤
    <-≤-trans
    ≤-<-trans
    public
```

## 序数广集

由 `≈-isEquivalence` 可以构造序数广集, 它相当于是 `Ord` 在 `_≈_` 上的商集, 合并了传统理论中同一序数在我们这里的多种基本序列表示. 但我们几乎不会使用它, 而是直接使用底层的 `Ord`.

```agda
open Relation.Binary using (Setoid)

OrdSetoid : Setoid 0ℓ 0ℓ
OrdSetoid = record
  { Carrier = Ord
  ; _≈_ = _≈_
  ; isEquivalence = ≈-isEquivalence
  }
```
