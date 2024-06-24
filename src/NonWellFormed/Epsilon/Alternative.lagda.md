---
title: Agda大序数(8*) ε的另一种表示
zhihu-tags: Agda, 序数, 大数数学
zhihu-url: https://zhuanlan.zhihu.com/p/582936614
---

# Agda大序数(8*) ε的另一种表示

> 交流Q群: 893531731  
> 目录: [NonWellFormed.html](https://choukh.github.io/agda-veblen/NonWellFormed.html)  
> 本文源码: [Epsilon/Alternative.lagda.md](https://github.com/choukh/agda-veblen/blob/main/src/NonWellFormed/Epsilon/Alternative.lagda.md)  
> 高亮渲染: [Epsilon.Alternative.html](https://choukh.github.io/agda-veblen/NonWellFormed.Epsilon.Alternative.html)  

```agda
{-# OPTIONS --without-K --safe --experimental-lossy-unification #-}

module NonWellFormed.Epsilon.Alternative where
```

## 前置

```agda
open import NonWellFormed.Ordinal
open NonWellFormed.Ordinal.≤-Reasoning
open import NonWellFormed.WellFormed
open import NonWellFormed.Arithmetic
open import NonWellFormed.Tetration using (_^^[_]_; _^^ω; _^^ω[_]; ^^≈^^[]ω)
open import NonWellFormed.Fixpoint.Lower using (π; π-fp; π≈)
open import NonWellFormed.Epsilon using (ε; ε-normal; ε-fp; ε-wfp)

open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
```

## 准备工作

我们一般化 `ε` 的下标, 并建立 `εα>1` 实例.

```agda
private variable
  α : Ord

εα≥ω : ε α ≥ ω
εα≥ω {α} =  begin
  ω         ≈˘⟨ ^-identityʳ _ ⟩
  ω ^ ⌜ 1 ⌝ ≤⟨ ≤f⇒≤l {n = 2} ≤-refl ⟩
  ε zero    ≤⟨ proj₁ ε-normal z≤ ⟩
  ε α       ∎

instance
  εα>1 : ε α > ⌜ 1 ⌝
  εα>1 {α} =  begin-strict
    ⌜ 1 ⌝     <⟨ n<ω ⟩
    ω         ≤⟨ εα≥ω ⟩
    ε α       ∎
```

## ε的另一种表示

观察序列 `ω ^^[ suc (ε α) ] ⌜_⌝` 的前几项有

$${ε_α}+1 = {ε_α}+1$$

```agda
_ : ω ^^[ suc (ε α) ] zero ≡ suc (ε α)
_ = refl
```
&nbsp;

$$ω^{{ε_α}+1} = ε_α × ω$$

```agda
ω^^[sε]1 : ω ^^[ suc (ε α) ] ⌜ 1 ⌝ ≈ ε α * ω
ω^^[sε]1 {α} =  begin-equality
  ω ^ ε α * ω   ≈⟨ *-congʳ {ω} (ε-fp α) ⟩
  ε α * ω       ∎
```
&nbsp;

$$ω^{ω^{{ε_α}+1}} = {ε_α}^ω$$

```agda
ω^^[sε]2 : ω ^^[ suc (ε α) ] ⌜ 2 ⌝ ≈ ε α ^ ω
ω^^[sε]2 {α} =                begin-equality
  ω ^ ω ^^[ suc (ε α) ] ⌜ 1 ⌝ ≈⟨ ^-congˡ ⦃ n≤ω ⦄ ω^^[sε]1 ⟩
  ω ^ (ε α * ω)               ≈˘⟨ ^-*-assoc _ _ _ ⟩
  (ω ^ ε α) ^ ω               ≈⟨ ^-congʳ {ω} (ε-fp α) ⟩
  ε α ^ ω                     ∎
```
&nbsp;

$$ω^{ω^{ω^{{ε_α}+1}}} = {ε_α}^{{ε_α}^ω}$$

```agda
ω^^[sε]3 : ω ^^[ suc (ε α) ] ⌜ 3 ⌝ ≈ ε α ^ (ε α ^ ω)
ω^^[sε]3 {α} =                begin-equality
  ω ^ ω ^^[ suc (ε α) ] ⌜ 2 ⌝ ≈⟨ ^-congˡ ⦃ n≤ω ⦄ (begin-equality
      ω ^^[ suc (ε α) ] ⌜ 2 ⌝ ≈⟨ ω^^[sε]2 ⟩
      ε α ^ ω                 ≈˘⟨ π₁ ⟩
      π ⌜ 1 ⌝                 ≈˘⟨ π-fp _ ⟩
      ε α * π ⌜ 1 ⌝           ∎) ⟩
  ω ^ (ε α * π ⌜ 1 ⌝)         ≈˘⟨ ^-*-assoc _ _ _ ⟩
  (ω ^ ε α) ^ π ⌜ 1 ⌝         ≈⟨ ^-congʳ {π ⌜ 1 ⌝} (ε-fp α) ⟩
  ε α ^ π ⌜ 1 ⌝               ≈⟨ ^-congˡ π₁ ⟩
  ε α ^ (ε α ^ ω)             ∎ where
    π₁ =                      begin-equality
      π ⌜ 1 ⌝                 ≈⟨ π≈ _ ⟩
      ε α ^ ω * ⌜ 1 ⌝         ≈⟨ *-identityʳ _ ⟩
      ε α ^ ω                 ∎
```

归纳到任意 `n` 项.

```agda
module _ (wfα : WellFormed α) where

  ω^^[sε]n : ∀ n → ω ^^[ suc (ε α) ] ⌜ suc (suc n) ⌝ ≈ ε α ^^[ ω ] ⌜ suc n ⌝
  ω^^[sε]n zero    = ω^^[sε]2
  ω^^[sε]n (suc n) =
    let ssn = ω ^^[ suc (ε α) ] ⌜ suc (suc n) ⌝ in
    let sn  = ω ^^[ suc (ε α) ] ⌜ suc n ⌝ in
                                    begin-equality
    ω ^ ssn                         ≈⟨ ^-congˡ ⦃ n≤ω ⦄ (begin-equality
      ssn                           ≡⟨⟩
      ω ^ sn                        ≈⟨ ^-congˡ ⦃ n≤ω ⦄ (begin-equality
        sn                          ≈˘⟨ ω^-absorb-+ ⦃ wf n ⦄ (< n) ⟩
        ω ^ ε α + sn                ≈⟨ +-congʳ (ε-fp _) ⟩
        ε α + sn                    ∎) ⟩
      ω ^ (ε α + sn)                ≈⟨ ^-distribˡ-+-* _ _ _ ⟩
      ω ^ ε α * ω ^ sn              ≡⟨⟩
      ω ^ ε α * ssn                 ≈⟨ *-congʳ (ε-fp _) ⟩
      ε α * ssn                     ∎) ⟩
    ω ^ (ε α * ssn)                 ≈˘⟨ ^-*-assoc _ _ _ ⟩
    (ω ^ ε α) ^ ssn                 ≈⟨ ^-congʳ (ε-fp _) ⟩
    ε α ^ ssn                       ≈⟨ ^-congˡ (ω^^[sε]n _) ⟩
    ε α ^ (ε α ^^[ ω ] suc ⌜ n ⌝) ∎ where
      wf : ∀ n → WellFormed (ω ^^[ suc (ε α) ] ⌜ n ⌝)
      wf zero    = ε-wfp wfα
      wf (suc n) = ^-wfp ω-wellFormed ⦃ n<ω ⦄ (wf n)
      <  : ∀ n → ε α < ω ^^[ suc (ε α) ] ⌜ n ⌝
      < zero     = <s
      < (suc n)  =                  begin-strict
        ε α                         <⟨ < n ⟩
        ω ^^[ suc (ε α) ] ⌜ n ⌝     ≤⟨ ^-incrˡ-≤ _ _ ⦃ n<ω ⦄ ⟩
        ω ^ ω ^^[ suc (ε α) ] ⌜ n ⌝ ∎
```

推广到 `ω` 项.

$$ω^{ω^{ω^{.^{.^{{ε_α}+1}}}}} = {ε_α}^{{ε_α}^{.^{.^ω}}}$$

```agda
  ω^^ω[sε] : ω ^^ω[ suc (ε α) ] ≈ ε α ^^ω[ ω ]
  ω^^ω[sε] = begin-equality
    lim (λ n → ω ^^[ suc (ε α) ] ⌜ n ⌝)           ≈⟨ l≈ls incr ⟩
    lim (λ n → ω ^^[ suc (ε α) ] ⌜ suc n ⌝)       ≈⟨ l≈ls (^-monoʳ-≤ ω ⦃ n≤ω ⦄ incr) ⟩
    lim (λ n → ω ^^[ suc (ε α) ] ⌜ suc (suc n) ⌝) ≈⟨ l≈l (ω^^[sε]n _) ⟩
    lim (λ n → ε α ^^[ ω ] ⌜ suc n ⌝)             ≈˘⟨ l≈ls (^-incrˡ-≤ ω (ε α)) ⟩
    lim (λ n → (ε α ^^[ ω ] ⌜ n ⌝))               ∎ where
      incr : suc (ε α) ≤ ω ^ suc (ε α)
      incr = ^-incrˡ-≤ (suc (ε α)) ω ⦃ n<ω ⦄
```

于是我们得到了 `ε` 后继项的另一种表示.

$$ε_{α+1}={ε_α}^{{ε_α}^{{ε_α}^{.^{.^.}}}}$$

```agda
  εₛ : ε (suc α) ≈ ε α ^^ω
  εₛ =                    begin-equality
    ε (suc α)             ≡⟨⟩
    ω ^^[ suc (ε α) ] ω   ≈⟨ ω^^ω[sε] ⟩
    ε α ^^[ ω ] ω         ≈˘⟨ ^^≈^^[]ω _ _ εα≥ω ⦃ n≤ω ⦄ ⟩
    ε α ^^ω               ∎
```

**注意** 这种表示只对 `ε` 成立而对 `ζ`, `η`, ... 不存在.
