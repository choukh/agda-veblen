{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --overlapping-instances #-}

module Ordinal.Bundles where

open import Ordinal as ord using () renaming (Ord to ord)
open import Ordinal.WellFormed as ord using (WellFormed)
import Ordinal.Function as ord

open import Data.Unit using (tt)
open import Data.Nat as ℕ using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; Σ-syntax)
open import Function using (_∘_)
open import Level using (0ℓ)
open import Relation.Binary using (Monotonic₁)
open import Relation.Binary using (Rel; _⇒_)

record Ord : Set where
  constructor _&
  field
    carrier : ord
    ⦃ wellFormed ⦄ : WellFormed carrier

open Ord

_≤_ : Rel Ord 0ℓ
(α &) ≤ (β &) = α ord.≤ β

_<_ : Rel Ord 0ℓ
(α &) < (β &) = α ord.< β

_≈_ : Rel Ord 0ℓ
(α &) ≈ (β &) = α ord.≈ β

monoSequence : (ℕ → Ord) → Set
monoSequence = Monotonic₁ ℕ._<_ _<_

zero : Ord
zero = ord.zero &

suc : Ord → Ord
suc (α &) = ord.suc α &
