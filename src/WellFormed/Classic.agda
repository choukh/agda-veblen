{-# OPTIONS --without-K #-}
{-# OPTIONS --overlapping-instances #-}

module WellFormed.Classic where

open import WellFormed.Ordinal
import NonWellFormed.Classic as ord

open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; _,_)
open import Function using (it)

≤-total : ∀ α β → α ≤ β ⊎ β ≤ α
≤-total (wf α) (wf β) = ord.≤-total α β

≤-split : ∀ α β → α ≤ β → α < β ⊎ α ≈ β
≤-split _ _ = ord.≤-split

≰⇒≥ : ∀ α β → α ≰ β → α ≥ β
≰⇒≥ _ _ = ord.≰⇒≥

<l⊎≥l : ∀ α f ⦃ mf : MonoSequence f ⦄ → α < Lim f ⊎ α ≥ Lim f
<l⊎≥l (wf α) f = ord.<l⊎≥l α (dip f) ⦃ it ⦄ ⦃ wellFormed (f _) , dipMono ⦄
