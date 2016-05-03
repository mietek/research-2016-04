module AltArtemov.Context.Representation.Core where

open import Data.Nat using (ℕ ; zero ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)


data CxR : Set where
  ∅   : CxR
  _,◌ : CxR → CxR


inv-,◌ : ∀ {g g′} → (g ,◌) ≡ (g′ ,◌) → g ≡ g′
inv-,◌ refl = refl


⌊_⌋ᵍ : CxR → ℕ
⌊ ∅ ⌋ᵍ    = zero
⌊ g ,◌ ⌋ᵍ = suc ⌊ g ⌋ᵍ
