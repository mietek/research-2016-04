module AltArtemov.Variable.Representation.Core where

open import Data.Fin using (Fin ; zero ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import AltArtemov.Context.Representation


data ◌∈_ : CxR → Set where
  top : ∀ {g} → ◌∈ (g ,◌)
  pop : ∀ {g} → ◌∈ g → ◌∈ (g ,◌)


inv-pop : ∀ {g} {i i′ : ◌∈ g} → pop i ≡ pop i′ → i ≡ i′
inv-pop refl = refl


⌊_⌋ⁱ : ∀ {g} → ◌∈ g → Fin ⌊ g ⌋ᵍ
⌊ top ⌋ⁱ   = zero
⌊ pop i ⌋ⁱ = suc ⌊ i ⌋ⁱ
