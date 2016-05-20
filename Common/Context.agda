module Common.Context where

open import Common.Core public


data Cx (X : Set) : Set where
  ∅   : Cx X
  _,_ : Cx X → X → Cx X


ᵍ⌊_⌋ : ∀ {X} → Cx X → ℕ
ᵍ⌊ ∅ ⌋     = zero
ᵍ⌊ Γ , A ⌋ = suc ᵍ⌊ Γ ⌋
