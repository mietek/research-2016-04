module AltArtemov.Context.Core where

open import Data.Nat using (ℕ)
open import Function using (_∘_)

open import AltArtemov.Context.Representation
open import AltArtemov.Type


infixl 5 _,_

data Cx : Set where
  ∅   : Cx
  _,_ : Cx → Ty ∅ → Cx


⌊_⌋ᴳ : Cx → CxR
⌊ ∅ ⌋ᴳ     = ∅
⌊ Γ , A ⌋ᴳ = ⌊ Γ ⌋ᴳ ,◌


⌊_⌋ᴳ′ : Cx → ℕ
⌊_⌋ᴳ′ = ⌊_⌋ᵍ ∘ ⌊_⌋ᴳ
