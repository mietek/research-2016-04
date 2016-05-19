module AltArtemov.Type.Renaming where

open import AltArtemov.Context.Representation
open import AltArtemov.Term.Representation
open import AltArtemov.Type.Core
open import AltArtemov.Variable.Representation


renᴬ : ∀ {g g′} → g′ ≥ᵍ g → RRen Ty g g′
renᴬ r ★       = ★
renᴬ r (t ∶ A) = renᵗ r t ∶ renᴬ r A
renᴬ r (A ⊃ B) = renᴬ r A ⊃ renᴬ r B
renᴬ r (A ∧ B) = renᴬ r A ∧ renᴬ r B
renᴬ r ⊥      = ⊥


wkᴬ* : ∀ {g} → Ty ∅ → Ty g
wkᴬ* = renᴬ g≥ᵍ∅
