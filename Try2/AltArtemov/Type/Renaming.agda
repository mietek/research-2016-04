module Try2.AltArtemov.Type.Renaming where

open import Try2.AltArtemov.Context.Representation
open import Try2.AltArtemov.Term.Representation
open import Try2.AltArtemov.Type.Core
open import Try2.AltArtemov.Variable.Representation


renᴬ : ∀ {g g′} → g′ ≥ᵍ g → RRen Ty g g′
renᴬ r ★       = ★
renᴬ r (t ∶ A) = renᵗ r t ∶ renᴬ r A
renᴬ r (A ⊃ B) = renᴬ r A ⊃ renᴬ r B
renᴬ r (A ∧ B) = renᴬ r A ∧ renᴬ r B
renᴬ r ⊥      = ⊥


wkᴬ* : ∀ {g} → Ty ∅ → Ty g
wkᴬ* = renᴬ g≥ᵍ∅
