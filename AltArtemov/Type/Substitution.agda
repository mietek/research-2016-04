module AltArtemov.Type.Substitution where

open import AltArtemov.Term.Representation
open import AltArtemov.Type.Core
open import AltArtemov.Variable.Representation


wkᴬ : ∀ {g} → (i : ◌∈ g) → Ty (g ∖ᵍ i) → Ty g
wkᴬ i (t ∶ A) = wkᵗ i t ∶ wkᴬ i A
wkᴬ i (A ⊃ B) = wkᴬ i A ⊃ wkᴬ i B
wkᴬ i (A ∧ B) = wkᴬ i A ∧ wkᴬ i B
wkᴬ i ⊥      = ⊥


substᴬ : ∀ {g} → Ty g → (i : ◌∈ g) → (g ∖ᵍ i) ⊢◌ → Ty (g ∖ᵍ i)
substᴬ (t ∶ A) i s = substᵗ t i s ∶ substᴬ A i s
substᴬ (A ⊃ B) i s = substᴬ A i s ⊃ substᴬ B i s
substᴬ (A ∧ B) i s = substᴬ A i s ∧ substᴬ B i s
substᴬ ⊥      i s = ⊥
