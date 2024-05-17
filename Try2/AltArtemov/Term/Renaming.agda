module Try2.AltArtemov.Term.Renaming where

open import Try2.AltArtemov.Context
open import Try2.AltArtemov.Type
open import Try2.AltArtemov.Variable


Ren : ∀ {X : Set} → (Cx → X → Set) → Cx → Cx → Set
Ren Ξ Γ Γ′ = ∀ {A} → Ξ Γ A → Ξ Γ′ A
