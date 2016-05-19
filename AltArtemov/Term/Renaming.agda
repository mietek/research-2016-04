module AltArtemov.Term.Renaming where

open import AltArtemov.Context
open import AltArtemov.Type
open import AltArtemov.Variable


Ren : ∀ {X : Set} → (Cx → X → Set) → Cx → Cx → Set
Ren Ξ Γ Γ′ = ∀ {A} → Ξ Γ A → Ξ Γ′ A
