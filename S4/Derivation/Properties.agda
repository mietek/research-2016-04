module S4.Derivation.Properties where

open import S4.Derivation.Core
open import S4.Type


-- Derivations have types.
ty : ∀ {Δ Γ A} (d : Δ ∙ Γ ⊢ A) → Ty
ty {A = A} d = A
