module AltArtemov.Type.Notation where

open import AltArtemov.TermVector
open import AltArtemov.Type.Core


infixr 5 _∶ⁿ_

-- tₙ ∶ tₙ₋₁ ∶ ⋯ ∶ t ∶ A
_∶ⁿ_ : ∀ {n} (ts : TmV n) (A : Ty) → Ty
[]       ∶ⁿ A = A
(t ∷ ts) ∶ⁿ A = t ∶ ts ∶ⁿ A
