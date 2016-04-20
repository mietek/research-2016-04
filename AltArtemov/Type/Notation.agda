module AltArtemov.Type.Notation where

open import AltArtemov.TermVector
open import AltArtemov.Type.Core


infixr 5 _∶⋯∶_

-- tₙ ∶ tₙ₋₁ ∶ ⋯ ∶ t ∶ A
_∶⋯∶_ : ∀ {n} (ts : Tms n) (A : Ty) → Ty
[]       ∶⋯∶ A = A
(t ∷ ts) ∶⋯∶ A = t ∶ ts ∶⋯∶ A
