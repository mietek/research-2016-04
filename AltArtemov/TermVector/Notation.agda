module AltArtemov.TermVector.Notation where

open import Data.Nat using (ℕ ; zero ; suc)

open import AltArtemov.Term
open import AltArtemov.TermVector.Core


-- VAR x ∶ VAR x ∶ ⋯ ∶ VAR x
VARs[_] : ∀ n (i : ℕ) → Tms n
VARs[ zero ]  i = []
VARs[ suc n ] i = VAR[ n ] i ∷ VARs[ n ] i


-- LAMⁿ tₙ ∶ LAMⁿ⁻¹ tₙ₋₁ ∶ ⋯ ∶ LAM t
LAMs[_] : ∀ n (ts : Tms n) → Tms n
LAMs[ zero ]  []       = []
LAMs[ suc n ] (t ∷ ts) = LAM[ n ] t ∷ LAMs[ n ] ts


-- APPⁿ tₙ sₙ ∶ APPⁿ⁻¹ tₙ₋₁ sₙ₋₁ ∶ ⋯ ∶ APP t s
APPs[_] : ∀ n (ts ss : Tms n) → Tms n
APPs[ zero ]  []       []       = []
APPs[ suc n ] (t ∷ ts) (s ∷ ss) = APP[ n ] t s ∷ APPs[ n ] ts ss


-- UPⁿ tₙ ∶ UPⁿ⁻¹ tₙ₋₁ ∶ ⋯ ∶ UP t
UPs[_] : ∀ n (ts : Tms n) → Tms n
UPs[ zero ]  []       = []
UPs[ suc n ] (t ∷ ts) = UP[ n ] t ∷ UPs[ n ] ts


-- DOWNⁿ tₙ ∶ DOWNⁿ⁻¹ tₙ₋₁ ∶ ⋯ ∶ DOWN t
DOWNs[_] : ∀ n (ts : Tms n) → Tms n
DOWNs[ zero ]  []       = []
DOWNs[ suc n ] (t ∷ ts) = DOWN[ n ] t ∷ DOWNs[ n ] ts


-- BOOMⁿ tₙ ∶ BOOMⁿ⁻¹ tₙ₋₁ ∶ ⋯ ∶ BOOM t
BOOMs[_] : ∀ n (ts : Tms n) → Tms n
BOOMs[ zero ]  []       = []
BOOMs[ suc n ] (t ∷ ts) = BOOM[ n ] t ∷ BOOMs[ n ] ts
