module AltArtemov.TermVector.Notation where

open import Data.Nat using (ℕ ; zero ; suc)

open import AltArtemov.Term
open import AltArtemov.TermVector.Core
open import AltArtemov.Type


infixr 5 _∶⋯∶_

-- tₙ ∶ tₙ₋₁ ∶ ⋯ ∶ t ∶ A
_∶⋯∶_ : ∀ {n} (ts : Tms n) (A : Ty) → Ty
[]       ∶⋯∶ A = A
(t ∷ ts) ∶⋯∶ A = t ∶ ts ∶⋯∶ A


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


-- PAIRⁿ tₙ sₙ ∶ PAIRⁿ⁻¹ tₙ₋₁ sₙ₋₁ ∶ ⋯ ∶ PAIR t s
PAIRs[_] : ∀ n (ts ss : Tms n) → Tms n
PAIRs[ zero ]  []       []       = []
PAIRs[ suc n ] (t ∷ ts) (s ∷ ss) = PAIR[ n ] t s ∷ PAIRs[ n ] ts ss


-- FSTⁿ tₙ ∶ FSTⁿ⁻¹ tₙ₋₁ ∶ ⋯ ∶ FST t
FSTs[_] : ∀ n (ts : Tms n) → Tms n
FSTs[ zero ]  []       = []
FSTs[ suc n ] (t ∷ ts) = FST[ n ] t ∷ FSTs[ n ] ts


-- SNDⁿ tₙ ∶ SNDⁿ⁻¹ tₙ₋₁ ∶ ⋯ ∶ SND t
SNDs[_] : ∀ n (ts : Tms n) → Tms n
SNDs[ zero ]  []       = []
SNDs[ suc n ] (t ∷ ts) = SND[ n ] t ∷ SNDs[ n ] ts


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
