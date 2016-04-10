module AltArtemov.TermVector.Notation where

open import Data.Nat using (ℕ ; zero ; suc)

open import AltArtemov.Term
open import AltArtemov.TermVector.Core


-- var x ∶ var x ∶ ⋯ ∶ var x
varⁿ[_] : ∀ n → (i : ℕ) → TmV n
varⁿ[ zero ]  i = []
varⁿ[ suc n ] i = var[ n ] i ∷ varⁿ[ n ] i


-- lamⁿ tₙ ∶ lamⁿ⁻¹ tₙ₋₁ ∶ ⋯ ∶ lam t
lamⁿ[_] : ∀ n → (ts : TmV n) → TmV n
lamⁿ[ zero ]  []       = []
lamⁿ[ suc n ] (t ∷ ts) = lam[ n ] t ∷ lamⁿ[ n ] ts


-- tₙ appⁿ sₙ ∶ tₙ₋₁ appⁿ⁻¹ ∶ sₙ₋₁ ∶ ⋯ ∶ t app s
appⁿ[_] : ∀ n → (ts ss : TmV n) → TmV n
appⁿ[ zero ]  []       []       = []
appⁿ[ suc n ] (t ∷ ts) (s ∷ ss) = app[ n ] t s ∷ appⁿ[ n ] ts ss


-- upⁿ tₙ ∶ upⁿ⁻¹ tₙ₋₁ ∶ ⋯ ∶ up t
upⁿ[_] : ∀ n → (ts : TmV n) → TmV n
upⁿ[ zero ]  []       = []
upⁿ[ suc n ] (t ∷ ts) = up[ n ] t ∷ upⁿ[ n ] ts


-- downⁿ tₙ ∶ downⁿ⁻¹ tₙ₋₁ ∶ ⋯ ∶ down t
downⁿ[_] : ∀ n → (ts : TmV n) → TmV n
downⁿ[ zero ]  []       = []
downⁿ[ suc n ] (t ∷ ts) = down[ n ] t ∷ downⁿ[ n ] ts
