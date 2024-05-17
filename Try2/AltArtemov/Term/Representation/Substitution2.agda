module Try2.AltArtemov.Term.Representation.Substitution2 where

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Fin using (Fin ; zero ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)

open import Try2.AltArtemov.Context.Representation
open import Try2.AltArtemov.Term.Representation.Core
open import Try2.AltArtemov.Term.Representation.Vector
open import Try2.AltArtemov.Variable.Representation
open import Try2.Data.Fin.Missing


-- weak : ∀ {g} → (g ,◌) ≳ᵍ g
-- weak = skip ≳ᵍ-refl

mapⁱ : ∀ {g g′} → g ≳ᵍ g′ → ◌∈ g′ → ◌∈ g
mapⁱ done     i       = i
mapⁱ (skip p) i       = pop (mapⁱ p i)
mapⁱ (keep p) top     = top
mapⁱ (keep p) (pop i) = pop (mapⁱ p i)

mapᵗ : ∀ {g g′} → g ≳ᵍ g′ → g′ ⊢◌ → g ⊢◌
mapᵗ p (VAR[ n ] i)    = VAR[ n ] (mapⁱ p i)
mapᵗ p (LAM[ n ] t)    = LAM[ n ] (mapᵗ (keep p) t)
mapᵗ p (APP[ n ] t u)  = APP[ n ] (mapᵗ p t) (mapᵗ p u)
mapᵗ p (PAIR[ n ] t u) = PAIR[ n ] (mapᵗ p t) (mapᵗ p u)
mapᵗ p (FST[ n ] t)    = FST[ n ] (mapᵗ p t)
mapᵗ p (SND[ n ] t)    = SND[ n ] (mapᵗ p t)
mapᵗ p (UP[ n ] t)     = UP[ n ] (mapᵗ p t)
mapᵗ p (DOWN[ n ] t)   = DOWN[ n ] (mapᵗ p t)
mapᵗ p (BOOM[ n ] t)   = BOOM[ n ] (mapᵗ p t)
mapᵗ p (! t)           = ! mapᵗ p t
