module Try2.AltArtemov.Term.Representation.Vector.Core where

open import Data.Nat using (ℕ ; zero ; suc)

open import Try2.AltArtemov.Context.Representation
open import Try2.AltArtemov.Term.Representation.Core
open import Try2.AltArtemov.Variable.Representation


infixr 5 _∷_

data Vec (g : CxR) : ℕ → Set where
  []  : Vec g zero
  _∷_ : ∀ {n} → g ⊢◌ → Vec g n → Vec g (suc n)
