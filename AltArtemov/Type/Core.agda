module AltArtemov.Type.Core where

open import AltArtemov.Context.Representation
open import AltArtemov.Term.Representation


infixr 10 _⊃_
infixr 15 _∶_
infixl 20 _∧_

data Ty (g : CxR) : Set where
  ★   : Ty g
  _∶_ : g ⊢◌ → Ty g → Ty g
  _⊃_ : Ty g → Ty g → Ty g
  _∧_ : Ty g → Ty g → Ty g
  ⊥  : Ty g


⊤ : ∀ {g} → Ty g
⊤ = ⊥ ⊃ ⊥

¬_ : ∀ {g} → Ty g → Ty g
¬ A = A ⊃ ⊥

_⫗_ : ∀ {g} → Ty g → Ty g → Ty g
A ⫗ B = (A ⊃ B) ∧ (B ⊃ A)
