module AltArtemov.Type.Core where

open import AltArtemov.Term


infixr 2 _⊃_
infixr 5 _∶_

data Ty : Set where
  -- Falsehood.
  ⊥ : Ty

  -- Implication.
  _⊃_ : (A B : Ty) → Ty

  -- Type assertion.
  _∶_ : (t : Tm) → (A : Ty) → Ty


-- Negation.
¬_ : Ty → Ty
¬ A = A ⊃ ⊥
