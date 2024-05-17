module Try1.AltArtemov.Type.Core where

open import Try1.AltArtemov.Term


infixr 2 _⊃_
infixr 3 _≑_ _≠_
infixr 5 _∶_

data Ty : Set where
  -- Falsehood.
  ⊥ : Ty

  -- Implication.
  _⊃_ : (A B : Ty) → Ty

  -- Conjunction.
  _∧_ : (A B : Ty) → Ty

  -- Type assertion.
  _∶_ : (t : Tm) → (A : Ty) → Ty

  -- Type equality.
  _≑_ : (A B : Ty) → Ty


-- Negation.
¬_ : Ty → Ty
¬ A = A ⊃ ⊥

-- Negation of type equality.
_≠_ : (A B : Ty) → Ty
A ≠ B = ¬ (A ≑ B)
