module AltArtemov.Type.Core where

open import AltArtemov.Term
import S4


infixr 2 _⊃_
infixr 5 _∶_

data Ty : Set where
  -- Falsehood.
  ⊥ : Ty

  -- Implication.
  _⊃_ : (A B : Ty) → Ty

  -- Type assertion.
  _∶_ : (t : Tm) → (A : Ty) → Ty


°[_] : ∀ A → S4.Ty
°[ ⊥ ]    = S4.⊥
°[ A ⊃ B ] = °[ A ] S4.⊃ °[ B ]
°[ t ∶ A ] = S4.□ °[ A ]
