module S4.Type.Core where


infixr 2 _⊃_

data Ty : Set where
  -- Falsehood.
  ⊥ : Ty

  -- Implication.
  _⊃_ : (A B : Ty) → Ty

  -- Modality.
  □_ : (A : Ty) → Ty
