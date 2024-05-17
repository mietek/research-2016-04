module Try1.S4.Type where


infixr 2 _⊃_

data Ty : Set where
  -- Falsehood.
  ⊥ : Ty

  -- Implication.
  _⊃_ : (A B : Ty) → Ty

  -- Conjunction.
  _∧_ : (A B : Ty) → Ty

  -- Modality.
  □_ : (A : Ty) → Ty
