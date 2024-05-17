module Try1.S4.Derivation.Core where

open import Try1.S4.Context
open import Try1.S4.Type


infixr 0 _∙_⊢_

data _∙_⊢_ (Δ Γ : Cx) : ∀ (A : Ty) → Set where
  -- Variable reference.
  var : ∀ {A}
      → (i : Γ ∋ A)
      → Δ ∙ Γ ⊢ A

  -- Lambda abstraction. (⊃I)
  lam : ∀ {A B}
      → (d : Δ ∙ Γ , A ⊢ B)
      → Δ ∙ Γ ⊢ A ⊃ B

  -- Function application. (⊃E)
  app : ∀ {A B}
      → (d : Δ ∙ Γ ⊢ A ⊃ B)    → (c : Δ ∙ Γ ⊢ A)
      → Δ ∙ Γ ⊢ B

  -- Product. (∧I)
  pair : ∀ {A B}
      → (d : Δ ∙ Γ ⊢ A)    → (c : Δ ∙ Γ ⊢ B)
      → Δ ∙ Γ ⊢ A ∧ B

  -- First projection. (∧E₁)
  fst : ∀ {A B}
      → (d : Δ ∙ Γ ⊢ A ∧ B)
      → Δ ∙ Γ ⊢ A

  -- Second projection. (∧E₂)
  snd : ∀ {A B}
      → (d : Δ ∙ Γ ⊢ A ∧ B)
      → Δ ∙ Γ ⊢ B

  -- Modal variable reference.
  var* : ∀ {A}
      → (i : Δ ∋ A)
      → Δ ∙ Γ ⊢ A

  -- Modality introduction. (□I)
  box : ∀ {A}
      → (d : Δ ∙ ∅ ⊢ A)
      → Δ ∙ Γ ⊢ □ A

  -- Modality elimination. (□E)
  unbox : ∀ {A C}
      → (d : Δ ∙ Γ ⊢ □ A)    → (c : Δ , A ∙ Γ ⊢ C)
      → Δ ∙ Γ ⊢ C


ty : ∀ {Δ Γ A} (d : Δ ∙ Γ ⊢ A) → Ty
ty {A = A} d = A
