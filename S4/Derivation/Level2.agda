module S4.Derivation.Level2 where

open import S4.Context
open import S4.Term
open import S4.Type


infixr 0 _∙_⊢_∶_

data _∙_⊢_∶_ (Δ Γ : Cx) : ∀ (t : Tm) (A : Ty) → Set where
  -- Variable reference.
  VAR² : ∀ {A}
      → (i : Γ ∋ A)
      → Δ ∙ Γ ⊢ var (ix i) ∶ A

  -- Lambda abstraction.
  LAM² : ∀ {t A B}
      → (d : Δ ∙ Γ , A ⊢ t ∶ B)
      → Δ ∙ Γ ⊢ lam t ∶ (A ⊃ B)

  -- Function application.
  APP² : ∀ {t s A B}
      → (d : Δ ∙ Γ ⊢ t ∶ (A ⊃ B))    → (c : Δ ∙ Γ ⊢ s ∶ A)
      → Δ ∙ Γ ⊢ app t s ∶ B

  -- Modal variable reference.
  VAR*² : ∀ {A}
      → (i : Δ ∋ A)
      → Δ ∙ Γ ⊢ var* (ix i) ∶ A

  -- Modality introduction.
  BOX² : ∀ {t A}
      → (d : Δ ∙ ∅ ⊢ t ∶ A)
      → Δ ∙ Γ ⊢ box t ∶ □ A

  -- Modality elimination.
  UNBOX² : ∀ {t s A C}
      → (d : Δ ∙ Γ ⊢ t ∶ □ A)    → (c : Δ , A ∙ Γ ⊢ s ∶ C)
      → Δ ∙ Γ ⊢ unbox t s ∶ C
