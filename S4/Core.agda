module S4.Core where

open import Common.Variable public


data Ty : Set where
  ⊥  : Ty
  □_  : Ty → Ty
  _⊃_ : Ty → Ty → Ty
  _∧_ : Ty → Ty → Ty

data Tm (Γ Δ : Cx Ty) : Ty → Set where
  var  : ∀ {A} → Var Ty Γ A → Tm Γ Δ A
  lam  : ∀ {A B} → Tm (Γ , A) Δ B → Tm Γ Δ (A ⊃ B)
  app  : ∀ {A B} → Tm Γ Δ (A ⊃ B) → Tm Γ Δ A → Tm Γ Δ B
  *var : ∀ {A} → Var Ty Δ A → Tm Γ Δ A
  up   : ∀ {A} → Tm ∅ Δ A → Tm Γ Δ (□ A)
  down : ∀ {A C} → Tm Γ Δ (□ A) → Tm Γ (Δ , A) C → Tm Γ Δ C
  pair : ∀ {A B} → Tm Γ Δ A → Tm Γ Δ B → Tm Γ Δ (A ∧ B)
  fst  : ∀ {A B} → Tm Γ Δ (A ∧ B) → Tm Γ Δ A
  snd  : ∀ {A B} → Tm Γ Δ (A ∧ B) → Tm Γ Δ B


infixr 5 _⊃_
infixl 7 _∧_


v₀ : ∀ {Γ Δ A} → Tm (Γ , A) Δ A
v₀ = var x₀

v₁ : ∀ {Γ Δ A B} → Tm ((Γ , A) , B) Δ A
v₁ = var x₁

v₂ : ∀ {Γ Δ A B C} → Tm (((Γ , A) , B) , C) Δ A
v₂ = var x₂


*v₀ : ∀ {Γ Δ A} → Tm Γ (Δ , A) A
*v₀ = *var x₀

*v₁ : ∀ {Γ Δ A B} → Tm Γ ((Δ , A) , B) A
*v₁ = *var x₁

*v₂ : ∀ {Γ Δ A B C} → Tm Γ (((Δ , A) , B) , C) A
*v₂ = *var x₂
