module Try3.LPWithEquality.Core where

open import Try3.Common.Variable public


mutual
  data Ty : Set where
    ⊥  : Ty
    _∴_ : ∀ {Ξ A} → Tm ∅ Ξ A → Ty → Ty
    _⊃_ : Ty → Ty → Ty
    _∧_ : Ty → Ty → Ty
    _≑_ : Ty → Ty → Ty

  data Tm (Γ Δ : Cx Ty) : Ty → Set where
    var   : ∀ {A} → Var Ty Γ A → Tm Γ Δ A
    lam   : ∀ {A B} → Tm (Γ , A) Δ B → Tm Γ Δ (A ⊃ B)
    app   : ∀ {A B} → Tm Γ Δ (A ⊃ B) → Tm Γ Δ A → Tm Γ Δ B
    *var  : ∀ {A} → Var Ty Δ A → Tm Γ Δ A
    up    : ∀ {A} → (t : Tm ∅ Δ A) → Tm Γ Δ (t ∴ A)
    down  : ∀ {Ξ A C} {t : Tm ∅ Ξ A} → Tm Γ Δ (t ∴ A) → Tm Γ (Δ , A) C → Tm Γ Δ C
    pair  : ∀ {A B} → Tm Γ Δ A → Tm Γ Δ B → Tm Γ Δ (A ∧ B)
    fst   : ∀ {A B} → Tm Γ Δ (A ∧ B) → Tm Γ Δ A
    snd   : ∀ {A B} → Tm Γ Δ (A ∧ B) → Tm Γ Δ B
    ≑I    : ∀ {A B} → Tm (Γ , A) Δ B → Tm (Γ , B) Δ A → Tm Γ Δ (A ≑ B)
    ≑E₁   : ∀ {A B C} → Tm Γ Δ (A ≑ B) → Tm Γ Δ A → Tm (Γ , B) Δ C → Tm Γ Δ C
    ≑E₂   : ∀ {A B C} → Tm Γ Δ (A ≑ B) → Tm Γ Δ B → Tm (Γ , A) Δ C → Tm Γ Δ C


¬_ : Ty → Ty
¬ A = A ⊃ ⊥


infix  4 _≑_
infixr 5 _⊃_
infixl 7 _∧_
infixl 8 app
infixr 9 _∴_

syntax lam t      = ƛ t
syntax app t₁ t₂  = t₁ ∙ t₂
syntax up t       = ⇑ t
syntax down t₁ t₂ = ⇓⟨ t₁ ∣ t₂ ⟩
syntax pair t₁ t₂ = p⟨ t₁ , t₂ ⟩
syntax fst t      = π₁ t
syntax snd t      = π₂ t


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


[vᵢ]_ : Ty → Ty
[vᵢ] A = _∴_ {Ξ = (∅ , A)} *v₀ A
