module Try3.S4.Examples where

open import Try3.S4.Core public


I : ∀ {Γ Δ A} → Tm Γ Δ (A ⊃ A)
I = lam v₀

K : ∀ {Γ Δ A B} → Tm Γ Δ (A ⊃ B ⊃ A)
K = lam (lam v₁)

S : ∀ {Γ Δ A B C} → Tm Γ Δ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
S = lam (lam (lam (app (app v₂ v₀) (app v₁ v₀))))


D : ∀ {Γ Δ A B} → Tm Γ Δ (□ (A ⊃ B) ⊃ □ A ⊃ □ B)
D = lam (lam (down v₁ (down v₀ (up (app *v₁ *v₀)))))

T : ∀ {Γ Δ A} → Tm Γ Δ (□ A ⊃ A)
T = lam (down v₀ *v₀)

#4 : ∀ {Γ Δ A} → Tm Γ Δ (□ A ⊃ □ □ A)
#4 = lam (down v₀ (up (up *v₀)))


E1 : ∀ {Γ Δ A} → Tm Γ Δ (□ (□ A ⊃ A))
E1 = up T

E2 : ∀ {Γ Δ A} → Tm Γ Δ (□ (□ A ⊃ □ □ A))
E2 = up #4

E3 : ∀ {Γ Δ A B} → Tm Γ Δ (□ □ (A ⊃ B ⊃ A ∧ B))
E3 = up (up (lam (lam (pair v₁ v₀))))

E4 : ∀ {Γ Δ A B} → Tm Γ Δ (□ (□ A ⊃ □ B ⊃ □ □ (A ∧ B)))
E4 = up (lam (lam (down v₁ (down v₀ (up (up (pair *v₁ *v₀)))))))
