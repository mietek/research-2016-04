module LP.AltArtemovNotation where

open import LP.Core public


I : ∀ {Γ Δ A} → Tm Γ Δ (A ⊃ A)
I = ƛ v₀

K : ∀ {Γ Δ A B} → Tm Γ Δ (A ⊃ B ⊃ A)
K = ƛ ƛ v₁

S : ∀ {Γ Δ A B C} → Tm Γ Δ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
S = ƛ ƛ ƛ ((v₂ ∙ v₀) ∙ (v₁ ∙ v₀))


D : ∀ {Γ Δ A B} → Tm Γ Δ ([vᵢ] (A ⊃ B) ⊃ [vᵢ] A ⊃ (*v₁ ∙ *v₀) ∴ B)
D = ƛ ƛ ⇓⟨ v₁ ∣ ⇓⟨ v₀ ∣ ⇑ (*v₁ ∙ *v₀) ⟩ ⟩

T : ∀ {Γ Δ A} → Tm Γ Δ ([vᵢ] A ⊃ A)
T = ƛ ⇓⟨ v₀ ∣ *v₀ ⟩

#4 : ∀ {Γ Δ A} → Tm Γ Δ ([vᵢ] A ⊃ ⇑ *v₀ ∴ *v₀ ∴ A)
#4 = ƛ ⇓⟨ v₀ ∣ ⇑ ⇑ *v₀ ⟩


E1 : ∀ {Γ Δ A} → Tm Γ Δ (T ∴ ([vᵢ] A ⊃ A))
E1 = ⇑ T

E2 : ∀ {Γ Δ A} → Tm Γ Δ (#4 ∴ ([vᵢ] A ⊃ ⇑ *v₀ ∴ *v₀ ∴ A))
E2 = ⇑ #4

E3 : ∀ {Γ Δ A B} →
     Tm Γ Δ (⇑ ƛ ƛ p⟨ v₁ , v₀ ⟩ ∴ ƛ ƛ p⟨ v₁ , v₀ ⟩ ∴ (A ⊃ B ⊃ A ∧ B))
E3 = ⇑ ⇑ ƛ ƛ p⟨ v₁ , v₀ ⟩

E4 : ∀ {Γ Δ A B} →
     Tm Γ Δ (ƛ ƛ ⇓⟨ v₁ ∣ ⇓⟨ v₀ ∣ ⇑ ⇑ p⟨ *v₁ , *v₀ ⟩ ⟩ ⟩ ∴
            ([vᵢ] A ⊃ [vᵢ] B ⊃ ⇑ p⟨ *v₁ , *v₀ ⟩ ∴ p⟨ *v₁ , *v₀ ⟩ ∴ (A ∧ B)))
E4 = ⇑ ƛ ƛ ⇓⟨ v₁ ∣ ⇓⟨ v₀ ∣ ⇑ ⇑ p⟨ *v₁ , *v₀ ⟩ ⟩ ⟩
