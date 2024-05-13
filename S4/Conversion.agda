module Try3.S4.Conversion where

open import Try3.S4.Substitution public


data _⇔_ {Γ Δ} : ∀ {A} → Tm Γ Δ A → Tm Γ Δ A → Set where
  ⇔refl      : ∀ {A} {t : Tm Γ Δ A} →
                t ⇔ t
  ⇔sym       : ∀ {A} {t t′ : Tm Γ Δ A} →
                t ⇔ t′ → t′ ⇔ t
  ⇔trans     : ∀ {A} {t t′ t″ : Tm Γ Δ A} →
                t ⇔ t′ → t′ ⇔ t″ → t ⇔ t″
  ⇔cong-lam  : ∀ {A B} {t t′ : Tm (Γ , A) Δ B} →
                t ⇔ t′ → lam t ⇔ lam t′
  ⇔cong-app  : ∀ {A B} {t₁ t₁′ : Tm Γ Δ (A ⊃ B)} {t₂ t₂′ : Tm Γ Δ A} →
                t₁ ⇔ t₁′ → t₂ ⇔ t₂′ → app t₁ t₂ ⇔ app t₁′ t₂′
  ⇔cong-down : ∀ {A C} {t₁ t₁′ : Tm Γ Δ (□ A)} {t₂ t₂′ : Tm Γ (Δ , A) C} →
                t₁ ⇔ t₁′ → t₂ ⇔ t₂′ → down t₁ t₂ ⇔ down t₁′ t₂′
  ⇔cong-pair : ∀ {A B} {t₁ t₁′ : Tm Γ Δ A} {t₂ t₂′ : Tm Γ Δ B} →
                t₁ ⇔ t₁′ → t₂ ⇔ t₂′ → pair t₁ t₂ ⇔ pair t₁′ t₂′
  ⇔cong-fst  : ∀ {A B} {t t′ : Tm Γ Δ (A ∧ B)} →
                t ⇔ t′ → fst t ⇔ fst t′
  ⇔cong-snd  : ∀ {A B} {t t′ : Tm Γ Δ (A ∧ B)} →
                t ⇔ t′ → snd t ⇔ snd t′
  ⇔beta      : ∀ {A B} {t₁ : Tm (Γ , A) Δ B} {t₂ : Tm Γ Δ A} →
                app (lam t₁) t₂ ⇔ subst-tm⁻ t₁ top t₂
  ⇔eta       : ∀ {A B} {t : Tm Γ Δ (A ⊃ B)} →
                lam (app (wk-tm⁻ top t) v₀) ⇔ t
