module Try3.LP.DenotationalSemantics where

open import Try3.LP.Core public


mutual
  ⟦_⟧ᴬ : Ty → Set
  ⟦ ⊥ ⟧ᴬ    = Empty
  ⟦ A ⊃ B ⟧ᴬ = ⟦ A ⟧ᴬ → ⟦ B ⟧ᴬ
  ⟦ A ∧ B ⟧ᴬ = ⟦ A ⟧ᴬ × ⟦ B ⟧ᴬ
  ⟦ t ∴ A ⟧ᴬ = ∃ (λ t′ → t ≡ t′) × ⟦ A ⟧ᴬ

  ⟦_⟧ᴳ : Cx Ty → Set
  ⟦ ∅ ⟧ᴳ       = Unit
  ⟦ (Γ , A) ⟧ᴳ = ⟦ Γ ⟧ᴳ × ⟦ A ⟧ᴬ

  ⟦_⟧ˣ : ∀ {Γ A} → Var Ty Γ A → ⟦ Γ ⟧ᴳ → ⟦ A ⟧ᴬ
  ⟦ top ⟧ˣ   (γ , a) = a
  ⟦ pop x ⟧ˣ (γ , b) = ⟦ x ⟧ˣ γ

  ⟦_⟧ : ∀ {Γ Δ A} → Tm Γ Δ A → ⟦ Γ ⟧ᴳ → ⟦ Δ ⟧ᴳ → ⟦ A ⟧ᴬ
  ⟦ var x ⟧      γ δ = ⟦ x ⟧ˣ γ
  ⟦ lam t ⟧      γ δ = λ a → ⟦ t ⟧ (γ , a) δ
  ⟦ app t₁ t₂ ⟧  γ δ = (⟦ t₁ ⟧ γ δ) (⟦ t₂ ⟧ γ δ)
  ⟦ *var x ⟧     γ δ = ⟦ x ⟧ˣ δ
  ⟦ up t ⟧       γ δ = ((t , refl) , ⟦ t ⟧ unit δ)
  ⟦ down t₁ t₂ ⟧ γ δ with ⟦ t₁ ⟧ γ δ
  …                 | ((t , refl) , *a) = ⟦ t₂ ⟧ γ (δ , *a)
  ⟦ pair t₁ t₂ ⟧ γ δ = (⟦ t₁ ⟧ γ δ , ⟦ t₂ ⟧ γ δ)
  ⟦ fst t ⟧      γ δ = proj₁ (⟦ t ⟧ γ δ)
  ⟦ snd t ⟧      γ δ = proj₂ (⟦ t ⟧ γ δ)
