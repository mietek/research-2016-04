{-# OPTIONS --allow-unsolved-metas #-}

module LP.Renaming where

open import LP.Core public


ren-tm : ∀ {Γ Γ′ Δ A} → Γ′ ≥ Γ → Tm Γ Δ A → Tm Γ′ Δ A
ren-tm η (var x)      = var (ren-var η x)
ren-tm η (lam t)      = lam (ren-tm (lift η) t)
ren-tm η (app t₁ t₂)  = app (ren-tm η t₁) (ren-tm η t₂)
ren-tm η (*var x)     = *var x
ren-tm η (up t)       = up t
ren-tm η (down t₁ t₂) = down (ren-tm η t₁) (ren-tm η t₂)
ren-tm η (pair t₁ t₂) = pair (ren-tm η t₁) (ren-tm η t₂)
ren-tm η (fst t)      = fst (ren-tm η t)
ren-tm η (snd t)      = snd (ren-tm η t)

wk-tm : ∀ {Γ Δ A B} → Tm Γ Δ A → Tm (Γ , B) Δ A
wk-tm = ren-tm wk

wk₀-tm : ∀ {Γ Δ A} → Tm ∅ Δ A → Tm Γ Δ A
wk₀-tm = ren-tm to


ren-tm-id : ∀ {Γ Δ A} → (t : Tm Γ Δ A) → ren-tm id t ≡ t
ren-tm-id (var x)      = cong var (ren-var-id x)
ren-tm-id (lam t)      = cong lam (ren-tm-id t)
ren-tm-id (app t₁ t₂)  = cong₂ app (ren-tm-id t₁) (ren-tm-id t₂)
ren-tm-id (*var x)     = refl
ren-tm-id (up t)       = refl
ren-tm-id (down t₁ t₂) = cong₂ down (ren-tm-id t₁) (ren-tm-id t₂)
ren-tm-id (pair t₁ t₂) = cong₂ pair (ren-tm-id t₁) (ren-tm-id t₂)
ren-tm-id (fst t)      = cong fst (ren-tm-id t)
ren-tm-id (snd t)      = cong snd (ren-tm-id t)

ren-tm-• : ∀ {Γ Γ′ Γ″ Δ A} → (η′ : Γ″ ≥ Γ′) (η : Γ′ ≥ Γ) (t : Tm Γ Δ A) →
           ren-tm η′ (ren-tm η t) ≡ ren-tm (η′ • η) t
ren-tm-• η′ η (var x)      = cong var (ren-var-• η′ η x)
ren-tm-• η′ η (lam t)      = cong lam (ren-tm-• (lift η′) (lift η) t)
ren-tm-• η′ η (app t₁ t₂)  = cong₂ app (ren-tm-• η′ η t₁) (ren-tm-• η′ η t₂)
ren-tm-• η′ η (*var x)     = refl
ren-tm-• η′ η (up t)       = refl
ren-tm-• η′ η (down t₁ t₂) = cong₂ down (ren-tm-• η′ η t₁) (ren-tm-• η′ η t₂)
ren-tm-• η′ η (pair t₁ t₂) = cong₂ pair (ren-tm-• η′ η t₁) (ren-tm-• η′ η t₂)
ren-tm-• η′ η (fst t)      = cong fst (ren-tm-• η′ η t)
ren-tm-• η′ η (snd t)      = cong snd (ren-tm-• η′ η t)


mutual
  *ren-ty : ∀ {Δ Δ′ : Cx Ty} → Δ′ ≥ Δ → Ty → Ty
  *ren-ty η ⊥      = ⊥
  *ren-ty η (t ∴ A) = {!*ren-tm η t ∴ *ren-ty η A!}
  *ren-ty η (A ⊃ B) = A ⊃ *ren-ty η B
  *ren-ty η (A ∧ B) = *ren-ty η A ∧ *ren-ty η B

  *ren-tm : ∀ {Γ Δ Δ′ A} → Δ′ ≥ Δ → Tm Γ Δ A → Tm Γ Δ′ A
  *ren-tm η (var x)      = var x
  *ren-tm η (lam t)      = lam (*ren-tm η t)
  *ren-tm η (app t₁ t₂)  = app (*ren-tm η t₁) (*ren-tm η t₂)
  *ren-tm η (*var x)     = *var (ren-var η x)
  *ren-tm η (up t)       = {!up (*ren-tm η t)!}
  *ren-tm η (down t₁ t₂) = down (*ren-tm η t₁) (*ren-tm (lift η) t₂)
  *ren-tm η (pair t₁ t₂) = pair (*ren-tm η t₁) (*ren-tm η t₂)
  *ren-tm η (fst t)      = fst (*ren-tm η t)
  *ren-tm η (snd t)      = snd (*ren-tm η t)


subst-tm : ∀ {Γ Γ′ Δ A B} → Γ′ ≥ Γ → Var Ty Γ′ A → Tm Γ Δ A → Tm Γ′ Δ B → Tm Γ′ Δ B
subst-tm η x s (var y)      = {!!}
subst-tm η x s (lam t)      = {!!}
subst-tm η x s (app t₁ t₂)  = app (subst-tm η x s t₁) (subst-tm η x s t₂)
subst-tm η x s (*var y)     = *var y
subst-tm η x s (up t)       = up t
subst-tm η x s (down t₁ t₂) = down (subst-tm η x s t₁) {!!}
subst-tm η x s (pair t₁ t₂) = pair (subst-tm η x s t₁) (subst-tm η x s t₂)
subst-tm η x s (fst t)      = fst (subst-tm η x s t)
subst-tm η x s (snd t)      = snd (subst-tm η x s t)
