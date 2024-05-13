module Try3.S4.Substitution where

open import Try3.S4.Weakening public


subst-var⁻ : ∀ {Γ Δ A B} → (v : Var Ty Γ B) (x : Var Ty Γ A) (s : Tm (Γ - x) Δ A) →
             Tm (Γ - x) Δ B
subst-var⁻ v              x  s with eq-var⁻ x v
subst-var⁻ v              .v s | same      = s
subst-var⁻ .(wk-var⁻ v x) v  s | diff .v x = var x

*subst-var⁻ : ∀ {Γ Δ A B} → (v : Var Ty Δ B) (x : Var Ty Δ A) (s : Tm ∅ (Δ - x) A) →
              Tm Γ (Δ - x) B
*subst-var⁻ v              x  s with eq-var⁻ x v
*subst-var⁻ v              .v s | same      = down (up s) *v₀  -- WHOA!
*subst-var⁻ .(wk-var⁻ v x) v  s | diff .v x = *var x


subst-tm⁻ : ∀ {Γ Δ A B} → (t : Tm Γ Δ B) (x : Var Ty Γ A) (s : Tm (Γ - x) Δ A) →
            Tm (Γ - x) Δ B
subst-tm⁻ (var v)      x s = subst-var⁻ v x s
subst-tm⁻ (lam t)      x s = lam (subst-tm⁻ t (pop x) (wk-tm⁻ top s))
subst-tm⁻ (app t₁ t₂)  x s = app (subst-tm⁻ t₁ x s) (subst-tm⁻ t₂ x s)
subst-tm⁻ (*var v)     x s = *var v
subst-tm⁻ (up t)       x s = up t
subst-tm⁻ (down t₁ t₂) x s = down (subst-tm⁻ t₁ x s) (subst-tm⁻ t₂ x (*wk-tm⁻ top s))
subst-tm⁻ (pair t₁ t₂) x s = pair (subst-tm⁻ t₁ x s) (subst-tm⁻ t₂ x s)
subst-tm⁻ (fst t)      x s = fst (subst-tm⁻ t x s)
subst-tm⁻ (snd t)      x s = snd (subst-tm⁻ t x s)

*subst-tm⁻ : ∀ {Γ Δ A B} → (t : Tm Γ Δ B) (x : Var Ty Δ A) (s : Tm ∅ (Δ - x) A) →
             Tm Γ (Δ - x) B
*subst-tm⁻ (var v)      x s = var v
*subst-tm⁻ (lam t)      x s = lam (*subst-tm⁻ t x s)
*subst-tm⁻ (app t₁ t₂)  x s = app (*subst-tm⁻ t₁ x s) (*subst-tm⁻ t₂ x s)
*subst-tm⁻ (*var v)     x s = *subst-var⁻ v x s
*subst-tm⁻ (up t)       x s = up (*subst-tm⁻ t x s)
*subst-tm⁻ (down t₁ t₂) x s = down (*subst-tm⁻ t₁ x s) (*subst-tm⁻ t₂ (pop x) (*wk-tm⁻ top s))
*subst-tm⁻ (pair t₁ t₂) x s = pair (*subst-tm⁻ t₁ x s) (*subst-tm⁻ t₂ x s)
*subst-tm⁻ (fst t)      x s = fst (*subst-tm⁻ t x s)
*subst-tm⁻ (snd t)      x s = snd (*subst-tm⁻ t x s)
