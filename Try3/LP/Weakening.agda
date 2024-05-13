{-# OPTIONS --allow-unsolved-metas #-}

module Try3.LP.Weakening where

open import Try3.LP.Core public


wk-tm⁻ : ∀ {Γ Δ A B} → (x : Var Ty Γ A) → Tm (Γ - x) Δ B → Tm Γ Δ B
wk-tm⁻ x (var v)      = var (wk-var⁻ x v)
wk-tm⁻ x (lam t)      = lam (wk-tm⁻ (pop x) t)
wk-tm⁻ x (app t₁ t₂)  = app (wk-tm⁻ x t₁) (wk-tm⁻ x t₂)
wk-tm⁻ x (*var v)     = *var v
wk-tm⁻ x (up t)       = up t
wk-tm⁻ x (down t₁ t₂) = down (wk-tm⁻ x t₁) (wk-tm⁻ x t₂)
wk-tm⁻ x (pair t₁ t₂) = pair (wk-tm⁻ x t₁) (wk-tm⁻ x t₂)
wk-tm⁻ x (fst t)      = fst (wk-tm⁻ x t)
wk-tm⁻ x (snd t)      = snd (wk-tm⁻ x t)

*wk-tm⁻ : ∀ {Γ Δ A B} → (x : Var Ty Δ A) → Tm Γ (Δ - x) B → Tm Γ Δ B
*wk-tm⁻ x (var v)      = var v
*wk-tm⁻ x (lam t)      = lam (*wk-tm⁻ x t)
*wk-tm⁻ x (app t₁ t₂)  = app (*wk-tm⁻ x t₁) (*wk-tm⁻ x t₂)
*wk-tm⁻ x (*var v)     = *var (wk-var⁻ x v)
*wk-tm⁻ x (up t)       = {!up ?!} -- up (*wk-tm⁻ x t)
*wk-tm⁻ x (down t₁ t₂) = down (*wk-tm⁻ x t₁) (*wk-tm⁻ (pop x) t₂)
*wk-tm⁻ x (pair t₁ t₂) = pair (*wk-tm⁻ x t₁) (*wk-tm⁻ x t₂)
*wk-tm⁻ x (fst t)      = fst (*wk-tm⁻ x t)
*wk-tm⁻ x (snd t)      = snd (*wk-tm⁻ x t)
