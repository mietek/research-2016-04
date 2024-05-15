module Examples.Negation where

open import AltArtemov


-- Some examples of reasoning with negation and principle of explosion.

X0 : ∀ {Γ} → Γ ⊢ ⊥ ⊃ ⊥
X0 = lam v0

X1 : ∀ {A Γ} → Γ ⊢ ⊥ ⊃ A
X1 = lam (boom v0)

X1² : ∀ {A Γ} → Γ ⊢ LAM (BOOM V0) ∶ (⊥ ⊃ A)
X1² = nec X1

X2 : ∀ {x A Γ} → Γ ⊢ x ∶ ⊥ ⊃ BOOM x ∶ A
X2 = lam (boom² v0)

X3 : ∀ {A Γ} → Γ ⊢ ¬ A ⊃ A ⊃ ⊥
X3 = lam (lam (app v1 v0))

X4 : ∀ {x y A Γ} → Γ ⊢ x ∶ ¬ A ⊃ y ∶ A ⊃ APP x y ∶ ⊥
X4 = lam (lam (app² v1 v0))

X5 : ∀ {x y A Γ} → Γ ⊢ x ∶ ¬ A ⊃ y ∶ A ⊃ quo (APP x y) ∶ APP x y ∶ ⊥
X5 = lam (lam (up (app² v1 v0)))


--meta : ∀ {A B Γ} → Γ ⊢ (LAM V0 ∶ (A ⊃ B ⊃ A)) ⊃ ⊥
--meta = lam {!!}
