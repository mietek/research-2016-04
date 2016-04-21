module Examples.Negation where

open import AltArtemov


-- Some examples of reasoning with negation and principle of explosion.

X0 : ⊩ ⊥ ⊃ ⊥
X0 = lam v0

X1 : ∀ {A} → ⊩ ⊥ ⊃ A
X1 = lam (boom v0)

X1² : ∀ {A} → ⊩ LAM (BOOM V0) ∶ (⊥ ⊃ A)
X1² = nec X1

X2 : ∀ {x A} → ⊩ x ∶ ⊥ ⊃ BOOM x ∶ A
X2 = lam (boom² v0)

X3 : ∀ {A} → ⊩ ¬ A ⊃ A ⊃ ⊥
X3 = lam (lam (app v1 v0))

X4 : ∀ {x y A} → ⊩ x ∶ ¬ A ⊃ y ∶ A ⊃ APP x y ∶ ⊥
X4 = lam (lam (app² v1 v0))

X5 : ∀ {x y A} → ⊩ x ∶ ¬ A ⊃ y ∶ A ⊃ quo (APP x y) ∶ APP x y ∶ ⊥
X5 = lam (lam (up (app² v1 v0)))


--meta : ∀ {A B} → ⊩ (LAM V0 ∶ (A ⊃ B ⊃ A)) ⊃ ⊥
--meta = lam {!!}
