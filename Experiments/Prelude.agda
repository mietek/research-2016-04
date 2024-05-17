module Try1.Experiments.Prelude where

open import Try1.AltArtemov


-- Function.

id : ∀ {A Γ} → Γ ⊢ A ⊃ A
id = lam v0

const : ∀ {A B Γ} → Γ ⊢ A ⊃ B ⊃ A
const = lam (lam v1)

ap : ∀ {A B C Γ} → Γ ⊢ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
ap = lam (lam (lam (app (app v2 v0) (app v1 v0))))

comp : ∀ {A B C Γ} → Γ ⊢ (B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
comp = lam (lam (lam (app v2 (app v1 v0))))

flip : ∀ {A B C Γ} → Γ ⊢ (A ⊃ B ⊃ C) ⊃ B ⊃ A ⊃ C
flip = lam (lam (lam (app (app v2 v0) v1)))

of : ∀ {A B C Γ} → Γ ⊢ A ⊃ (A ⊃ B ⊃ C) ⊃ B ⊃ C
of = lam (lam (lam (app (app v1 v2) v0)))

on : ∀ {A B C Γ} → Γ ⊢ (B ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ A ⊃ C
on = lam (lam (lam (lam (app (app v3 (app v2 v1)) (app v2 v0)))))


-- Negation.

contradiction : ∀ {A B Γ} → Γ ⊢ A ⊃ ¬ A ⊃ B
contradiction = lam (lam (boom (app v0 v1)))

contraposition : ∀ {A B Γ} → Γ ⊢ (A ⊃ B) ⊃ ¬ B ⊃ ¬ A
contraposition = lam (lam (lam (app (app contradiction (app v2 v0)) v1)))

¬-flip : ∀ {A B Γ} → Γ ⊢ (A ⊃ ¬ B) ⊃ B ⊃ ¬ A
¬-flip = flip

¬¬-map : ∀ {A B Γ} → Γ ⊢ (A ⊃ B) ⊃ ¬ ¬ A ⊃ ¬ ¬ B
¬¬-map {A} {B} = lam (app contraposition (app contraposition v0))
