module Experiments.Prelude where

open import AltArtemov


-- Function.

id : ∀ {A} → ⊩ A ⊃ A
id = lam v0

const : ∀ {A B} → ⊩ A ⊃ B ⊃ A
const = lam (lam v1)

ap : ∀ {A B C} → ⊩ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
ap = lam (lam (lam (app (app v2 v0) (app v1 v0))))

comp : ∀ {A B C} → ⊩ (B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
comp = lam (lam (lam (app v2 (app v1 v0))))

flip : ∀ {A B C} → ⊩ (A ⊃ B ⊃ C) ⊃ B ⊃ A ⊃ C
flip = lam (lam (lam (app (app v2 v0) v1)))

of : ∀ {A B C} → ⊩ A ⊃ (A ⊃ B ⊃ C) ⊃ B ⊃ C
of = lam (lam (lam (app (app v1 v2) v0)))

on : ∀ {A B C} → ⊩ (B ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ A ⊃ C
on = lam (lam (lam (lam (app (app v3 (app v2 v1)) (app v2 v0)))))


-- Negation.

contradiction : ∀ {A B} → ⊩ A ⊃ ¬ A ⊃ B
contradiction = lam (lam (boom (app v0 v1)))

contraposition : ∀ {A B} → ⊩ (A ⊃ B) ⊃ ¬ B ⊃ ¬ A
contraposition = lam (lam (lam (app (app contradiction (app v2 v0)) v1)))

¬-flip : ∀ {A B} → ⊩ (A ⊃ ¬ B) ⊃ B ⊃ ¬ A
¬-flip = flip

¬¬-map : ∀ {A B} → ⊩ (A ⊃ B) ⊃ ¬ ¬ A ⊃ ¬ ¬ B
¬¬-map {A} {B} = lam (app contraposition (app contraposition v0))
