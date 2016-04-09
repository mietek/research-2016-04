module README where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import AltArtemov


module Level0 where
  I : ∀ {A : Set}
      → A → A
  I x = x

  K : ∀ {A B : Set}
      → A → B → A
  K x y = x

  S : ∀ {A B C : Set}
      → (A → B → C) → (A → B) → A → C
  S f g x = (f x) (g x)


module Level1 where
  I : ∀ {A}
      → ⊩ A ⊃ A
  I = LAM V0

  K : ∀ {A B}
      → ⊩ A ⊃ B ⊃ A
  K = LAM LAM V1

  S : ∀ {A B C}
      → ⊩ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
  S = LAM LAM LAM APP (APP V2 V0) (APP V1 V0)


module Level2 where
  I : ∀ {A}
      → ⊩ lam v0 ∶ (A ⊃ A)
  I = LAM² V0²

  K : ∀ {A B}
      → ⊩ lam lam v1 ∶ (A ⊃ B ⊃ A)
  K = LAM² LAM² V1²

  S : ∀ {A B C}
      → ⊩ lam lam lam app (app v2 v0) (app v1 v0) ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
  S = LAM² LAM² LAM² APP² (APP² V2² V0²) (APP² V1² V0²)

  nec-I≡I² : ∀ {A} → nec (Level1.I {A}) ≡ I
  nec-I≡I² = refl

  nec-K≡K² : ∀ {A B} → nec (Level1.K {A} {B}) ≡ K
  nec-K≡K² = refl

  nec-S≡S² : ∀ {A B C} → nec (Level1.S {A} {B} {C}) ≡ S
  nec-S≡S² = refl
