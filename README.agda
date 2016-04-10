module README where

open import Data.Nat using (≤′-refl)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import AltArtemov


-- The intended interpretation of some theorems of propositional logic.
module PL⁰ where
  I : ∀ {A : Set}
      → A → A
  I x = x

  K : ∀ {A B : Set}
      → A → B → A
  K x y = x

  S : ∀ {A B C : Set}
      → (A → B → C) → (A → B) → A → C
  S f g x = (f x) (g x)


-- Some theorems of propositional logic.
module PL where
  I : ∀ {A}
      → ⊩ A ⊃ A
  I = LAM V0

  K : ∀ {A B}
      → ⊩ A ⊃ B ⊃ A
  K = LAM LAM V1

  S : ∀ {A B C}
      → ⊩ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
  S = LAM LAM LAM APP (APP V2 V0) (APP V1 V0)


-- Some theorems of the λ-calculus.
module PL² where
  -- □ (A ⊃ A)
  I : ∀ {A}
      → ⊩ lam v0 ∶ (A ⊃ A)
  I = LAM² V0²

  -- □ (A ⊃ B ⊃ A)
  K : ∀ {A B}
      → ⊩ lam lam v1 ∶ (A ⊃ B ⊃ A)
  K = LAM² LAM² V1²

  -- □ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
  S : ∀ {A B C}
      → ⊩ lam lam lam app (app v2 v0) (app v1 v0) ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
  S = LAM² LAM² LAM² APP² (APP² V2² V0²) (APP² V1² V0²)


-- Demonstration of the isomorphism between propositional logic and the λ-calculus.
module PLDemo where
  nec-I≡I² : ∀ {A} → nec (PL.I {A}) ≡ PL².I
  nec-I≡I² = refl

  nec-K≡K² : ∀ {A B} → nec (PL.K {A} {B}) ≡ PL².K
  nec-K≡K² = refl

  nec-S≡S² : ∀ {A B C} → nec (PL.S {A} {B} {C}) ≡ PL².S
  nec-S≡S² = refl

  unnec-I²≡I : ∀ {A} → unnec (PL².I {A}) ≤′-refl ≤′-refl ≡ PL.I
  unnec-I²≡I = refl

  unnec-K²≡K : ∀ {A B} → unnec (PL².K {A} {B}) ≤′-refl ≤′-refl ≡ PL.K
  unnec-K²≡K = refl

  unnec-S²≡S : ∀ {A B C} → unnec (PL².S {A} {B} {C}) ≤′-refl ≤′-refl ≡ PL.S
  unnec-S²≡S = refl


-- Some first-level realisations of theorems of the modal logic S4.
module S4 where
  -- □ (A ⊃ B) ⊃ □ A ⊃ □ B
  K : ∀ {f x A B}
      → ⊩ f ∶ (A ⊃ B) ⊃ x ∶ A ⊃ app f x ∶ B
  K = LAM LAM APP² V1 V0

  -- □ A ⊃ A
  T : ∀ {x A}
      → ⊩ x ∶ A ⊃ A
  T = LAM DOWN V0

  -- □ A ⊃ □ □ A
  #4 : ∀ {x A}
      → ⊩ x ∶ A ⊃ quo x ∶ x ∶ A
  #4 = LAM UP V0


-- Some second-level realisations of theorems of the modal logic S4.
module S4² where
  -- □ (□ (A ⊃ B) ⊃ □ A ⊃ □ B)
  K : ∀ {f x A B}
      → ⊩ lam lam app² v1 v0 ∶ (f ∶ (A ⊃ B) ⊃ x ∶ A ⊃ app f x ∶ B)
  K = LAM² LAM² APP³ V1² V0²

  -- □ (□ A ⊃ A)
  T : ∀ {x A}
      → ⊩ lam down v0 ∶ (x ∶ A ⊃ A)
  T = LAM² DOWN² V0²

  -- □ (□ A ⊃ □ □ A)
  #4 : ∀ {x A}
      → ⊩ lam up v0 ∶ (x ∶ A ⊃ quo x ∶ x ∶ A)
  #4 = LAM² UP² V0²


-- Demonstration of the isomorphism between realisation levels one and two.
module S4Demo where
  nec-K≡K² : ∀ {f x A B} → nec (S4.K {f} {x} {A} {B}) ≡ S4².K
  nec-K≡K² = refl

  nec-T≡T² : ∀ {x A} → nec (S4.T {x} {A}) ≡ S4².T
  nec-T≡T² = refl

  nec-#4≡#4² : ∀ {x A} → nec (S4.#4 {x} {A}) ≡ S4².#4
  nec-#4≡#4² = refl

  unnec-K²≡K : ∀ {f x A B} → unnec (S4².K {f} {x} {A} {B}) ≤′-refl ≤′-refl ≡ S4.K
  unnec-K²≡K = refl

  unnec-T²≡T : ∀ {x A} → unnec (S4².T {x} {A}) ≤′-refl ≤′-refl ≡ S4.T
  unnec-T²≡T = refl

  unnec-#4²≡#4 : ∀ {x A} → unnec (S4².#4 {x} {A}) ≤′-refl ≤′-refl ≡ S4.#4
  unnec-#4²≡#4 = refl
