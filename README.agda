module README where

open import Data.Nat using (≤′-refl)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import AltArtemov


-- Some theorems of propositional logic.
module PL where
  I : ∀ {A} → ⊩ A ⊃ A
  I = LAM V0

  K : ∀ {A B} → ⊩ A ⊃ B ⊃ A
  K = LAM (LAM V1)

  S : ∀ {A B C} → ⊩ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
  S = LAM (LAM (LAM (APP (APP V2 V0) (APP V1 V0))))


-- Some theorems of the λ-calculus.
module PL² where
  -- □ (A ⊃ A)
  I² : ∀ {A} → ⊩ lam v0 ∶ (A ⊃ A)
  I² = LAM² V0²

  -- □ (A ⊃ B ⊃ A)
  K² : ∀ {A B} → ⊩ lam (lam v1) ∶ (A ⊃ B ⊃ A)
  K² = LAM² (LAM² V1²)

  -- □ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
  S² : ∀ {A B C} → ⊩ lam (lam (lam (app (app v2 v0) (app v1 v0)))) ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
  S² = LAM² (LAM² (LAM² (APP² (APP² V2² V0²) (APP² V1² V0²))))


-- Demonstration of the isomorphism between propositional logic and the λ-calculus.
module PLDemo where
  open PL
  open PL²

  nec-I≡I² : ∀ {A}
      → nec (I {A}) ≡ I²
  nec-I≡I² = refl

  nec-K≡K² : ∀ {A B}
      → nec (K {A} {B}) ≡ K²
  nec-K≡K² = refl

  nec-S≡S² : ∀ {A B C}
      → nec (S {A} {B} {C}) ≡ S²
  nec-S≡S² = refl

  unnec-I²≡I : ∀ {A}
      → unnec (I² {A}) ≤′-refl ≤′-refl ≡ I
  unnec-I²≡I = refl

  unnec-K²≡K : ∀ {A B}
      → unnec (K² {A} {B}) ≤′-refl ≤′-refl ≡ K
  unnec-K²≡K = refl

  unnec-S²≡S : ∀ {A B C}
      → unnec (S² {A} {B} {C}) ≤′-refl ≤′-refl ≡ S
  unnec-S²≡S = refl


-- Some first-level realisations of theorems of the modal logic S4.
module S4 where
  -- □ (A ⊃ B) ⊃ □ A ⊃ □ B
  K : ∀ {f x A B} → ⊩ f ∶ (A ⊃ B) ⊃ x ∶ A ⊃ app f x ∶ B
  K = LAM (LAM (APP² V1 V0))

  -- □ A ⊃ A
  T : ∀ {x A} → ⊩ x ∶ A ⊃ A
  T = LAM (DOWN V0)

  -- □ A ⊃ □ □ A
  #4 : ∀ {x A} → ⊩ x ∶ A ⊃ quo x ∶ x ∶ A
  #4 = LAM (UP V0)


-- Some second-level realisations of theorems of the modal logic S4.
module S4² where
  -- □ (□ (A ⊃ B) ⊃ □ A ⊃ □ B)
  K² : ∀ {f x A B} → ⊩ lam (lam (app² v1 v0)) ∶ (f ∶ (A ⊃ B) ⊃ x ∶ A ⊃ app f x ∶ B)
  K² = LAM² (LAM² (APP³ V1² V0²))

  -- □ (□ A ⊃ A)
  T² : ∀ {x A} → ⊩ lam (down v0) ∶ (x ∶ A ⊃ A)
  T² = LAM² (DOWN² V0²)

  -- □ (□ A ⊃ □ □ A)
  #4² : ∀ {x A} → ⊩ lam (up v0) ∶ (x ∶ A ⊃ quo x ∶ x ∶ A)
  #4² = LAM² (UP² V0²)


-- Demonstration of the isomorphism between realisation levels one and two.
module S4Demo where
  open S4
  open S4²

  nec-K≡K² : ∀ {f x A B}
      → nec (K {f} {x} {A} {B}) ≡ K²
  nec-K≡K² = refl

  nec-T≡T² : ∀ {x A}
      → nec (T {x} {A}) ≡ T²
  nec-T≡T² = refl

  nec-#4≡#4² : ∀ {x A}
      → nec (#4 {x} {A}) ≡ #4²
  nec-#4≡#4² = refl

  unnec-K²≡K : ∀ {f x A B}
      → unnec (K² {f} {x} {A} {B}) ≤′-refl ≤′-refl ≡ K
  unnec-K²≡K = refl

  unnec-T²≡T : ∀ {x A}
      → unnec (T² {x} {A}) ≤′-refl ≤′-refl ≡ T
  unnec-T²≡T = refl

  unnec-#4²≡#4 : ∀ {x A}
      → unnec (#4² {x} {A}) ≤′-refl ≤′-refl ≡ #4
  unnec-#4²≡#4 = refl
