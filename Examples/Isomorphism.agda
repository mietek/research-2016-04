module Examples.Isomorphism where

open import Data.Nat using (≤′-refl)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import AltArtemov
open import Examples.AltArtemov


-- Demonstration of the isomorphism between propositional logic and the
-- λ-calculus.
module DemoPL where
  open ExamPL
  open ExamPL²

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


-- Demonstration of the isomorphism between first- and second-level
-- realisations of theorems of the modal logic S4.
module DemoS4 where
  open ExamS4
  open ExamS4²

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
