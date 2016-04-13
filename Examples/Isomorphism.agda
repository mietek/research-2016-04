module Examples.Isomorphism where

open import Data.Nat using (≤′-refl)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import AltArtemov
open import Examples.AltArtemov


-- Demonstration of the isomorphism between propositional logic and the
-- λ-calculus.
module DemoPL where
  nec-I≡I² : ∀ {A}
      → nec (ExamPL.I {A}) ≡ ExamPL².I²
  nec-I≡I² = refl

  nec-K≡K² : ∀ {A B}
      → nec (ExamPL.K {A} {B}) ≡ ExamPL².K²
  nec-K≡K² = refl

  nec-S≡S² : ∀ {A B C}
      → nec (ExamPL.S {A} {B} {C}) ≡ ExamPL².S²
  nec-S≡S² = refl

  unnec-I²≡I : ∀ {A}
      → unnec (ExamPL².I² {A}) ≤′-refl ≤′-refl ≡ ExamPL.I
  unnec-I²≡I = refl

  unnec-K²≡K : ∀ {A B}
      → unnec (ExamPL².K² {A} {B}) ≤′-refl ≤′-refl ≡ ExamPL.K
  unnec-K²≡K = refl

  unnec-S²≡S : ∀ {A B C}
      → unnec (ExamPL².S² {A} {B} {C}) ≤′-refl ≤′-refl ≡ ExamPL.S
  unnec-S²≡S = refl


-- Demonstration of the isomorphism between first- and second-level
-- realisations of theorems of the modal logic S4.
module DemoS4 where
  nec-K≡K² : ∀ {f x A B}
      → nec (ExamS4.K {f} {x} {A} {B}) ≡ ExamS4².K²
  nec-K≡K² = refl

  nec-T≡T² : ∀ {x A}
      → nec (ExamS4.T {x} {A}) ≡ ExamS4².T²
  nec-T≡T² = refl

  nec-#4≡#4² : ∀ {x A}
      → nec (ExamS4.#4 {x} {A}) ≡ ExamS4².#4²
  nec-#4≡#4² = refl

  unnec-K²≡K : ∀ {f x A B}
      → unnec (ExamS4².K² {f} {x} {A} {B}) ≤′-refl ≤′-refl ≡ ExamS4.K
  unnec-K²≡K = refl

  unnec-T²≡T : ∀ {x A}
      → unnec (ExamS4².T² {x} {A}) ≤′-refl ≤′-refl ≡ ExamS4.T
  unnec-T²≡T = refl

  unnec-#4²≡#4 : ∀ {x A}
      → unnec (ExamS4².#4² {x} {A}) ≤′-refl ≤′-refl ≡ ExamS4.#4
  unnec-#4²≡#4 = refl
