module Examples.ForgetfulProjection where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import AltArtemov
open import Examples.AltArtemov
open import ForgetfulProjection
import Examples.S4 as S4
import S4


-- Forgetful projection of some theorems of propositional logic.
module DemoPL where
  °I≡S4-I : ∀ {A °A}
      → °[ A ] ≡ °A
      → °[ ty (ExamPL.I {A}) ] ≡ S4.ty (S4.ExamPL.I {°A})
  °I≡S4-I a rewrite a = refl

  °K≡S4-K : ∀ {A B °A °B}
      → °[ A ] ≡ °A    → °[ B ] ≡ °B
      → °[ ty (ExamPL.K {A} {B}) ] ≡ S4.ty (S4.ExamPL.K {°A} {°B})
  °K≡S4-K a b rewrite a | b = refl

  °S≡S4-S : ∀ {A B C °A °B °C}
      → °[ A ] ≡ °A    → °[ B ] ≡ °B    → °[ C ] ≡ °C
      → °[ ty (ExamPL.S {A} {B} {C}) ] ≡ S4.ty (S4.ExamPL.S {°A} {°B} {°C})
  °S≡S4-S a b c rewrite a | b | c = refl


-- Forgetful projection of some theorems of the λ-calculus.
module DemoPL² where
  °I²≡S4-□I : ∀ {A °A}
      → °[ A ] ≡ °A
      → °[ ty (ExamPL².I² {A}) ] ≡ S4.ty (S4.Exam□PL.□I {°A})
  °I²≡S4-□I a rewrite a = refl

  °K²≡S4-□K : ∀ {A B °A °B}
      → °[ A ] ≡ °A    → °[ B ] ≡ °B
      → °[ ty (ExamPL².K² {A} {B}) ] ≡ S4.ty (S4.Exam□PL.□K {°A} {°B})
  °K²≡S4-□K a b rewrite a | b = refl

  °S²≡S4-□S : ∀ {A B C °A °B °C}
      → °[ A ] ≡ °A    → °[ B ] ≡ °B    → °[ C ] ≡ °C
      → °[ ty (ExamPL².S² {A} {B} {C}) ] ≡ S4.ty (S4.Exam□PL.□S {°A} {°B} {°C})
  °S²≡S4-□S a b c rewrite a | b | c = refl


-- Forgetful projection of some first-level realisations of theorems of the
-- modal logic S4.
module DemoS4 where
  °K≡S4-K : ∀ {f x A B °A °B}
      → °[ A ] ≡ °A    → °[ B ] ≡ °B
      → °[ ty (ExamS4.K {f} {x} {A} {B}) ] ≡ S4.ty (S4.ExamS4.K {°A} {°B})
  °K≡S4-K a b rewrite a | b = refl

  °T≡S4-T : ∀ {x A °A}
      → °[ A ] ≡ °A
      → °[ ty (ExamS4.T {x} {A}) ] ≡ S4.ty (S4.ExamS4.T {°A})
  °T≡S4-T a rewrite a = refl

  °#4≡S4-#4 : ∀ {x A °A}
      → °[ A ] ≡ °A
      → °[ ty (ExamS4.#4 {x} {A}) ] ≡ S4.ty (S4.ExamS4.#4 {°A})
  °#4≡S4-#4 a rewrite a = refl


-- Forgetful projection of some second-level realisations of theorems of the
-- modal logic S4.
module DemoS4² where
  °K²≡S4-□K : ∀ {f x A B °A °B}
      → °[ A ] ≡ °A    → °[ B ] ≡ °B
      → °[ ty (ExamS4².K² {f} {x} {A} {B}) ] ≡ S4.ty (S4.Exam□S4.□K {°A} {°B})
  °K²≡S4-□K a b rewrite a | b = refl

  °T²≡S4-□T : ∀ {x A °A}
      → °[ A ] ≡ °A
      → °[ ty (ExamS4².T² {x} {A}) ] ≡ S4.ty (S4.Exam□S4.□T {°A})
  °T²≡S4-□T a rewrite a = refl

  °#4²≡S4-□#T : ∀ {x A °A}
      → °[ A ] ≡ °A
      → °[ ty (ExamS4².#4² {x} {A}) ] ≡ S4.ty (S4.Exam□S4.□#4 {°A})
  °#4²≡S4-□#T a rewrite a = refl
