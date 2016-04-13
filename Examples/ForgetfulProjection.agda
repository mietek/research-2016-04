module Examples.ForgetfulProjection where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import AltArtemov
open import Examples.AltArtemov
open import ForgetfulProjection
import Examples.S4 as S4
import S4


-- Forgetful projection of some theorems of propositional logic.
module DemoPL where
  °[I]≡I : ∀ {A °A}
      → °[ A ] ≡ °A
      → °[ ty (ExamPL.I {A}) ] ≡ S4.ty (S4.ExamPL.I {°A})
  °[I]≡I a rewrite a = refl

  °[K]≡K : ∀ {A B °A °B}
      → °[ A ] ≡ °A    → °[ B ] ≡ °B
      → °[ ty (ExamPL.K {A} {B}) ] ≡ S4.ty (S4.ExamPL.K {°A} {°B})
  °[K]≡K a b rewrite a | b = refl

  °[S]≡S : ∀ {A B C °A °B °C}
      → °[ A ] ≡ °A    → °[ B ] ≡ °B    → °[ C ] ≡ °C
      → °[ ty (ExamPL.S {A} {B} {C}) ] ≡ S4.ty (S4.ExamPL.S {°A} {°B} {°C})
  °[S]≡S a b c rewrite a | b | c = refl


-- Forgetful projection of some theorems of the λ-calculus.
module DemoPL² where
  °[I²]≡□I : ∀ {A °A}
      → °[ A ] ≡ °A
      → °[ ty (ExamPL².I² {A}) ] ≡ S4.ty (S4.Exam□PL.□I {°A})
  °[I²]≡□I a rewrite a = refl

  °[K²]≡□K : ∀ {A B °A °B}
      → °[ A ] ≡ °A    → °[ B ] ≡ °B
      → °[ ty (ExamPL².K² {A} {B}) ] ≡ S4.ty (S4.Exam□PL.□K {°A} {°B})
  °[K²]≡□K a b rewrite a | b = refl

  °[S²]≡□S : ∀ {A B C °A °B °C}
      → °[ A ] ≡ °A    → °[ B ] ≡ °B    → °[ C ] ≡ °C
      → °[ ty (ExamPL².S² {A} {B} {C}) ] ≡ S4.ty (S4.Exam□PL.□S {°A} {°B} {°C})
  °[S²]≡□S a b c rewrite a | b | c = refl


-- Forgetful projection of some first-level realisations of theorems of the
-- modal logic S4.
module DemoS4 where
  °[K]≡K : ∀ {f x A B °A °B}
      → °[ A ] ≡ °A    → °[ B ] ≡ °B
      → °[ ty (ExamS4.K {f} {x} {A} {B}) ] ≡ S4.ty (S4.ExamS4.K {°A} {°B})
  °[K]≡K a b rewrite a | b = refl

  °[T]≡T : ∀ {x A °A}
      → °[ A ] ≡ °A
      → °[ ty (ExamS4.T {x} {A}) ] ≡ S4.ty (S4.ExamS4.T {°A})
  °[T]≡T a rewrite a = refl

  °[#4]≡#4 : ∀ {x A °A}
      → °[ A ] ≡ °A
      → °[ ty (ExamS4.#4 {x} {A}) ] ≡ S4.ty (S4.ExamS4.#4 {°A})
  °[#4]≡#4 a rewrite a = refl


-- Forgetful projection of some second-level realisations of theorems of the
-- modal logic S4.
module DemoS4² where
  °[K²]≡□K : ∀ {f x A B °A °B}
      → °[ A ] ≡ °A    → °[ B ] ≡ °B
      → °[ ty (ExamS4².K² {f} {x} {A} {B}) ] ≡ S4.ty (S4.Exam□S4.□K {°A} {°B})
  °[K²]≡□K a b rewrite a | b = refl

  °[T²]≡□T : ∀ {x A °A}
      → °[ A ] ≡ °A
      → °[ ty (ExamS4².T² {x} {A}) ] ≡ S4.ty (S4.Exam□S4.□T {°A})
  °[T²]≡□T a rewrite a = refl

  °[#4²]≡□#T : ∀ {x A °A}
      → °[ A ] ≡ °A
      → °[ ty (ExamS4².#4² {x} {A}) ] ≡ S4.ty (S4.Exam□S4.□#4 {°A})
  °[#4²]≡□#T a rewrite a = refl
