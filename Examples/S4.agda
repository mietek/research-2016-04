module Examples.S4 where

open import S4


-- Some theorems of propositional logic.
module ExamPL where
  I : ∀ {A} → ⊩ A ⊃ A
  I = LAM V0

  K : ∀ {A B} → ⊩ A ⊃ B ⊃ A
  K = LAM (LAM V1)

  S : ∀ {A B C} → ⊩ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
  S = LAM (LAM (LAM (APP (APP V2 V0) (APP V1 V0))))


-- Some modalised theorems of propositional logic.
module Exam□PL where
  □I : ∀ {A} → ⊩ □ (A ⊃ A)
  □I = BOX (LAM V0)

  □K : ∀ {A B} → ⊩ □ (A ⊃ B ⊃ A)
  □K = BOX (LAM (LAM V1))

  □S : ∀ {A B C} → ⊩ □ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
  □S = BOX (LAM (LAM (LAM (APP (APP V2 V0) (APP V1 V0)))))


-- Some theorems of the modal logic S4.
module ExamS4 where
  K : ∀ {A B} → ⊩ □ (A ⊃ B) ⊃ □ A ⊃ □ B
  K = LAM (LAM (UNBOX V1 (UNBOX V0 (BOX (APP V1* V0*)))))

  T : ∀ {A} → ⊩ □ A ⊃ A
  T = LAM (UNBOX V0 V0*)

  #4 : ∀ {A} → ⊩ □ A ⊃ □ □ A
  #4 = LAM (UNBOX V0 (BOX (BOX V0*)))


-- Some modalised theorems of the modal logic S4.
module Exam□S4 where
  □K : ∀ {A B} → ⊩ □ (□ (A ⊃ B) ⊃ □ A ⊃ □ B)
  □K = BOX (LAM (LAM (UNBOX V1 (UNBOX V0 (BOX (APP V1* V0*))))))

  □T : ∀ {A} → ⊩ □ (□ A ⊃ A)
  □T = BOX (LAM (UNBOX V0 V0*))

  □#4 : ∀ {A} → ⊩ □ (□ A ⊃ □ □ A)
  □#4 = BOX (LAM (UNBOX V0 (BOX (BOX V0*))))
