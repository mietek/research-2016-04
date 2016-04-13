module Examples.AltArtemov where

open import AltArtemov


-- Some theorems of propositional logic.
module ExamPL where
  I : ∀ {A}
      → ⊩ A ⊃ A
  I = LAM V0

  K : ∀ {A B}
      → ⊩ A ⊃ B ⊃ A
  K = LAM (LAM V1)

  S : ∀ {A B C}
      → ⊩ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
  S = LAM (LAM (LAM (APP (APP V2 V0) (APP V1 V0))))


-- Some theorems of the λ-calculus.
module ExamPL² where
  I² : ∀ {A}
      → ⊩ lam v0 ∶ (A ⊃ A)
  I² = LAM² V0²

  K² : ∀ {A B}
      → ⊩ lam (lam v1) ∶ (A ⊃ B ⊃ A)
  K² = LAM² (LAM² V1²)

  S² : ∀ {A B C}
      → ⊩ lam (lam (lam (app (app v2 v0) (app v1 v0))))
          ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
  S² = LAM² (LAM² (LAM² (APP² (APP² V2² V0²) (APP² V1² V0²))))


-- Some first-level realisations of theorems of the modal logic S4.
module ExamS4 where
  K : ∀ {f x A B}
      → ⊩ f ∶ (A ⊃ B) ⊃ x ∶ A ⊃ app f x ∶ B
  K = LAM (LAM (APP² V1 V0))

  T : ∀ {x A}
      → ⊩ x ∶ A ⊃ A
  T = LAM (DOWN V0)

  #4 : ∀ {x A}
      → ⊩ x ∶ A ⊃ quo x ∶ x ∶ A
  #4 = LAM (UP V0)


-- Some second-level realisations of theorems of the modal logic S4.
module ExamS4² where
  K² : ∀ {f x A B}
      → ⊩ lam (lam (app² v1 v0)) ∶ (f ∶ (A ⊃ B) ⊃ x ∶ A ⊃ app f x ∶ B)
  K² = LAM² (LAM² (APP³ V1² V0²))

  T² : ∀ {x A}
      → ⊩ lam (down v0) ∶ (x ∶ A ⊃ A)
  T² = LAM² (DOWN² V0²)

  #4² : ∀ {x A}
      → ⊩ lam (up v0) ∶ (x ∶ A ⊃ quo x ∶ x ∶ A)
  #4² = LAM² (UP² V0²)
