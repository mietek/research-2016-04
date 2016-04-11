module S4 where

open import S4.Context public
open import S4.Derivation public
open import S4.Term public
open import S4.Type public


-- Some theorems of propositional logic.
module PL where
  I : ∀ {A} → ⊩ A ⊃ A
  I = LAM V0

  K : ∀ {A B} → ⊩ A ⊃ B ⊃ A
  K = LAM (LAM V1)

  S : ∀ {A B C} → ⊩ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
  S = LAM (LAM (LAM (APP (APP V2 V0) (APP V1 V0))))


-- Some theorems of the ƛ-calculus.
module PL² where
  I² : ∀ {A} → ⊩ lam v0 ∶ (A ⊃ A)
  I² = LAM² V0²

  K² : ∀ {A B} → ⊩ lam (lam v1) ∶ (A ⊃ B ⊃ A)
  K² = LAM² (LAM² V1²)

  S² : ∀ {A B C} → ⊩ lam (lam (lam (app (app v2 v0) (app v1 v0)))) ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
  S² = LAM² (LAM² (LAM² (APP² (APP² V2² V0²) (APP² V1² V0²))))


-- An implicit provability interpretation of the above theorems.
module PL²′ where
  I²′ : ∀ {A} → ⊩ □ (A ⊃ A)
  I²′ = BOX (LAM V0)

  K²′ : ∀ {A B} → ⊩ □ (A ⊃ B ⊃ A)
  K²′ = BOX (LAM (LAM V1))

  S²′ : ∀ {A B C} → ⊩ □ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
  S²′ = BOX (LAM (LAM (LAM (APP (APP V2 V0) (APP V1 V0)))))


-- Some theorems of the modal logic S4.
module S4 where
  K : ∀ {A B} → ⊩ □ (A ⊃ B) ⊃ □ A ⊃ □ B
  K = LAM (LAM (UNBOX V1 (UNBOX V0 (BOX (APP V1* V0*)))))

  T : ∀ {A} → ⊩ □ A ⊃ A
  T = LAM (UNBOX V0 V0*)

  #4 : ∀ {A} → ⊩ □ A ⊃ □ □ A
  #4 = LAM (UNBOX V0 (BOX (BOX V0*)))


-- Some theorems of the λ-calculus for S4.
module S4² where
  K² : ∀ {A B} → ⊩ lam (lam (unbox v1 (unbox v0 (box (app v1* v0*))))) ∶ (□ (A ⊃ B) ⊃ □ A ⊃ □ B)
  K² = LAM² (LAM² (UNBOX² V1² (UNBOX² V0² (BOX² (APP² V1*² V0*²)))))

  T² : ∀ {A} → ⊩ lam (unbox v0 v0*) ∶ (□ A ⊃ A)
  T² = LAM² (UNBOX² V0² V0*²)

  #4² : ∀ {A} → ⊩ lam (unbox v0 (box (box v0*))) ∶ (□ A ⊃ □ □ A)
  #4² = LAM² (UNBOX² V0² (BOX² (BOX² V0*²)))


-- An implicit provability interpretation of the above theorems.
module S4²′ where
  K²′ : ∀ {A B} → ⊩ □ (□ (A ⊃ B) ⊃ □ A ⊃ □ B)
  K²′ = BOX (LAM (LAM (UNBOX V1 (UNBOX V0 (BOX (APP V1* V0*))))))

  T²′ : ∀ {A} → ⊩ □ (□ A ⊃ A)
  T²′ = BOX (LAM (UNBOX V0 V0*))

  #4²′ : ∀ {A} → ⊩ □ (□ A ⊃ □ □ A)
  #4²′ = BOX (LAM (UNBOX V0 (BOX (BOX V0*))))
