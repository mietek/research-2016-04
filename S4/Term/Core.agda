module S4.Term.Core where

open import Data.Nat using (ℕ)


data Tm : Set where
  -- Variable reference.
  var : ∀ (i : ℕ) → Tm

  -- Lambda abstraction.
  lam : ∀ (t : Tm) → Tm

  -- Function application.
  app : ∀ (t s : Tm) → Tm

  -- Modal variable reference.
  var* : ∀ (i : ℕ) → Tm

  -- Modality introduction.
  box : ∀ (t : Tm) → Tm

  -- Modality elimination.
  unbox : ∀ (t s : Tm) → Tm
