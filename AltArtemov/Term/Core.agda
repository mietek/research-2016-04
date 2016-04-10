module AltArtemov.Term.Core where

open import Data.Nat using (ℕ)


data Tm : Set where
  -- Variable reference.
  var[_] : ∀ (n i : ℕ) → Tm

  -- Lambda abstraction.
  lam[_] : ∀ (n : ℕ) (t : Tm) → Tm

  -- Function application.
  app[_] : ∀ (n : ℕ) (t s : Tm) → Tm

  -- Reification.
  up[_] : ∀ (n : ℕ) (t : Tm) → Tm

  -- Reflection
  down[_] : ∀ (n : ℕ) (t : Tm) → Tm
