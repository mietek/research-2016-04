module Try1.AltArtemov.Term.Core where

open import Data.Nat using (ℕ)


data Tm : Set where
  -- Variable reference.
  VAR[_] : ∀ (n i : ℕ) → Tm

  -- Lambda abstraction. (⊃I)
  LAM[_] : ∀ (n : ℕ) (t : Tm) → Tm

  -- Function application. (⊃E)
  APP[_] : ∀ (n : ℕ) (t s : Tm) → Tm

  -- Product. (∧I)
  PAIR[_] : ∀ (n : ℕ) (t s : Tm) → Tm

  -- First projection. (∧E₁)
  FST[_] : ∀ (n : ℕ) (t : Tm) → Tm

  -- Second projection. (∧E₂)
  SND[_] : ∀ (n : ℕ) (t : Tm) → Tm

  -- Reification.
  UP[_] : ∀ (n : ℕ) (t : Tm) → Tm

  -- Reflection.
  DOWN[_] : ∀ (n : ℕ) (t : Tm) → Tm

  -- Explosion. (⊥E)
  BOOM[_] : ∀ (n : ℕ) (t : Tm) → Tm

  -- Type equality. (≑I)
  EQ[_] : ∀ (n : ℕ) (t s : Tm) → Tm
