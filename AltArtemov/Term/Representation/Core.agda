module AltArtemov.Term.Representation.Core where

open import Data.Nat using (ℕ)

open import AltArtemov.Context.Representation
open import AltArtemov.Variable.Representation


data _⊢◌ (g : CxR) : Set where
  VAR[_]  : ℕ → ◌∈ g → g ⊢◌
  LAM[_]  : ℕ → g ,◌ ⊢◌ → g ⊢◌
  APP[_]  : ℕ → g ⊢◌ → g ⊢◌ → g ⊢◌
  PAIR[_] : ℕ → g ⊢◌ → g ⊢◌ → g ⊢◌
  FST[_]  : ℕ → g ⊢◌ → g ⊢◌
  SND[_]  : ℕ → g ⊢◌ → g ⊢◌
  UP[_]   : ℕ → g ⊢◌ → g ⊢◌
  DOWN[_] : ℕ → g ⊢◌ → g ⊢◌
  BOOM[_] : ℕ → g ⊢◌ → g ⊢◌
  !_      : g ⊢◌ → g ⊢◌
