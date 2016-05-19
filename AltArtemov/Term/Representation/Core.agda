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


data NeR (k : CxR → Set) (g : CxR) : Set where
  VAR[_]  : ℕ → ◌∈ g → NeR k g
  APP[_]  : ℕ → NeR k g → k g → NeR k g
  FST[_]  : ℕ → NeR k g → NeR k g
  SND[_]  : ℕ → NeR k g → NeR k g
  DOWN[_] : ℕ → NeR k g → NeR k g
  BOOM[_] : ℕ → NeR k g → NeR k g


data NfR (d : CxR) : Set where
  NE      : NeR NfR d → NfR d
  LAM[_]  : ℕ → NfR (d ,◌) → NfR d
  PAIR[_] : ℕ → NfR d → NfR d → NfR d
  UP[_]   : ℕ → NfR d → NfR d
  !_      : NfR d → NfR d


mutual
  data ValR (d : CxR) : Set where
    NE      : NeR ValR d → ValR d
    LAM[_]  : ∀ {g} → ℕ → g ,◌ ⊢◌ → EnvR d g → ValR d
    PAIR[_] : ℕ → ValR d → ValR d → ValR d
    UP[_]   : ℕ → ValR d → ValR d

  data EnvR (d : CxR) : CxR → Set where
    ∅   : EnvR d ∅
    _,_ : ∀ {g} → EnvR d g → ValR d → EnvR d (g ,◌)
