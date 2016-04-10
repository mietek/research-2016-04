module AltArtemov.TermVector.Core where

open import Data.Nat using (ℕ ; zero ; suc)

open import AltArtemov.Term


infixr 5 _∷_

data TmV : ∀ (n : ℕ) → Set where
  [] : TmV zero
  _∷_ : ∀ {n} (t : Tm) (ts : TmV n) → TmV (suc n)
