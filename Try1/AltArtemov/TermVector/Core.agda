module Try1.AltArtemov.TermVector.Core where

open import Data.Nat using (ℕ ; zero ; suc)

open import Try1.AltArtemov.Term


infixr 5 _∷_

data Tms : ∀ (n : ℕ) → Set where
  [] : Tms zero
  _∷_ : ∀ {n} (t : Tm) (ts : Tms n) → Tms (suc n)
