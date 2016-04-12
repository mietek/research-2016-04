module AltArtemov.Derivation.Notation where

open import AltArtemov.Context
open import AltArtemov.Derivation.Core
open import AltArtemov.Derivation.Notation.Level1 public
open import AltArtemov.Derivation.Notation.Level2 public
open import AltArtemov.Derivation.Notation.Level3 public
open import AltArtemov.Type


infixr 0 ⊩_

⊩_ : ∀ (A : Ty) → Set
⊩ A = ∅ ⊢ A
