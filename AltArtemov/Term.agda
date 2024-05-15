module AltArtemov.Term where

open import AltArtemov.Term.Core public
open import AltArtemov.Term.Inversions public
open import AltArtemov.Term.Notation.Level1 public
open import AltArtemov.Term.Notation.Level2 public
open import AltArtemov.Term.Notation.Level3 public
open import AltArtemov.Term.Notation.Level4 public
open import AltArtemov.Term.Properties renaming (lev to tm-lev ; _≟_ to _Tm≟_) public
