module AltArtemov.Term where

open import AltArtemov.Term.Core public
open import AltArtemov.Term.Notation public
open import AltArtemov.Term.Properties renaming (lev to tm-lev ; _≟_ to _Tm≟_) public
