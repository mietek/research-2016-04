module AltArtemov.Type where

open import AltArtemov.Type.Core public
open import AltArtemov.Type.Inversions public
open import AltArtemov.Type.Properties renaming (lev to ty-lev ; tm to ty-tm ; _≟_ to _Ty≟_) public
