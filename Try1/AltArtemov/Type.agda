module Try1.AltArtemov.Type where

open import Try1.AltArtemov.Type.Core public
open import Try1.AltArtemov.Type.Inversions public
open import Try1.AltArtemov.Type.Properties renaming (lev to ty-lev ; tm to ty-tm ; _≟_ to _Ty≟_) public
