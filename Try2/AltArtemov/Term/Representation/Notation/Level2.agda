module Try2.AltArtemov.Term.Representation.Notation.Level2 where

open import Try2.AltArtemov.Context.Representation
open import Try2.AltArtemov.Term.Representation.Core
open import Try2.AltArtemov.Variable.Representation


VAR²  : ∀ {g} → ◌∈ g → g ⊢◌
LAM²  : ∀ {g} → g ,◌ ⊢◌ → g ⊢◌
APP²  : ∀ {g} → g ⊢◌ → g ⊢◌ → g ⊢◌
PAIR² : ∀ {g} → g ⊢◌ → g ⊢◌ → g ⊢◌
FST²  : ∀ {g} → g ⊢◌ → g ⊢◌
SND²  : ∀ {g} → g ⊢◌ → g ⊢◌
UP²   : ∀ {g} → g ⊢◌ → g ⊢◌
DOWN² : ∀ {g} → g ⊢◌ → g ⊢◌
BOOM² : ∀ {g} → g ⊢◌ → g ⊢◌
VAR²  = VAR[ 1 ]
LAM²  = LAM[ 1 ]
APP²  = APP[ 1 ]
PAIR² = PAIR[ 1 ]
FST²  = FST[ 1 ]
SND²  = SND[ 1 ]
UP²   = UP[ 1 ]
DOWN² = DOWN[ 1 ]
BOOM² = BOOM[ 1 ]

V0² : ∀ {g} → g ,◌ ⊢◌
V1² : ∀ {g} → g ,◌ ,◌ ⊢◌
V2² : ∀ {g} → g ,◌ ,◌ ,◌ ⊢◌
V3² : ∀ {g} → g ,◌ ,◌ ,◌ ,◌ ⊢◌
V4² : ∀ {g} → g ,◌ ,◌ ,◌ ,◌ ,◌ ⊢◌
V5² : ∀ {g} → g ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ⊢◌
V6² : ∀ {g} → g ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ⊢◌
V7² : ∀ {g} → g ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ⊢◌
V8² : ∀ {g} → g ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ⊢◌
V9² : ∀ {g} → g ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ⊢◌
V0² = VAR² 0ⁱ
V1² = VAR² 1ⁱ
V2² = VAR² 2ⁱ
V3² = VAR² 3ⁱ
V4² = VAR² 4ⁱ
V5² = VAR² 5ⁱ
V6² = VAR² 6ⁱ
V7² = VAR² 7ⁱ
V8² = VAR² 8ⁱ
V9² = VAR² 9ⁱ
