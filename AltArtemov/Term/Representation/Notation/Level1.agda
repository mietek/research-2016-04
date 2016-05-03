module AltArtemov.Term.Representation.Notation.Level1 where

open import AltArtemov.Context.Representation
open import AltArtemov.Term.Representation.Core
open import AltArtemov.Variable.Representation


VAR  : ∀ {g} → ◌∈ g → g ⊢◌
LAM  : ∀ {g} → g ,◌ ⊢◌ → g ⊢◌
APP  : ∀ {g} → g ⊢◌ → g ⊢◌ → g ⊢◌
PAIR : ∀ {g} → g ⊢◌ → g ⊢◌ → g ⊢◌
FST  : ∀ {g} → g ⊢◌ → g ⊢◌
SND  : ∀ {g} → g ⊢◌ → g ⊢◌
UP   : ∀ {g} → g ⊢◌ → g ⊢◌
DOWN : ∀ {g} → g ⊢◌ → g ⊢◌
BOOM : ∀ {g} → g ⊢◌ → g ⊢◌
VAR  = VAR[ 0 ]
LAM  = LAM[ 0 ]
APP  = APP[ 0 ]
PAIR = PAIR[ 0 ]
FST  = FST[ 0 ]
SND  = SND[ 0 ]
UP   = UP[ 0 ]
DOWN = DOWN[ 0 ]
BOOM = BOOM[ 0 ]

V0 : ∀ {g} → g ,◌ ⊢◌
V1 : ∀ {g} → g ,◌ ,◌ ⊢◌
V2 : ∀ {g} → g ,◌ ,◌ ,◌ ⊢◌
V3 : ∀ {g} → g ,◌ ,◌ ,◌ ,◌ ⊢◌
V4 : ∀ {g} → g ,◌ ,◌ ,◌ ,◌ ,◌ ⊢◌
V5 : ∀ {g} → g ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ⊢◌
V6 : ∀ {g} → g ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ⊢◌
V7 : ∀ {g} → g ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ⊢◌
V8 : ∀ {g} → g ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ⊢◌
V9 : ∀ {g} → g ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ⊢◌
V0 = VAR 0ⁱ
V1 = VAR 1ⁱ
V2 = VAR 2ⁱ
V3 = VAR 3ⁱ
V4 = VAR 4ⁱ
V5 = VAR 5ⁱ
V6 = VAR 6ⁱ
V7 = VAR 7ⁱ
V8 = VAR 8ⁱ
V9 = VAR 9ⁱ
