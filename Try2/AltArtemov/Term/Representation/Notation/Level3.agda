module Try2.AltArtemov.Term.Representation.Notation.Level3 where

open import Try2.AltArtemov.Context.Representation
open import Try2.AltArtemov.Term.Representation.Core
open import Try2.AltArtemov.Variable.Representation


VAR³  : ∀ {g} → ◌∈ g → g ⊢◌
LAM³  : ∀ {g} → g ,◌ ⊢◌ → g ⊢◌
APP³  : ∀ {g} → g ⊢◌ → g ⊢◌ → g ⊢◌
PAIR³ : ∀ {g} → g ⊢◌ → g ⊢◌ → g ⊢◌
FST³  : ∀ {g} → g ⊢◌ → g ⊢◌
SND³  : ∀ {g} → g ⊢◌ → g ⊢◌
UP³   : ∀ {g} → g ⊢◌ → g ⊢◌
DOWN³ : ∀ {g} → g ⊢◌ → g ⊢◌
BOOM³ : ∀ {g} → g ⊢◌ → g ⊢◌
VAR³  = VAR[ 2 ]
LAM³  = LAM[ 2 ]
APP³  = APP[ 2 ]
PAIR³ = PAIR[ 2 ]
FST³  = FST[ 2 ]
SND³  = SND[ 2 ]
UP³   = UP[ 2 ]
DOWN³ = DOWN[ 2 ]
BOOM³ = BOOM[ 2 ]

V0³ : ∀ {g} → g ,◌ ⊢◌
V1³ : ∀ {g} → g ,◌ ,◌ ⊢◌
V2³ : ∀ {g} → g ,◌ ,◌ ,◌ ⊢◌
V3³ : ∀ {g} → g ,◌ ,◌ ,◌ ,◌ ⊢◌
V4³ : ∀ {g} → g ,◌ ,◌ ,◌ ,◌ ,◌ ⊢◌
V5³ : ∀ {g} → g ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ⊢◌
V6³ : ∀ {g} → g ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ⊢◌
V7³ : ∀ {g} → g ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ⊢◌
V8³ : ∀ {g} → g ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ⊢◌
V9³ : ∀ {g} → g ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ,◌ ⊢◌
V0³ = VAR³ 0ⁱ
V1³ = VAR³ 1ⁱ
V2³ = VAR³ 2ⁱ
V3³ = VAR³ 3ⁱ
V4³ = VAR³ 4ⁱ
V5³ = VAR³ 5ⁱ
V6³ = VAR³ 6ⁱ
V7³ = VAR³ 7ⁱ
V8³ = VAR³ 8ⁱ
V9³ = VAR³ 9ⁱ
