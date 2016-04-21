module AltArtemov.Term.Notation.Level2 where

open import AltArtemov.Term.Core


VAR² : ∀ i → Tm
VAR² i₂ = VAR[ 1 ] i₂

LAM² : ∀ t₂ → Tm
LAM² t₂ = LAM[ 1 ] t₂

APP² : ∀ t₂ s₂ → Tm
APP² t₂ s₂ = APP[ 1 ] t₂ s₂

UP² : ∀ t₂ → Tm
UP² t₂ = UP[ 1 ] t₂

DOWN² : ∀ t₂ → Tm
DOWN² t₂ = DOWN[ 1 ] t₂

BOOM² : ∀ t₂ → Tm
BOOM² t₂ = BOOM[ 1 ] t₂


V0² : Tm
V0² = VAR² 0

V1² : Tm
V1² = VAR² 1

V2² : Tm
V2² = VAR² 2

V3² : Tm
V3² = VAR² 3

V4² : Tm
V4² = VAR² 4

V5² : Tm
V5² = VAR² 5

V6² : Tm
V6² = VAR² 6

V7² : Tm
V7² = VAR² 7

V8² : Tm
V8² = VAR² 8

V9² : Tm
V9² = VAR² 9
