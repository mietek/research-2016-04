module Try1.AltArtemov.Term.Notation.Level3 where

open import Try1.AltArtemov.Term.Core


VAR³ : ∀ i → Tm
VAR³ i₃ = VAR[ 2 ] i₃

LAM³ : ∀ t₃ → Tm
LAM³ t₃ = LAM[ 2 ] t₃

APP³ : ∀ t₃ s₃ → Tm
APP³ t₃ s₃ = APP[ 2 ] t₃ s₃

PAIR³ : ∀ t₃ s₃ → Tm
PAIR³ t₃ s₃ = PAIR[ 2 ] t₃ s₃

FST³ : ∀ t₃ → Tm
FST³ t₃ = FST[ 2 ] t₃

SND³ : ∀ t₃ → Tm
SND³ t₃ = SND[ 2 ] t₃

UP³ : ∀ t₃ → Tm
UP³ t₃ = UP[ 2 ] t₃

DOWN³ : ∀ t₃ → Tm
DOWN³ t₃ = DOWN[ 2 ] t₃

BOOM³ : ∀ t₃ → Tm
BOOM³ t₃ = BOOM[ 2 ] t₃

EQ³ : ∀ t₃ s₃ → Tm
EQ³ t₃ s₃ = EQ[ 2 ] t₃ s₃


V0³ : Tm
V0³ = VAR³ 0

V1³ : Tm
V1³ = VAR³ 1

V2³ : Tm
V2³ = VAR³ 2

V3³ : Tm
V3³ = VAR³ 3

V4³ : Tm
V4³ = VAR³ 4

V5³ : Tm
V5³ = VAR³ 5

V6³ : Tm
V6³ = VAR³ 6

V7³ : Tm
V7³ = VAR³ 7

V8³ : Tm
V8³ = VAR³ 8

V9³ : Tm
V9³ = VAR³ 9
