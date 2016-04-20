module AltArtemov.Term.Notation.Level1 where

open import AltArtemov.Term.Core


VAR : ∀ i → Tm
VAR i = VAR[ 0 ] i

LAM : ∀ t → Tm
LAM t = LAM[ 0 ] t

APP : ∀ t s → Tm
APP t s = APP[ 0 ] t s

UP : ∀ t → Tm
UP t = UP[ 0 ] t

DOWN : ∀ t → Tm
DOWN t = DOWN[ 0 ] t


V0 : Tm
V0 = VAR 0

V1 : Tm
V1 = VAR 1

V2 : Tm
V2 = VAR 2

V3 : Tm
V3 = VAR 3

V4 : Tm
V4 = VAR 4

V5 : Tm
V5 = VAR 5

V6 : Tm
V6 = VAR 6

V7 : Tm
V7 = VAR 7

V8 : Tm
V8 = VAR 8

V9 : Tm
V9 = VAR 9
