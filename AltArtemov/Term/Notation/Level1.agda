module AltArtemov.Term.Notation.Level1 where

open import AltArtemov.Term.Core


var_ : ∀ i → Tm
var i = var[ 0 ] i

lam_ : ∀ t → Tm
lam t = lam[ 0 ] t

app : ∀ t s → Tm
app t s = app[ 0 ] t s


v0 : Tm
v0 = var 0

v1 : Tm
v1 = var 1

v2 : Tm
v2 = var 2

v3 : Tm
v3 = var 3

v4 : Tm
v4 = var 4

v5 : Tm
v5 = var 5

v6 : Tm
v6 = var 6

v7 : Tm
v7 = var 7

v8 : Tm
v8 = var 8

v9 : Tm
v9 = var 9
