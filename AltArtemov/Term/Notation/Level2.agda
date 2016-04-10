module AltArtemov.Term.Notation.Level2 where

open import AltArtemov.Term.Core


var²_ : ∀ i → Tm
var² i₂ = var[ 1 ] i₂

lam²_ : ∀ t₂ → Tm
lam² t₂ = lam[ 1 ] t₂

app² : ∀ t₂ s₂ → Tm
app² t₂ s₂ = app[ 1 ] t₂ s₂

up²_ : ∀ t₂ → Tm
up² t₂ = up[ 1 ] t₂

down²_ : ∀ t₂ → Tm
down² t₂ = down[ 1 ] t₂


v0² : Tm
v0² = var² 0

v1² : Tm
v1² = var² 1

v2² : Tm
v2² = var² 2

v3² : Tm
v3² = var² 3

v4² : Tm
v4² = var² 4

v5² : Tm
v5² = var² 5

v6² : Tm
v6² = var² 6

v7² : Tm
v7² = var² 7

v8² : Tm
v8² = var² 8

v9² : Tm
v9² = var² 9
