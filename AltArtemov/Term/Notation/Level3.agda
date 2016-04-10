module AltArtemov.Term.Notation.Level3 where

open import AltArtemov.Term.Core


var³_ : ∀ i → Tm
var³ i₃ = var[ 2 ] i₃

lam³_ : ∀ t₃ → Tm
lam³ t₃ = lam[ 2 ] t₃

app³ : ∀ t₃ s₃ → Tm
app³ t₃ s₃ = app[ 2 ] t₃ s₃

up³_ : ∀ t₃ → Tm
up³ t₃ = up[ 2 ] t₃

down³_ : ∀ t₃ → Tm
down³ t₃ = down[ 2 ] t₃


v0³ : Tm
v0³ = var³ 0

v1³ : Tm
v1³ = var³ 1

v2³ : Tm
v2³ = var³ 2

v3³ : Tm
v3³ = var³ 3

v4³ : Tm
v4³ = var³ 4

v5³ : Tm
v5³ = var³ 5

v6³ : Tm
v6³ = var³ 6

v7³ : Tm
v7³ = var³ 7

v8³ : Tm
v8³ = var³ 8

v9³ : Tm
v9³ = var³ 9
