module AltArtemov.Term.Notation.Level4 where

open import AltArtemov.Term.Core


var⁴ : ∀ i → Tm
var⁴ i₄ = var[ 3 ] i₄

lam⁴ : ∀ t₄ → Tm
lam⁴ t₄ = lam[ 3 ] t₄

app⁴ : ∀ t₄ s₄ → Tm
app⁴ t₄ s₄ = app[ 3 ] t₄ s₄

up⁴ : ∀ t₄ → Tm
up⁴ t₄ = up[ 3 ] t₄

down⁴ : ∀ t₄ → Tm
down⁴ t₄ = down[ 3 ] t₄


v0⁴ : Tm
v0⁴ = var⁴ 0

v1⁴ : Tm
v1⁴ = var⁴ 1

v2⁴ : Tm
v2⁴ = var⁴ 2

v3⁴ : Tm
v3⁴ = var⁴ 3

v4⁴ : Tm
v4⁴ = var⁴ 4

v5⁴ : Tm
v5⁴ = var⁴ 5

v6⁴ : Tm
v6⁴ = var⁴ 6

v7⁴ : Tm
v7⁴ = var⁴ 7

v8⁴ : Tm
v8⁴ = var⁴ 8

v9⁴ : Tm
v9⁴ = var⁴ 9
