module AltArtemov.Term.Inversions where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import AltArtemov.Term.Core


var-inv-n : ∀ {n i n′ i′} → var[ n ] i ≡ var[ n′ ] i′ → n ≡ n′
var-inv-n refl = refl

var-inv-i : ∀ {n i n′ i′} → var[ n ] i ≡ var[ n′ ] i′ → i ≡ i′
var-inv-i refl = refl


lam-inv-n : ∀ {n t n′ t′} → lam[ n ] t ≡ lam[ n′ ] t′ → n ≡ n′
lam-inv-n refl = refl

lam-inv-t : ∀ {n t n′ t′} → lam[ n ] t ≡ lam[ n′ ] t′ → t ≡ t′
lam-inv-t refl = refl


app-inv-n : ∀ {n t s n′ t′ s′} → app[ n ] t s ≡ app[ n′ ] t′ s′ → n ≡ n′
app-inv-n refl = refl

app-inv-t : ∀ {n t s n′ t′ s′} → app[ n ] t s ≡ app[ n′ ] t′ s′ → t ≡ t′
app-inv-t refl = refl

app-inv-s : ∀ {n t s n′ t′ s′} → app[ n ] t s ≡ app[ n′ ] t′ s′ → s ≡ s′
app-inv-s refl = refl
