module AltArtemov.WIP.TmSubst where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)

open import AltArtemov.Context
open import AltArtemov.Term.Core
open import AltArtemov.Term.Representation
open import AltArtemov.Type
open import AltArtemov.Variable

open import AltArtemov.Term.Substitution


∖-dist : ∀ {Γ X} → (x : X ∈ Γ) → ⌊ Γ ∖ᴳ x ⌋ᴳ ≡ ⌊ Γ ⌋ᴳ ∖ᵍ ⌊ x ⌋ˣ
∖-dist top     = refl
∖-dist (pop x) = cong _,◌ (∖-dist x)


wkⁱ′ : ∀ {Γ X} → (x : X ∈ Γ) → ◌∈ ⌊ Γ ∖ᴳ x ⌋ᴳ → ◌∈ ⌊ Γ ⌋ᴳ
wkⁱ′ x rewrite ∖-dist x = wkⁱ ⌊ x ⌋ˣ


wkᵗ′ : ∀ {Γ X} → (x : X ∈ Γ) → ⌊ Γ ∖ᴳ x ⌋ᴳ ⊢◌ → ⌊ Γ ⌋ᴳ ⊢◌
wkᵗ′ x rewrite ∖-dist x = wkᵗ ⌊ x ⌋ˣ


wkᵛ′ : ∀ {Γ X n} → (x : X ∈ Γ) → Vec ⌊ Γ ∖ᴳ x ⌋ᴳ n → Vec ⌊ Γ ⌋ᴳ n
wkᵛ′ x rewrite ∖-dist x = wkᵛ ⌊ x ⌋ˣ


wkᴬ′ : ∀ {Γ X} → (x : X ∈ Γ) → Ty ⌊ Γ ∖ᴳ x ⌋ᴳ → Ty ⌊ Γ ⌋ᴳ
wkᴬ′ x rewrite ∖-dist x = wkᴬ ⌊ x ⌋ˣ
