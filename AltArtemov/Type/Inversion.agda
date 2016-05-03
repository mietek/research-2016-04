module AltArtemov.Type.Inversion where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import AltArtemov.Term.Representation
open import AltArtemov.Type.Core


inv-∶-t : ∀ {g} {t t′ : g ⊢◌} {A A′ : Ty g} → t ∶ A ≡ t′ ∶ A′ → t ≡ t′
inv-∶-A : ∀ {g} {t t′ : g ⊢◌} {A A′ : Ty g} → t ∶ A ≡ t′ ∶ A′ → A ≡ A′
inv-∶-t refl = refl
inv-∶-A refl = refl

inv-⊃-A : ∀ {g} {A A′ B B′ : Ty g} → (A ⊃ B) ≡ (A′ ⊃ B′) → A ≡ A′
inv-⊃-B : ∀ {g} {A A′ B B′ : Ty g} → (A ⊃ B) ≡ (A′ ⊃ B′) → B ≡ B′
inv-⊃-A refl = refl
inv-⊃-B refl = refl

inv-∧-A : ∀ {g} {A A′ B B′ : Ty g} → (A ∧ B) ≡ (A′ ∧ B′) → A ≡ A′
inv-∧-B : ∀ {g} {A A′ B B′ : Ty g} → (A ∧ B) ≡ (A′ ∧ B′) → B ≡ B′
inv-∧-A refl = refl
inv-∧-B refl = refl
