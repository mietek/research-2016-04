module AltArtemov.Type.Inversions where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import AltArtemov.Type.Core


⊃-inv-A : ∀ {A B A′ B′} → (A ⊃ B) ≡ (A′ ⊃ B′) → A ≡ A′
⊃-inv-A refl = refl

⊃-inv-B : ∀ {A B A′ B′} → (A ⊃ B) ≡ (A′ ⊃ B′) → B ≡ B′
⊃-inv-B refl = refl


∧-inv-A : ∀ {A B A′ B′} → (A ∧ B) ≡ (A′ ∧ B′) → A ≡ A′
∧-inv-A refl = refl

∧-inv-B : ∀ {A B A′ B′} → (A ∧ B) ≡ (A′ ∧ B′) → B ≡ B′
∧-inv-B refl = refl


∶-inv-t : ∀ {t A t′ A′} → (t ∶ A) ≡ (t′ ∶ A′) → t ≡ t′
∶-inv-t refl = refl

∶-inv-A : ∀ {t A t′ A′} → (t ∶ A) ≡ (t′ ∶ A′) → A ≡ A′
∶-inv-A refl = refl
