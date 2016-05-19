module AltArtemov.Context.OPE where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)

open import AltArtemov.Context.Core


data _≥_ : (Γ Γ′ : Cx) → Set where
  id   : ∀ {Γ} → Γ ≥ Γ
  weak : ∀ {Γ Γ′ A} → Γ′ ≥ Γ → (Γ′ , A) ≥ Γ
  lift : ∀ {Γ Γ′ A} → Γ′ ≥ Γ → (Γ′ , A) ≥ (Γ , A)


_•_ : ∀ {Γ Γ′ Γ″} → Γ″ ≥ Γ′ → Γ′ ≥ Γ → Γ″ ≥ Γ
id     • ρ′      = ρ′
weak ρ • ρ′      = weak (ρ • ρ′)
lift ρ • id      = lift ρ
lift ρ • weak ρ′ = weak (ρ • ρ′)
lift ρ • lift ρ′ = lift (ρ • ρ′)


ρ•id : ∀ {Γ Γ′} (ρ : Γ ≥ Γ′) → ρ • id ≡ ρ
ρ•id id       = refl
ρ•id (weak ρ) = cong weak (ρ•id ρ)
ρ•id (lift ρ) = refl

id•ρ : ∀ {Γ Γ′} (ρ : Γ ≥ Γ′) → id • ρ ≡ ρ
id•ρ id       = refl
id•ρ (weak ρ) = refl
id•ρ (lift ρ) = cong lift (id•ρ ρ)


•assoc : ∀ {Γ Γ′ Γ″ Γ‴} (ρ″ : Γ‴ ≥ Γ″) (ρ′ : Γ″ ≥ Γ′) (ρ : Γ′ ≥ Γ)
    → (ρ″ • ρ′) • ρ ≡ ρ″ • (ρ′ • ρ)
•assoc id        ρ′        ρ        = refl
•assoc (weak ρ″) ρ′        ρ        = cong weak (•assoc ρ″ ρ′ ρ)
•assoc (lift ρ″) id        ρ        = refl
•assoc (lift ρ″) (weak ρ′) ρ        = cong weak (•assoc ρ″ ρ′ ρ)
•assoc (lift ρ″) (lift ρ′) id       = refl
•assoc (lift ρ″) (lift ρ′) (weak ρ) = cong weak (•assoc ρ″ ρ′ ρ)
•assoc (lift ρ″) (lift ρ′) (lift ρ) = cong lift (•assoc ρ″ ρ′ ρ)
