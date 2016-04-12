module AltArtemov.Context.Properties where

open import Data.Nat using (ℕ ; zero ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)

open import AltArtemov.Context.Core


-- Context indices can be represented as naturals.
ix : ∀ {Γ A} (i : Γ ∋ A) → ℕ
ix top     = zero
ix (pop i) = suc (ix i)


-- Contexts can be weakened.
_++_ : ∀ Γ Δ → Cx
Γ ++ ∅       = Γ
Γ ++ (Δ , A) = Γ ++ Δ , A


-- Weakening a context preserves indices into the context.
weak-ix : ∀ Γ Δ {A} (i : ∅ ++ Γ ∋ A) → Δ ++ Γ ∋ A
weak-ix ∅       Δ ()
weak-ix (Γ , A) Δ top     = top
weak-ix (Γ , B) Δ (pop i) = pop (weak-ix Γ Δ i)


-- Weakening a context preserves the representation of indices into the context.
ix-weak-cx≡ix : ∀ Γ {Δ A} (i : ∅ ++ Γ ∋ A) → ix (weak-ix Γ Δ i) ≡ ix i
ix-weak-cx≡ix ∅       ()
ix-weak-cx≡ix (Γ , A) top     = refl
ix-weak-cx≡ix (Γ , A) (pop i) = cong suc (ix-weak-cx≡ix Γ i)
