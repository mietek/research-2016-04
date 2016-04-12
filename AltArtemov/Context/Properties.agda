module AltArtemov.Context.Properties where

open import Data.Nat using (ℕ ; zero ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)

open import AltArtemov.Context.Core


-- Context indices can be represented as naturals.
ix : ∀ {Γ A} (i : Γ ∋ A) → ℕ
ix top     = zero
ix (pop i) = suc (ix i)


-- Contexts can be concatenated.
_++_ : ∀ (Γ Δ : Cx) → Cx
Γ ++ ∅       = Γ
Γ ++ (Δ , A) = Γ ++ Δ , A


-- TODO: Rename this!
wk∋ : ∀ Γ {Δ A} (i : ∅ ++ Γ ∋ A) → Δ ++ Γ ∋ A
wk∋ ∅       ()
wk∋ (Γ , A) top     = top
wk∋ (Γ , B) (pop i) = pop (wk∋ Γ i)


-- TODO: Rename this!
fnord : ∀ Γ {Δ A} (i : ∅ ++ Γ ∋ A) → ix (wk∋ Γ {Δ} i) ≡ ix i
fnord ∅       ()
fnord (Γ , A) top     = refl
fnord (Γ , A) (pop i) = cong suc (fnord Γ i)
