module AltArtemov.Variable.Core where

open import Data.Fin using (Fin)
open import Function using (_∘_)

open import AltArtemov.Context
open import AltArtemov.Type
open import AltArtemov.Variable.Representation


data _∈_ (A : Ty ∅) : Cx → Set where
  top : ∀ {Γ} → A ∈ (Γ , A)
  pop : ∀ {Γ B} → A ∈ Γ → A ∈ (Γ , B)


⌊_⌋ˣ : ∀ {Γ A} → A ∈ Γ → ◌∈ ⌊ Γ ⌋ᴳ
⌊ top ⌋ˣ   = top
⌊ pop x ⌋ˣ = pop ⌊ x ⌋ˣ


⌊_⌋ˣ′ : ∀ {Γ A} → A ∈ Γ → Fin ⌊ Γ ⌋ᴳ′
⌊_⌋ˣ′ = ⌊_⌋ⁱ ∘ ⌊_⌋ˣ
