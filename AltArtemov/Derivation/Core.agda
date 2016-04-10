module AltArtemov.Derivation.Core where

open import AltArtemov.Context
open import AltArtemov.Term
open import AltArtemov.TermVector
open import AltArtemov.Type


infixr 0 _⊢_

data _⊢_ (Γ : Cx) : (A : Ty) → Set where
  -- Variable reference.
  VAR[_] : ∀ n {A}
      → (i : Γ ∋ A)
      → Γ ⊢ varⁿ[ n ] (ix i) ∶ⁿ A

  -- Lambda abstraction.
  LAM[_] : ∀ n {ts : TmV n} {A B}
      → (d : Γ , A ⊢ ts ∶ⁿ B)
      → Γ ⊢ lamⁿ[ n ] ts ∶ⁿ (A ⊃ B)

  -- Function application.
  APP[_] : ∀ n {ts ss : TmV n} {A B}
      → (d : Γ ⊢ ts ∶ⁿ (A ⊃ B))    → (c : Γ ⊢ ss ∶ⁿ A)
      → Γ ⊢ appⁿ[ n ] ts ss ∶ⁿ B

  -- Reification.
  UP[_] : ∀ n {ts : TmV n} {u A}
      → (d : Γ ⊢ ts ∶ⁿ u ∶ A)
      → Γ ⊢ upⁿ[ n ] ts ∶ⁿ quo u ∶ u ∶ A

  -- Reflection.
  DOWN[_] : ∀ n {ts : TmV n} {u A}
      → (d : Γ ⊢ ts ∶ⁿ u ∶ A)
      → Γ ⊢ downⁿ[ n ] ts ∶ⁿ A
