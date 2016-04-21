module AltArtemov.Derivation.Core where

open import AltArtemov.Context
open import AltArtemov.Term
open import AltArtemov.TermVector
open import AltArtemov.Type


infixr 0 _⊢_

data _⊢_ (Γ : Cx) : ∀ (A : Ty) → Set where
  -- Variable reference.
  var[_] : ∀ n {A}
      → (i : Γ ∋ A)
      → Γ ⊢ VARs[ n ] (ix i) ∶⋯∶ A

  -- Lambda abstraction. (⊃I)
  lam[_] : ∀ n {ts : Tms n} {A B}
      → (d : Γ , A ⊢ ts ∶⋯∶ B)
      → Γ ⊢ LAMs[ n ] ts ∶⋯∶ (A ⊃ B)

  -- Function application. (⊃E)
  app[_] : ∀ n {ts ss : Tms n} {A B}
      → (d : Γ ⊢ ts ∶⋯∶ (A ⊃ B))    → (c : Γ ⊢ ss ∶⋯∶ A)
      → Γ ⊢ APPs[ n ] ts ss ∶⋯∶ B

  -- Reification.
  up[_] : ∀ n {ts : Tms n} {u A}
      → (d : Γ ⊢ ts ∶⋯∶ u ∶ A)
      → Γ ⊢ UPs[ n ] ts ∶⋯∶ quo u ∶ u ∶ A

  -- Reflection.
  down[_] : ∀ n {ts : Tms n} {u A}
      → (d : Γ ⊢ ts ∶⋯∶ u ∶ A)
      → Γ ⊢ DOWNs[ n ] ts ∶⋯∶ A

  -- Explosion. (⊥E)
  boom[_] : ∀ n {ts : Tms n} {A}
      → (d : Γ ⊢ ts ∶⋯∶ ⊥)
      → Γ ⊢ BOOMs[ n ] ts ∶⋯∶ A


infixr 0 ⊩_

⊩_ : ∀ (A : Ty) → Set
⊩ A = ∅ ⊢ A
