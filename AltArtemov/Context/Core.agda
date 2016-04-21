module AltArtemov.Context.Core where

open import AltArtemov.Type


infixl 2 _,_
infixr 1 _∋_

data Cx : Set where
  instance ∅ : Cx
  _,_ : ∀ (Γ : Cx) (A : Ty) → Cx

data _∋_ : ∀ (Γ : Cx) (A : Ty) → Set where
  top : ∀ {Γ A} → Γ , A ∋ A
  pop : ∀ {Γ A B} (i : Γ ∋ A) → Γ , B ∋ A
