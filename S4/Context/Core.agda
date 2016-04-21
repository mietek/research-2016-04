module S4.Context.Core where

open import Data.Nat using (ℕ ; zero ; suc)

open import S4.Type


infixl 2 _,_
infixr 1 _∋_

data Cx : Set where
  instance ∅ : Cx
  _,_ : ∀ (Γ : Cx) (A : Ty) → Cx

data _∋_ : ∀ (Γ : Cx) (A : Ty) → Set where
  top : ∀ {Γ A} → Γ , A ∋ A
  pop : ∀ {Γ A B} (i : Γ ∋ A) → Γ , B ∋ A


ix : ∀ {Γ A} (i : Γ ∋ A) → ℕ
ix top     = zero
ix (pop i) = suc (ix i)
