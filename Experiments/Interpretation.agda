module Experiments.Interpretation where

open import AltArtemov as AA using (Ty ; _⊃_ ; _∶_ ; Cx ; ∅ ; _,_ ; _∋_ ; Tm ; [] ; _∷_ ; _⊢_)
open import Experiments.Typing
open import Experiments.Shallow


level : ∀ (t : Tm) → ℕ
level (AA.VAR[ n ] i)   = n
level (AA.LAM[ n ] t)   = n
level (AA.APP[ n ] t s) = n
level (AA.UP[ n ] t)    = n
level (AA.DOWN[ n ] t)  = n

mutual
  power : ∀ (A : Set) (t : A) (n : ℕ) → Set
  power A t zero    = A
  power A t (suc n) = power A t n ▷ witness A t n

  witness : ∀ (A : Set) (t : A) (n : ℕ) → power A t n
  witness A t zero    = t
  witness A t (suc n) = [ witness A t n ]


-- TODO

mutual
  ⟦_⟧ᵗ : ∀ (A : Ty) → Set
  ⟦ AA.⊥ ⟧ᵗ = ⊥
  ⟦ A ⊃ B ⟧ᵗ = ⟦ A ⟧ᵗ → ⟦ B ⟧ᵗ
  ⟦ t ∶ A ⟧ᵗ = decode-ty t A

  ⟦_⟧ᶜ : ∀ (Γ : Cx) → Set
  ⟦ ∅ ⟧ᶜ     = ⊤
  ⟦ Γ , A ⟧ᶜ = ⟦ Γ ⟧ᶜ ∧ ⟦ A ⟧ᵗ

  ⟦_⟧∍ : ∀ {Γ : Cx} {A : Ty} (i : Γ ∋ A) (γ : ⟦ Γ ⟧ᶜ) → ⟦ A ⟧ᵗ
  ⟦ AA.top ⟧∍   (γ , a) = a
  ⟦ AA.pop i ⟧∍ (γ , b) = ⟦ i ⟧∍ γ

  decode-ty : ∀ (t : Tm) (A : Ty) → Set
  decode-ty t A = power ⟦ A ⟧ᵗ (decode-tm t unit ⟦ A ⟧ᵗ) (level t)

  decode-tm : ∀ {Γ : Cx} (t : Tm) (γ : ⟦ Γ ⟧ᶜ) (A : Set) → A
  decode-tm (AA.VAR[ n ] i)   γ A = {!!}
  decode-tm (AA.LAM[ n ] t)   γ A = {!!}
  decode-tm (AA.APP[ n ] t s) γ A = {!!}
  decode-tm (AA.UP[ n ] t)    γ A = {!!}
  decode-tm (AA.DOWN[ n ] t)  γ A = {!!}


⟦_⟧⊦ : ∀ {Γ : Cx} {A : Ty} (d : Γ ⊢ A) (γ : ⟦ Γ ⟧ᶜ) → ⟦ A ⟧ᵗ
⟦ AA.var[ zero ] i ⟧⊦              γ = ⟦ i ⟧∍ γ
⟦ AA.lam[ zero ] {[]} t ⟧⊦         γ = λ a → ⟦ t ⟧⊦ (γ , a)
⟦ AA.app[ zero ] {[]} {[]} t s ⟧⊦  γ = (⟦ t ⟧⊦ γ) (⟦ s ⟧⊦ γ)
⟦ AA.up[ zero ] {[]} t ⟧⊦          γ = {!!} -- up [ ⟦ u ⟧ᵗ ]
⟦ AA.down[ zero ] {[]} t ⟧⊦        γ = {!!} -- down ⟦ t ⟧⊦ γ
⟦ AA.var[ suc n ] i ⟧⊦             γ = {!!}
⟦ AA.lam[ suc n ] {ts} t ⟧⊦        γ = {!!}
⟦ AA.app[ suc n ] {ts} {ss} t s ⟧⊦ γ = {!!}
⟦ AA.up[ suc n ] {ts} t ⟧⊦         γ = {!!}
⟦ AA.down[ suc n ] {ts} t ⟧⊦       γ = {!!}
