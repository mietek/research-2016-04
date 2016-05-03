module AltArtemov.Term.Core where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import AltArtemov.Context
open import AltArtemov.Term.Representation
open import AltArtemov.Type
open import AltArtemov.Variable

open import AltArtemov.WIP.TySubst#


infix 0 _⊢_

data _⊢_ (Γ : Cx) : Ty ⌊ Γ ⌋ᴳ → Set where
  var[_] : (n : ℕ) → {A : Ty ∅} → {Z : Ty ⌊ Γ ⌋ᴳ}
      → (x : A ∈ Γ)
      → {{_ : VARs[ n ] ⌊ x ⌋ˣ ∴ A ≡ Z}}
      → Γ ⊢ Z

  lam[_] : (n : ℕ) → {A : Ty ∅} → {ts : Vec ⌊ Γ , A ⌋ᴳ n} → {B : Ty ∅} → {Z : Ty ⌊ Γ ⌋ᴳ}
      → Γ , A ⊢ ts ∴ B
      → {{_ : LAMs[ n ] ts ∴ (A ⊃ B) ≡ Z}}
      → Γ ⊢ Z

  app[_] : (n : ℕ) → {ts us : Vec ⌊ Γ ⌋ᴳ n} → {A B : Ty ∅} → {Z : Ty ⌊ Γ ⌋ᴳ}
      → Γ ⊢ ts ∴ (A ⊃ B)    → Γ ⊢ us ∴ A
      → {{_ : APPs[ n ] ts us ∴ B ≡ Z}}
      → Γ ⊢ Z

  pair[_] : (n : ℕ) → {ts us : Vec ⌊ Γ ⌋ᴳ n} → {A B : Ty ∅} → {Z : Ty ⌊ Γ ⌋ᴳ}
      → Γ ⊢ ts ∴ A    → Γ ⊢ us ∴ B
      → {{_ : PAIRs[ n ] ts us ∴ (A ∧ B) ≡ Z}}
      → Γ ⊢ Z

  fst[_] : (n : ℕ) → {ts : Vec ⌊ Γ ⌋ᴳ n} → {A B : Ty ∅} → {Z : Ty ⌊ Γ ⌋ᴳ}
      → Γ ⊢ ts ∴ (A ∧ B)
      → {{_ : FSTs[ n ] ts ∴ A ≡ Z}}
      → Γ ⊢ Z

  snd[_] : (n : ℕ) → {ts : Vec ⌊ Γ ⌋ᴳ n} → {A B : Ty ∅} → {Z : Ty ⌊ Γ ⌋ᴳ}
      → Γ ⊢ ts ∴ (A ∧ B)
      → {{_ : SNDs[ n ] ts ∴ B ≡ Z}}
      → Γ ⊢ Z

  up[_] : (n : ℕ) → {ts : Vec ⌊ Γ ⌋ᴳ n} → {s : ∅ ⊢◌} → {A : Ty ∅} → {Z : Ty ⌊ Γ ⌋ᴳ}
      → Γ ⊢ ts ∴ s ∶ A
      → {{_ : UPs[ n ] ts ∴ ! s ∶ s ∶ A ≡ Z}}
      → Γ ⊢ Z

  down[_] : (n : ℕ) → {ts : Vec ⌊ Γ ⌋ᴳ n} → {s : ∅ ⊢◌} → {A : Ty ∅} → {Z : Ty ⌊ Γ ⌋ᴳ}
      → Γ ⊢ ts ∴ s ∶ A
      → {{_ : DOWNs[ n ] ts ∴ A ≡ Z}}
      → Γ ⊢ Z

  boom[_] : (n : ℕ) → {ts : Vec ⌊ Γ ⌋ᴳ n} → {A : Ty ∅} → {Z : Ty ⌊ Γ ⌋ᴳ}
      → Γ ⊢ ts ∴ ⊥
      → {{_ : BOOMs[ n ] ts ∴ A ≡ Z}}
      → Γ ⊢ Z


⌊_⌋ᵈ : ∀ {Γ A} → Γ ⊢ A → ⌊ Γ ⌋ᴳ ⊢◌
⌊ var[ n ] x ⌋ᵈ    = VAR[ n ] ⌊ x ⌋ˣ
⌊ lam[ n ] d ⌋ᵈ    = LAM[ n ] ⌊ d ⌋ᵈ
⌊ app[ n ] d e ⌋ᵈ  = APP[ n ] ⌊ d ⌋ᵈ ⌊ e ⌋ᵈ
⌊ pair[ n ] d e ⌋ᵈ = PAIR[ n ] ⌊ d ⌋ᵈ ⌊ e ⌋ᵈ
⌊ fst[ n ] d ⌋ᵈ    = FST[ n ] ⌊ d ⌋ᵈ
⌊ snd[ n ] d ⌋ᵈ    = SND[ n ] ⌊ d ⌋ᵈ
⌊ up[ n ] d ⌋ᵈ     = UP[ n ] ⌊ d ⌋ᵈ
⌊ down[ n ] d ⌋ᵈ   = DOWN[ n ] ⌊ d ⌋ᵈ
⌊ boom[ n ] d ⌋ᵈ   = BOOM[ n ] ⌊ d ⌋ᵈ
