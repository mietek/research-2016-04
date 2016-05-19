module AltArtemov.WIP.Evaluation where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import AltArtemov.Context
open import AltArtemov.Type
open import AltArtemov.Term
open import AltArtemov.Variable

open import AltArtemov.WIP.TySubst#


data Ne (Ξ : (Γ : Cx) → Ty ⌊ Γ ⌋ᴳ → Set) (Γ : Cx) : Ty ⌊ Γ ⌋ᴳ → Set where
  var[_] : (n : ℕ) {A : Ty ∅} →
           (x : A ∈ Γ) →
           Ne Ξ Γ (VARs[ n ] ⌊ x ⌋ˣ ∴ A)

  app[_] : (n : ℕ) {ts us : Vec ⌊ Γ ⌋ᴳ n} {A B : Ty ∅} →
           Ne Ξ Γ (ts ∴ (A ⊃ B))    → Ξ Γ (us ∴ A) →
           Ne Ξ Γ (APPs[ n ] ts us ∴ B)

  fst[_] : (n : ℕ) {ts : Vec ⌊ Γ ⌋ᴳ n} {A B : Ty ∅} →
           Ne Ξ Γ (ts ∴ (A ∧ B)) →
           Ne Ξ Γ (FSTs[ n ] ts ∴ A)

  snd[_] : (n : ℕ) {ts : Vec ⌊ Γ ⌋ᴳ n} {A B : Ty ∅} →
           Ne Ξ Γ (ts ∴ (A ∧ B)) →
           Ne Ξ Γ (SNDs[ n ] ts ∴ B)

  down[_] : (n : ℕ) {ts : Vec ⌊ Γ ⌋ᴳ n} {s : ∅ ⊢◌} {A : Ty ∅} →
            Ne Ξ Γ (ts ∴ s ∶ A) →
            Ne Ξ Γ (DOWNs[ n ] ts ∴ A)

  boom[_] : (n : ℕ) {ts : Vec ⌊ Γ ⌋ᴳ n} {A : Ty ∅} →
            Ne Ξ Γ (ts ∴ ⊥) →
            Ne Ξ Γ (BOOMs[ n ] ts ∴ A)


postulate
  magic-rename : ∀ {Γ Δ} → Ty Γ → Ty Δ


mutual
  data Whnf (Δ : Cx) : Ty ⌊ Δ ⌋ᴳ → Set where
    ne : ∀ {A : Ty ⌊ Δ ⌋ᴳ} → Ne Whnf Δ A →
         Whnf Δ A

    lam[_] : ∀ {Γ} (n : ℕ) {A : Ty ∅} {ts : Vec ⌊ Γ , A ⌋ᴳ n} {B : Ty ∅} →
             Γ , A ⊢ ts ∴ B    → Env Δ Γ →
             Whnf Δ (magic-rename (LAMs[ n ] ts ∴ (A ⊃ B)))

    pair[_] : (n : ℕ) {ts us : Vec ⌊ Δ ⌋ᴳ n} {A B : Ty ∅} →
              Δ ⊢ ts ∴ A    → Δ ⊢ us ∴ B →
              Whnf Δ (PAIRs[ n ] ts us ∴ (A ∧ B))

    up[_] : (n : ℕ) {ts : Vec ⌊ Δ ⌋ᴳ n} {s : ∅ ⊢◌} {A : Ty ∅} →
            Δ ⊢ ts ∴ s ∶ A →
            Whnf Δ (UPs[ n ] ts ∴ ! s ∶ s ∶ A)

  data Env (Δ : Cx) : Cx → Set where
    ∅   : Env Δ ∅
    _,_ : ∀ {Γ} {A : Ty ∅} → Env Δ Γ → Whnf Δ (magic-rename A) → Env Δ (Γ , A)


data Nf (Γ : Cx) : Ty ⌊ Γ ⌋ᴳ → Set where
  ne : ∀ {A : Ty ⌊ Γ ⌋ᴳ} → Ne Nf Γ A →
       Nf Γ A

  lam[_] : (n : ℕ) {A : Ty ∅} {ts : Vec ⌊ Γ , A ⌋ᴳ n} {B : Ty ∅} →
           Nf (Γ , A) (ts ∴ B) →
           Nf Γ (LAMs[ n ] ts ∴ (A ⊃ B))

  pair[_] : (n : ℕ) {ts us : Vec ⌊ Γ ⌋ᴳ n} {A B : Ty ∅} →
            Nf Γ (ts ∴ A)    → Nf Γ (us ∴ B) →
            Nf Γ (PAIRs[ n ] ts us ∴ (A ∧ B))

  up[_] : (n : ℕ) {ts : Vec ⌊ Γ ⌋ᴳ n} {s : ∅ ⊢◌} {A : Ty ∅} →
          Nf Γ (ts ∴ s ∶ A) →
          Nf Γ (UPs[ n ] ts ∴ ! s ∶ s ∶ A)
