{-# OPTIONS --allow-unsolved-metas #-}

module AltArtemov.Term.Core where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import AltArtemov.Context
open import AltArtemov.Term.Representation
open import AltArtemov.Type
open import AltArtemov.Variable


infixr 15 _∴_

_∴_ : ∀ {g n} → Vec g n → Ty ∅ → Ty g
[]       ∴ A = wkᴬ* A
(t ∷ ts) ∴ A = t ∶ ts ∴ A


infix 0 _⊢_

data _⊢_ (Γ : Cx) : Ty ⌊ Γ ⌋ᴳ → Set where
  var[_] : (n : ℕ) {A : Ty ∅}
      → (x : A ∈ Γ)
      → Γ ⊢ VARs[ n ] ⌊ x ⌋ˣ ∴ A

  lam[_] : (n : ℕ) {A : Ty ∅} {ts : Vec ⌊ Γ , A ⌋ᴳ n} {B : Ty ∅}
      → Γ , A ⊢ ts ∴ B
      → Γ ⊢ LAMs[ n ] ts ∴ (A ⊃ B)

  app[_] : (n : ℕ) {ts us : Vec ⌊ Γ ⌋ᴳ n} {A B : Ty ∅}
      → Γ ⊢ ts ∴ (A ⊃ B)    → Γ ⊢ us ∴ A
      → Γ ⊢ APPs[ n ] ts us ∴ B

  pair[_] : (n : ℕ) {ts us : Vec ⌊ Γ ⌋ᴳ n} {A B : Ty ∅}
      → Γ ⊢ ts ∴ A    → Γ ⊢ us ∴ B
      → Γ ⊢ PAIRs[ n ] ts us ∴ (A ∧ B)

  fst[_] : (n : ℕ) {ts : Vec ⌊ Γ ⌋ᴳ n} {A B : Ty ∅}
      → Γ ⊢ ts ∴ (A ∧ B)
      → Γ ⊢ FSTs[ n ] ts ∴ A

  snd[_] : (n : ℕ) {ts : Vec ⌊ Γ ⌋ᴳ n} {A B : Ty ∅}
      → Γ ⊢ ts ∴ (A ∧ B)
      → Γ ⊢ SNDs[ n ] ts ∴ B

  up[_] : (n : ℕ) {ts : Vec ⌊ Γ ⌋ᴳ n} {s : ∅ ⊢◌} {A : Ty ∅}
      → Γ ⊢ ts ∴ s ∶ A
      → Γ ⊢ UPs[ n ] ts ∴ ! s ∶ s ∶ A

  down[_] : (n : ℕ) {ts : Vec ⌊ Γ ⌋ᴳ n} {s : ∅ ⊢◌} {A : Ty ∅}
      → Γ ⊢ ts ∴ s ∶ A
      → Γ ⊢ DOWNs[ n ] ts ∴ A

  boom[_] : (n : ℕ) {ts : Vec ⌊ Γ ⌋ᴳ n} {C : Ty ∅}
      → Γ ⊢ ts ∴ ⊥
      → Γ ⊢ BOOMs[ n ] ts ∴ C


data Ne (Ξ : (Δ : Cx) → Ty ⌊ Δ ⌋ᴳ → Set) (Γ : Cx) : Ty ⌊ Γ ⌋ᴳ → Set where
  var[_] : (n : ℕ) {A : Ty ∅}
      → (x : A ∈ Γ)
      → Ne Ξ Γ (VARs[ n ] ⌊ x ⌋ˣ ∴ A)

  app[_] : (n : ℕ) {ts us : Vec ⌊ Γ ⌋ᴳ n} {A B : Ty ∅}
      → Ne Ξ Γ (ts ∴ (A ⊃ B))    → Ξ Γ (us ∴ A)
      → Ne Ξ Γ (APPs[ n ] ts us ∴ B)

  fst[_] : (n : ℕ) {ts : Vec ⌊ Γ ⌋ᴳ n} {A B : Ty ∅}
      → Ne Ξ Γ (ts ∴ (A ∧ B))
      → Ne Ξ Γ (FSTs[ n ] ts ∴ A)

  snd[_] : (n : ℕ) {ts : Vec ⌊ Γ ⌋ᴳ n} {A B : Ty ∅}
      → Ne Ξ Γ (ts ∴ (A ∧ B))
      → Ne Ξ Γ (SNDs[ n ] ts ∴ B)

  boom[_] : (n : ℕ) {ts : Vec ⌊ Γ ⌋ᴳ n} {C : Ty ∅}
      → Ne Ξ Γ (ts ∴ ⊥)
      → Ne Ξ Γ (BOOMs[ n ] ts ∴ C)


data Nf (Δ : Cx) : Ty ⌊ Δ ⌋ᴳ → Set where
  ne : Ne Nf Δ ★ → Nf Δ ★

  lam[_] : (n : ℕ) {A : Ty ∅} {ts : Vec ⌊ Δ , A ⌋ᴳ n} {B : Ty ∅}
      → Nf (Δ , A) (ts ∴ B)
      → Nf Δ (LAMs[ n ] ts ∴ (A ⊃ B))

  pair[_] : (n : ℕ) {ts us : Vec ⌊ Δ ⌋ᴳ n} {A B : Ty ∅}
      → Nf Δ (ts ∴ A)    → Nf Δ (us ∴ B)
      → Nf Δ (PAIRs[ n ] ts us ∴ (A ∧ B))


-- TODO: unfinished
mutual
  data Val (Δ : Cx) : Ty ⌊ Δ ⌋ᴳ → Set where
    ne : ∀ {A} → Ne Val Δ A → Val Δ A

    lam[_] : (n : ℕ) {Γ : Cx} {A : Ty ∅} {ts : Vec ⌊ Γ , A ⌋ᴳ n} {B : Ty ∅}
        → Γ , A ⊢ ts ∴ B    → Env Δ Γ
        → Val Δ {!LAMs[ n ] ts ∴ (A ⊃ B)!}

    pair[_] : (n : ℕ) {ts us : Vec ⌊ Δ ⌋ᴳ n} {A B : Ty ∅}
        → Val Δ (ts ∴ A)    → Val Δ (us ∴ B)
        → Val Δ (PAIRs[ n ] ts us ∴ (A ∧ B))

  data Env (Δ : Cx) : Cx → Set where
    ∅   : Env Δ ∅
    _,_ : ∀ {Γ} {A : Ty ∅} → Env Δ Γ → Val Δ (wkᴬ* A) → Env Δ (Γ , A)


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
