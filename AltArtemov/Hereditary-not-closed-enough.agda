module AltArtemov.Hereditary where

open import Data.Fin using (Fin ; zero ; suc)
open import Data.Nat using (ℕ ; zero ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.PropositionalEquality as ≡


-- Terms

data Tm (g : ℕ) : Set where
  VAR[_]  : ℕ → Fin g → Tm g
  LAM[_]  : ℕ → Tm (suc g) → Tm g
  APP[_]  : ℕ → Tm g → Tm g → Tm g
  PAIR[_] : ℕ → Tm g → Tm g → Tm g
  FST[_]  : ℕ → Tm g → Tm g
  SND[_]  : ℕ → Tm g → Tm g
  UP[_]   : ℕ → Tm g → Tm g
  DOWN[_] : ℕ → Tm g → Tm g
  BOOM[_] : ℕ → Tm g → Tm g
  !_      : Tm g → Tm g


module tm where
  infixl 4 _-ᵛ_

  _-ᵛ_ : (g : ℕ) → Fin g → ℕ
  zero -ᵛ ()
  suc g -ᵛ zero  = g
  suc g -ᵛ suc i = suc (g -ᵛ i)

  wkᵛ : ∀ {g} → (i : Fin g) → Fin (g -ᵛ i) → Fin g
  wkᵛ zero j          = suc j
  wkᵛ (suc i) zero    = zero
  wkᵛ (suc i) (suc j) = suc (wkᵛ i j)

  data _=ᵛ_ {g : ℕ} : Fin g → Fin g → Set where
    same : {i : Fin g} → i =ᵛ i
    diff : (i : Fin g) → (j : Fin (g -ᵛ i)) → i =ᵛ wkᵛ i j

  _=ᵛ?_ : ∀ {g} → (i : Fin g) → (j : Fin g) → i =ᵛ j
  zero =ᵛ? zero            = same
  zero =ᵛ? suc j           = diff zero j
  suc i =ᵛ? zero           = diff (suc i) zero
  suc i =ᵛ? suc j          with i =ᵛ? j
  suc i =ᵛ? suc .i         | same = same
  suc i =ᵛ? suc .(wkᵛ i j) | diff .i j = diff (suc i) (suc j)

  wk : ∀ {g} → (i : Fin g) → Tm (g -ᵛ i) → Tm g
  wk i (VAR[ n ] v)    = VAR[ n ] (wkᵛ i v)
  wk i (LAM[ n ] t)    = LAM[ n ] (wk (suc i) t)
  wk i (APP[ n ] t u)  = APP[ n ] (wk i t) (wk i u)
  wk i (PAIR[ n ] t u) = PAIR[ n ] (wk i t) (wk i u)
  wk i (FST[ n ] t)    = FST[ n ] (wk i t)
  wk i (SND[ n ] t)    = SND[ n ] (wk i t)
  wk i (UP[ n ] t)     = UP[ n ] (wk i t)
  wk i (DOWN[ n ] t)   = DOWN[ n ] (wk i t)
  wk i (BOOM[ n ] t)   = BOOM[ n ] (wk i t)
  wk i (! t)           = ! (wk i t)

  substᵛ : ∀ {g} → ℕ → Fin g → (i : Fin g) → Tm (g -ᵛ i) → Tm (g -ᵛ i)
  substᵛ n v i s          with i =ᵛ? v
  substᵛ n v .v s         | same = s
  substᵛ n .(wkᵛ v i) v s | diff .v i = VAR[ n ] i

  subst : ∀ {g} → Tm g → (i : Fin g) → Tm (g -ᵛ i) → Tm (g -ᵛ i)
  subst (VAR[ n ] v) i s    = substᵛ n v i s
  subst (LAM[ n ] t) i s    = LAM[ n ] (subst t (suc i) (wk zero s))
  subst (APP[ n ] t u) i s  = APP[ n ] (subst t i s) (subst u i s)
  subst (PAIR[ n ] t u) i s = PAIR[ n ] (subst t i s) (subst u i s)
  subst (FST[ n ] t) i s    = FST[ n ] (subst t i s)
  subst (SND[ n ] t) i s    = SND[ n ] (subst t i s)
  subst (UP[ n ] t) i s     = UP[ n ] (subst t i s)
  subst (DOWN[ n ] t) i s   = DOWN[ n ] (subst t i s)
  subst (BOOM[ n ] t) i s   = BOOM[ n ] (subst t i s)
  subst (! t) i s           = ! subst t i s

  data _⇔_ {g : ℕ} : Tm g → Tm g → Set where
    refl      : {t : Tm g} → t ⇔ t
    sym       : {t t′ : Tm g} → t ⇔ t′ → t′ ⇔ t
    trans     : {t t′ t″ : Tm g} → t ⇔ t′ → t′ ⇔ t″ → t ⇔ t″
    cong-LAM  : ∀ {n} → {t t′ : Tm (suc g)} → t ⇔ t′ → LAM[ n ] t ⇔ LAM[ n ] t′
    cong-APP  : ∀ {n} → {t t′ u u′ : Tm g} → t ⇔ t′ → u ⇔ u′ → APP[ n ] t u ⇔ APP[ n ] t′ u′
    cong-PAIR : ∀ {n} → {t t′ u u′ : Tm g} → t ⇔ t′ → u ⇔ u′ → PAIR[ n ] t u ⇔ PAIR[ n ] t′ u′
    cong-FST  : ∀ {n} → {t t′ : Tm g} → t ⇔ t′ → FST[ n ] t ⇔ FST[ n ] t′
    cong-SND  : ∀ {n} → {t t′ : Tm g} → t ⇔ t′ → SND[ n ] t ⇔ SND[ n ] t′
    cong-UP   : ∀ {n} → {t t′ : Tm g} → t ⇔ t′ → UP[ n ] t ⇔ UP[ n ] t′
    cong-DOWN : ∀ {n} → {t t′ : Tm g} → t ⇔ t′ → DOWN[ n ] t ⇔ DOWN[ n ] t′
    cong-BOOM : ∀ {n} → {t t′ : Tm g} → t ⇔ t′ → BOOM[ n ] t ⇔ BOOM[ n ] t′
    red-APP   : ∀ {n} → {t : Tm (suc g)} → {u : Tm g} → APP[ n ] (LAM[ n ] t) u ⇔ subst t zero u
    exp-LAM   : ∀ {n} → {t : Tm g} → LAM[ n ] (APP[ n ] (wk zero t) (VAR[ n ] zero)) ⇔ t
    red-FST   : ∀ {n} → {t u : Tm g} → FST[ n ] (PAIR[ n ] t u) ⇔ t
    red-SND   : ∀ {n} → {t u : Tm g} → SND[ n ] (PAIR[ n ] t u) ⇔ u
    exp-PAIR  : ∀ {n} → {t : Tm g} → PAIR[ n ] (FST[ n ] t) (SND[ n ] t) ⇔ t
    red-DOWN  : ∀ {n} → {t : Tm g} → DOWN[ n ] (UP[ n ] t) ⇔ t
    exp-UP    : ∀ {n} → {t : Tm g} → UP[ n ] (DOWN[ n ] t) ⇔ t


-- Types

infixr 2 _⊃_
infixr 5 _∶_

data Ty (g : ℕ) : Set where
  _⊃_ : Ty g → Ty (suc g) → Ty g
  _∧_ : Ty g → Ty g → Ty g
  _∶_ : Tm g → Ty g → Ty g
  ⊥  : Ty g

⊤ : ∀ {g} → Ty g
⊤ = ⊥ ⊃ ⊥

¬_ : ∀ {g} → Ty g → Ty g
¬ A = A ⊃ ⊥


module ty where
  open tm using (_-ᵛ_)

  wk : ∀ {g} → (i : Fin g) → Ty (g -ᵛ i) → Ty g
  wk i (A ⊃ B) = wk i A ⊃ wk (suc i) B
  wk i (A ∧ B) = wk i A ∧ wk i B
  wk i (t ∶ A) = tm.wk i t ∶ wk i A
  wk i ⊥      = ⊥

  subst : ∀ {g} → Ty g → (i : Fin g) → Tm (g -ᵛ i) → Ty (g -ᵛ i)
  subst (A ⊃ B) i s = subst A i s ⊃ subst B (suc i) (tm.wk zero s)
  subst (A ∧ B) i s = subst A i s ∧ subst B i s
  subst (t ∶ A) i s = tm.subst t i s ∶ subst A i s
  subst ⊥ i s      = ⊥

_⫗_ : ∀ {g} → Ty g → Ty g → Ty g
A ⫗ B = (A ⊃ ty.wk zero B) ∧ (B ⊃ ty.wk zero A)


-- Term vectors

infixr 5 _∷_

data Tms (g : ℕ) : ℕ → Set where
  []  : Tms g zero
  _∷_ : ∀ {n} → Tm g → Tms g n → Tms g (suc n)

tms : ∀ {g} → (ℕ → Tm g → Tm g) → (n : ℕ) → Tms g n → Tms g n
tms f zero []          = []
tms f (suc n) (t ∷ ts) = f n t ∷ tms f n ts

tms₂ : ∀ {g} → (ℕ → Tm g → Tm g → Tm g) → (n : ℕ) → Tms g n → Tms g n → Tms g n
tms₂ f zero [] []                 = []
tms₂ f (suc n)  (t ∷ ts) (u ∷ us) = f n t u ∷ tms₂ f n ts us


-- Term vector notation

VARs[_] : ∀ {g} → (n : ℕ) → Fin g → Tms g n
VARs[ zero ] i  = []
VARs[ suc n ] i = VAR[ n ] i ∷ VARs[ n ] i

LAMs[_] : ∀ {g} → (n : ℕ) → Tms (suc g) n → Tms g n
LAMs[ zero ] []        = []
LAMs[ suc n ] (t ∷ ts) = LAM[ n ] t ∷ LAMs[ n ] ts

APPs[_]  : ∀ {g} → (n : ℕ) → Tms g n → Tms g n → Tms g n
PAIRs[_] : ∀ {g} → (n : ℕ) → Tms g n → Tms g n → Tms g n
APPs[_]  = tms₂ APP[_]
PAIRs[_] = tms₂ PAIR[_]

FSTs[_]  : ∀ {g} → (n : ℕ) → Tms g n → Tms g n
SNDs[_]  : ∀ {g} → (n : ℕ) → Tms g n → Tms g n
UPs[_]   : ∀ {g} → (n : ℕ) → Tms g n → Tms g n
DOWNs[_] : ∀ {g} → (n : ℕ) → Tms g n → Tms g n
BOOMs[_] : ∀ {g} → (n : ℕ) → Tms g n → Tms g n
FSTs[_]  = tms FST[_]
SNDs[_]  = tms SND[_]
UPs[_]   = tms UP[_]
DOWNs[_] = tms DOWN[_]
BOOMs[_] = tms BOOM[_]


-- Contexts

infixl 2 _,_

mutual
  data Cx : Set where
    ∅   : Cx
    _,_ : (Γ : Cx) → Ty ⌊ Γ ⌋ᶜ → Cx

  ⌊_⌋ᶜ : Cx → ℕ
  ⌊ ∅ ⌋ᶜ     = zero
  ⌊ Γ , A ⌋ᶜ = suc ⌊ Γ ⌋ᶜ


-- Variables

infixr 1 _∋_

data _∋_ : (Γ : Cx) → Ty ⌊ Γ ⌋ᶜ → Set where
  top : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → Γ , A ∋ ty.wk zero A
  pop : ∀ {Γ} → {A B : Ty ⌊ Γ ⌋ᶜ} → Γ ∋ A → Γ , B ∋ ty.wk zero A

⌊_⌋ᵛ : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → Γ ∋ A → Fin ⌊ Γ ⌋ᶜ
⌊ top ⌋ᵛ   = zero
⌊ pop i ⌋ᵛ = suc ⌊ i ⌋ᵛ


-- Derivations

infixr 5 _∴_

_∴_ : ∀ {g n} → Tms g n → Ty g → Ty g
[] ∴ A       = A
(t ∷ ts) ∴ A = t ∶ ts ∴ A

infix 0 _⊢_

mutual
  data _⊢_ (Γ : Cx) : Ty ⌊ Γ ⌋ᶜ → Set where
    var[_] : (n : ℕ) → {A : Ty ⌊ Γ ⌋ᶜ}
        → (v : Γ ∋ A)
        → Γ ⊢ VARs[ n ] ⌊ v ⌋ᵛ ∴ A

    lam[_] : (n : ℕ) → {A : Ty ⌊ Γ ⌋ᶜ} → {ts : Tms (suc ⌊ Γ ⌋ᶜ) n} → {B : Ty (suc ⌊ Γ ⌋ᶜ)}
        → Γ , A ⊢ ts ∴ B
        → Γ ⊢ LAMs[ n ] ts ∴ (A ⊃ B)

    app[_] : (n : ℕ) → {ts us : Tms ⌊ Γ ⌋ᶜ n} → {A : Ty ⌊ Γ ⌋ᶜ} → {B : Ty (suc ⌊ Γ ⌋ᶜ)}
        → Γ ⊢ ts ∴ (A ⊃ B)    → (e : Γ ⊢ us ∴ A)
        → Γ ⊢ APPs[ n ] ts us ∴ ty.subst B zero ⌊ e ⌋

    pair[_] : (n : ℕ) → {ts us : Tms ⌊ Γ ⌋ᶜ n} → {A B : Ty ⌊ Γ ⌋ᶜ}
        → Γ ⊢ ts ∴ A    → Γ ⊢ us ∴ B
        → Γ ⊢ PAIRs[ n ] ts us ∴ (A ∧ B)

    fst[_] : (n : ℕ) → {ts : Tms ⌊ Γ ⌋ᶜ n} → {A B : Ty ⌊ Γ ⌋ᶜ}
        → Γ ⊢ ts ∴ (A ∧ B)
        → Γ ⊢ FSTs[ n ] ts ∴ A

    snd[_] : (n : ℕ) → {ts : Tms ⌊ Γ ⌋ᶜ n} → {A B : Ty ⌊ Γ ⌋ᶜ}
        → Γ ⊢ ts ∴ (A ∧ B)
        → Γ ⊢ SNDs[ n ] ts ∴ B

    up[_] : (n : ℕ) → {ts : Tms ⌊ Γ ⌋ᶜ n} → {u : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ}
        → Γ ⊢ ts ∴ u ∶ A
        → Γ ⊢ UPs[ n ] ts ∴ ! u ∶ u ∶ A

    down[_] : (n : ℕ) → {ts : Tms ⌊ Γ ⌋ᶜ n} → {u : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ}
        → Γ ⊢ ts ∴ u ∶ A
        → Γ ⊢ DOWNs[ n ] ts ∴ A

    boom[_] : (n : ℕ) → {ts : Tms ⌊ Γ ⌋ᶜ n} → {A : Ty ⌊ Γ ⌋ᶜ}
        → Γ ⊢ ts ∴ ⊥
        → Γ ⊢ BOOMs[ n ] ts ∴ A

  ⌊_⌋ : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → Γ ⊢ A → Tm ⌊ Γ ⌋ᶜ
  ⌊ var[ n ] v ⌋    = VAR[ n ] ⌊ v ⌋ᵛ
  ⌊ lam[ n ] d ⌋    = LAM[ n ] ⌊ d ⌋
  ⌊ app[ n ] d e ⌋  = APP[ n ] ⌊ d ⌋ ⌊ e ⌋
  ⌊ pair[ n ] d e ⌋ = PAIR[ n ] ⌊ d ⌋ ⌊ e ⌋
  ⌊ fst[ n ] d ⌋    = FST[ n ] ⌊ d ⌋
  ⌊ snd[ n ] d ⌋    = SND[ n ] ⌊ d ⌋
  ⌊ up[ n ] d ⌋     = UP[ n ] ⌊ d ⌋
  ⌊ down[ n ] d ⌋   = DOWN[ n ] ⌊ d ⌋
  ⌊ boom[ n ] d ⌋   = BOOM[ n ] ⌊ d ⌋


module dn where
  infixl 4 _-ᵛ_

  _-ᵛ_ : (Γ : Cx) → {A : Ty ⌊ Γ ⌋ᶜ} → Γ ∋ A → Cx
  ∅ -ᵛ ()
  (Γ , A) -ᵛ top   = Γ
  (Γ , B) -ᵛ pop x = Γ -ᵛ x , {!B!}


-- -- Term notation

-- VAR  : ∀ {g} → Fin g → Tm g
-- LAM  : ∀ {g} → Tm (suc g) → Tm g
-- APP  : ∀ {g} → Tm g → Tm g → Tm g
-- PAIR : ∀ {g} → Tm g → Tm g → Tm g
-- FST  : ∀ {g} → Tm g → Tm g
-- SND  : ∀ {g} → Tm g → Tm g
-- UP   : ∀ {g} → Tm g → Tm g
-- DOWN : ∀ {g} → Tm g → Tm g
-- BOOM : ∀ {g} → Tm g → Tm g
-- VAR  = VAR[ 0 ]
-- LAM  = LAM[ 0 ]
-- APP  = APP[ 0 ]
-- PAIR = PAIR[ 0 ]
-- FST  = FST[ 0 ]
-- SND  = SND[ 0 ]
-- UP   = UP[ 0 ]
-- DOWN = DOWN[ 0 ]
-- BOOM = BOOM[ 0 ]

-- VAR²  : ∀ {g} → Fin g → Tm g
-- LAM²  : ∀ {g} → Tm (suc g) → Tm g
-- APP²  : ∀ {g} → Tm g → Tm g → Tm g
-- PAIR² : ∀ {g} → Tm g → Tm g → Tm g
-- FST²  : ∀ {g} → Tm g → Tm g
-- SND²  : ∀ {g} → Tm g → Tm g
-- UP²   : ∀ {g} → Tm g → Tm g
-- DOWN² : ∀ {g} → Tm g → Tm g
-- BOOM² : ∀ {g} → Tm g → Tm g
-- VAR²  = VAR[ 1 ]
-- LAM²  = LAM[ 1 ]
-- APP²  = APP[ 1 ]
-- PAIR² = PAIR[ 1 ]
-- FST²  = FST[ 1 ]
-- SND²  = SND[ 1 ]
-- UP²   = UP[ 1 ]
-- DOWN² = DOWN[ 1 ]
-- BOOM² = BOOM[ 1 ]

-- VAR³  : ∀ {g} → Fin g → Tm g
-- LAM³  : ∀ {g} → Tm (suc g) → Tm g
-- APP³  : ∀ {g} → Tm g → Tm g → Tm g
-- PAIR³ : ∀ {g} → Tm g → Tm g → Tm g
-- FST³  : ∀ {g} → Tm g → Tm g
-- SND³  : ∀ {g} → Tm g → Tm g
-- UP³   : ∀ {g} → Tm g → Tm g
-- DOWN³ : ∀ {g} → Tm g → Tm g
-- BOOM³ : ∀ {g} → Tm g → Tm g
-- VAR³  = VAR[ 2 ]
-- LAM³  = LAM[ 2 ]
-- APP³  = APP[ 2 ]
-- PAIR³ = PAIR[ 2 ]
-- FST³  = FST[ 2 ]
-- SND³  = SND[ 2 ]
-- UP³   = UP[ 2 ]
-- DOWN³ = DOWN[ 2 ]
-- BOOM³ = BOOM[ 2 ]

-- V0 : ∀ {g} → Tm (suc g)
-- V1 : ∀ {g} → Tm (suc (suc g))
-- V2 : ∀ {g} → Tm (suc (suc (suc g)))
-- V0 = VAR zero
-- V1 = VAR (suc zero)
-- V2 = VAR (suc (suc zero))

-- V0² : ∀ {g} → Tm (suc g)
-- V1² : ∀ {g} → Tm (suc (suc g))
-- V2² : ∀ {g} → Tm (suc (suc (suc g)))
-- V0² = VAR² zero
-- V1² = VAR² (suc zero)
-- V2² = VAR² (suc (suc zero))

-- V0³ : ∀ {g} → Tm (suc g)
-- V1³ : ∀ {g} → Tm (suc (suc g))
-- V2³ : ∀ {g} → Tm (suc (suc (suc g)))
-- V0³ = VAR³ zero
-- V1³ = VAR³ (suc zero)
-- V2³ = VAR³ (suc (suc zero))


-- -- Variable notation

-- 0ᵛ : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → Γ , A ∋ ty.wk zero A
-- 0ᵛ = top

-- 1ᵛ : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → {B : Ty (suc ⌊ Γ ⌋ᶜ)} → Γ , A , B ∋ ty.wk zero (ty.wk zero A)
-- 1ᵛ = pop top

-- 2ᵛ : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → {B : Ty (suc ⌊ Γ ⌋ᶜ)} → {C : Ty (suc (suc ⌊ Γ ⌋ᶜ))} → Γ , A , B , C ∋ ty.wk zero (ty.wk zero (ty.wk zero A))
-- 2ᵛ = pop (pop top)


-- -- Derivation notation, level 1

-- var : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ}
--     → (v : Γ ∋ A)
--     → Γ ⊢ A
-- var = var[ 0 ]

-- lam : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → {B : Ty (suc ⌊ Γ ⌋ᶜ)}
--     → Γ , A ⊢ B
--     → Γ ⊢ A ⊃ B
-- lam = lam[ 0 ] {ts = []}

-- app : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → {B : Ty (suc ⌊ Γ ⌋ᶜ)}
--     → Γ ⊢ A ⊃ B    → (e : Γ ⊢ A)
--     → Γ ⊢ ty.subst B zero ⌊ e ⌋
-- app = app[ 0 ] {ts = []} {us = []}

-- pair : ∀ {Γ} → {A B : Ty ⌊ Γ ⌋ᶜ}
--     → Γ ⊢ A    → Γ ⊢ B
--     → Γ ⊢ A ∧ B
-- pair = pair[ 0 ] {ts = []} {us = []}

-- fst : ∀ {Γ} → {A B : Ty ⌊ Γ ⌋ᶜ}
--     → Γ ⊢ A ∧ B
--     → Γ ⊢ A
-- fst = fst[ 0 ] {ts = []}

-- snd : ∀ {Γ} → {A B : Ty ⌊ Γ ⌋ᶜ}
--     → Γ ⊢ A ∧ B
--     → Γ ⊢ B
-- snd = snd[ 0 ] {ts = []}

-- up : ∀ {Γ} → {u : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ}
--     → Γ ⊢ u ∶ A
--     → Γ ⊢ ! u ∶ u ∶ A
-- up = up[ 0 ] {ts = []}

-- down : ∀ {Γ} → {u : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ}
--     → Γ ⊢ u ∶ A
--     → Γ ⊢ A
-- down = down[ 0 ] {ts = []}

-- boom : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ}
--     → Γ ⊢ ⊥ {⌊ Γ ⌋ᶜ}
--     → Γ ⊢ A
-- boom = boom[ 0 ] {ts = []}

-- v0 : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → Γ , A ⊢ ty.wk zero A
-- v0 = var 0ᵛ

-- v1 : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → {B : Ty (suc ⌊ Γ ⌋ᶜ)} → Γ , A , B ⊢ ty.wk zero (ty.wk zero A)
-- v1 = var 1ᵛ

-- v2 : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → {B : Ty (suc ⌊ Γ ⌋ᶜ)} → {C : Ty (suc (suc ⌊ Γ ⌋ᶜ))} → Γ , A , B , C ⊢ ty.wk zero (ty.wk zero (ty.wk zero A))
-- v2 = var 2ᵛ


-- -- Derivation notation, level 2

-- var² : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ}
--     → (v : Γ ∋ A)
--     → Γ ⊢ VAR[ 0 ] ⌊ v ⌋ᵛ ∶ A
-- var² = var[ 1 ]

-- lam² : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → {t : Tm (suc ⌊ Γ ⌋ᶜ)} → {B : Ty (suc ⌊ Γ ⌋ᶜ)}
--     → Γ , A ⊢ t ∶ B
--     → Γ ⊢ LAM[ 0 ] t ∶ (A ⊃ B)
-- lam² {t = t} = lam[ 1 ] {ts = t ∷ []}

-- app² : ∀ {Γ} → {t u : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ} → {B : Ty (suc ⌊ Γ ⌋ᶜ)}
--     → Γ ⊢ t ∶ (A ⊃ B)    → (e : Γ ⊢ u ∶ A)
--     → Γ ⊢ APP[ 0 ] t u ∶ ty.subst B zero ⌊ e ⌋
-- app² {t = t} {u} = app[ 1 ] {ts = t ∷ []} {us = u ∷ []}

-- pair² : ∀ {Γ} → {t u : Tm ⌊ Γ ⌋ᶜ} → {A B : Ty ⌊ Γ ⌋ᶜ}
--     → Γ ⊢ t ∶ A    → Γ ⊢ u ∶ B
--     → Γ ⊢ PAIR[ 0 ] t u ∶ (A ∧ B)
-- pair² {t = t} {u} = pair[ 1 ] {ts = t ∷ []} {us = u ∷ []}

-- fst² : ∀ {Γ} → {t : Tm ⌊ Γ ⌋ᶜ} → {A B : Ty ⌊ Γ ⌋ᶜ}
--     → Γ ⊢ t ∶ (A ∧ B)
--     → Γ ⊢ FST[ 0 ] t ∶ A
-- fst² {t = t} = fst[ 1 ] {ts = t ∷ []}

-- snd² : ∀ {Γ} → {t : Tm ⌊ Γ ⌋ᶜ} → {A B : Ty ⌊ Γ ⌋ᶜ}
--     → Γ ⊢ t ∶ (A ∧ B)
--     → Γ ⊢ SND[ 0 ] t ∶ B
-- snd² {t = t} = snd[ 1 ] {ts = t ∷ []}

-- up² : ∀ {Γ} → {t u : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ}
--     → Γ ⊢ t ∶ u ∶ A
--     → Γ ⊢ UP[ 0 ] t ∶ ! u ∶ u ∶ A
-- up² {t = t} = up[ 1 ] {ts = t ∷ []}

-- down² : ∀ {Γ} → {t u : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ}
--     → Γ ⊢ t ∶ u ∶ A
--     → Γ ⊢ DOWN[ 0 ] t ∶ A
-- down² {t = t} = down[ 1 ] {ts = t ∷ []}

-- boom² : ∀ {Γ} → {t : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ}
--     → Γ ⊢ t ∶ ⊥ {⌊ Γ ⌋ᶜ}
--     → Γ ⊢ BOOM[ 0 ] t ∶ A
-- boom² {t = t} = boom[ 1 ] {ts = t ∷ []}

-- v0² : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → Γ , A ⊢ V0 ∶ ty.wk zero A
-- v0² = var² 0ᵛ

-- v1² : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → {B : Ty (suc ⌊ Γ ⌋ᶜ)} → Γ , A , B ⊢ V1 ∶ ty.wk zero (ty.wk zero A)
-- v1² = var² 1ᵛ

-- v2² : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → {B : Ty (suc ⌊ Γ ⌋ᶜ)} → {C : Ty (suc (suc ⌊ Γ ⌋ᶜ))} → Γ , A , B , C ⊢ V2 ∶ ty.wk zero (ty.wk zero (ty.wk zero A))
-- v2² = var² 2ᵛ


-- -- Derivation notation, level 3

-- var³ : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ}
--     → (v : Γ ∋ A)
--     → Γ ⊢ VAR[ 1 ] ⌊ v ⌋ᵛ ∶ VAR[ 0 ] ⌊ v ⌋ᵛ ∶ A
-- var³ = var[ 2 ]

-- lam³ : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → {t₂ t : Tm (suc ⌊ Γ ⌋ᶜ)} → {B : Ty (suc ⌊ Γ ⌋ᶜ)}
--     → Γ , A ⊢ t₂ ∶ t ∶ B
--     → Γ ⊢ LAM[ 1 ] t₂ ∶ LAM[ 0 ] t ∶ (A ⊃ B)
-- lam³ {t₂ = t₂} {t} = lam[ 2 ] {ts = t₂ ∷ t ∷ []}

-- app³ : ∀ {Γ} → {t₂ t u₂ u : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ} → {B : Ty (suc ⌊ Γ ⌋ᶜ)}
--     → Γ ⊢ t₂ ∶ t ∶ (A ⊃ B)    → (e : Γ ⊢ u₂ ∶ u ∶ A)
--     → Γ ⊢ APP[ 1 ] t₂ u₂ ∶ APP[ 0 ] t u ∶ ty.subst B zero ⌊ e ⌋
-- app³ {t₂ = t₂} {t} {u₂} {u} = app[ 2 ] {ts = t₂ ∷ t ∷ []} {us = u₂ ∷ u ∷ []}

-- pair³ : ∀ {Γ} → {t₂ t u₂ u : Tm ⌊ Γ ⌋ᶜ} → {A B : Ty ⌊ Γ ⌋ᶜ}
--     → Γ ⊢ t₂ ∶ t ∶ A    → Γ ⊢ u₂ ∶ u ∶ B
--     → Γ ⊢ PAIR[ 1 ] t₂ u₂ ∶ PAIR[ 0 ] t u ∶ (A ∧ B)
-- pair³ {t₂ = t₂} {t} {u₂} {u} = pair[ 2 ] {ts = t₂ ∷ t ∷ []} {us = u₂ ∷ u ∷ []}

-- fst³ : ∀ {Γ} → {t₂ t : Tm ⌊ Γ ⌋ᶜ} → {A B : Ty ⌊ Γ ⌋ᶜ}
--     → Γ ⊢ t₂ ∶ t ∶ (A ∧ B)
--     → Γ ⊢ FST[ 1 ] t₂ ∶ FST[ 0 ] t ∶ A
-- fst³ {t₂ = t₂} {t} = fst[ 2 ] {ts = t₂ ∷ t ∷ []}

-- snd³ : ∀ {Γ} → {t₂ t : Tm ⌊ Γ ⌋ᶜ} → {A B : Ty ⌊ Γ ⌋ᶜ}
--     → Γ ⊢ t₂ ∶ t ∶ (A ∧ B)
--     → Γ ⊢ SND[ 1 ] t₂ ∶ SND[ 0 ] t ∶ B
-- snd³ {t₂ = t₂} {t} = snd[ 2 ] {ts = t₂ ∷ t ∷ []}

-- up³ : ∀ {Γ} → {t₂ t u : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ}
--     → Γ ⊢ t₂ ∶ t ∶ u ∶ A
--     → Γ ⊢ UP[ 1 ] t₂ ∶ UP[ 0 ] t ∶ ! u ∶ u ∶ A
-- up³ {t₂ = t₂} {t} = up[ 2 ] {ts = t₂ ∷ t ∷ []}

-- down³ : ∀ {Γ} → {t₂ t u : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ}
--     → Γ ⊢ t₂ ∶ t ∶ u ∶ A
--     → Γ ⊢ DOWN[ 1 ] t₂ ∶ DOWN[ 0 ] t ∶ A
-- down³ {t₂ = t₂} {t} = down[ 2 ] {ts = t₂ ∷ t ∷ []}

-- boom³ : ∀ {Γ} → {t₂ t : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ}
--     → Γ ⊢ t₂ ∶ t ∶ ⊥ {⌊ Γ ⌋ᶜ}
--     → Γ ⊢ BOOM[ 1 ] t₂ ∶ BOOM[ 0 ] t ∶ A
-- boom³ {t₂ = t₂} {t} = boom[ 2 ] {ts = t₂ ∷ t ∷ []}

-- v0³ : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → Γ , A ⊢ V0² ∶ V0 ∶ ty.wk zero A
-- v0³ = var³ 0ᵛ

-- v1³ : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → {B : Ty (suc ⌊ Γ ⌋ᶜ)} → Γ , A , B ⊢ V1² ∶ V1 ∶ ty.wk zero (ty.wk zero A)
-- v1³ = var³ 1ᵛ

-- v2³ : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → {B : Ty (suc ⌊ Γ ⌋ᶜ)} → {C : Ty (suc (suc ⌊ Γ ⌋ᶜ))} → Γ , A , B , C ⊢ V2² ∶ V2 ∶ ty.wk zero (ty.wk zero (ty.wk zero A))
-- v2³ = var³ 2ᵛ


-- -- Examples

-- module ex where
--   open ty renaming (wk to w)

--   I : ∀ {Γ} {A : Ty ⌊ Γ ⌋ᶜ} → Γ ⊢ A ⊃ w zero A
--   I = lam v0

--   K : ∀ {Γ} {A B : Ty ⌊ Γ ⌋ᶜ} → Γ ⊢ A ⊃ w zero B ⊃ w zero (w zero A)
--   K = lam (lam v1)
