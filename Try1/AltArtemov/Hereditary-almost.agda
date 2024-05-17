module AltArtemov.Hereditary where

open import Data.Fin using (Fin ; zero ; suc)
open import Data.Nat using (ℕ ; zero ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)


-- Terms

data Tm (g : ℕ) : Set where
  !_      : Tm g → Tm g
  VAR[_]  : ℕ → Fin g → Tm g
  LAM[_]  : ℕ → Tm (suc g) → Tm g
  APP[_]  : ℕ → Tm g → Tm g → Tm g
  UP[_]   : ℕ → Tm g → Tm g
  DOWN[_] : ℕ → Tm g → Tm g
  PAIR[_] : ℕ → Tm g → Tm g → Tm g
  FST[_]  : ℕ → Tm g → Tm g
  SND[_]  : ℕ → Tm g → Tm g
  BOOM[_] : ℕ → Tm g → Tm g

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

  data _≡ᵛ_ {g : ℕ} : Fin g → Fin g → Set where
    same : {i : Fin g} → i ≡ᵛ i
    diff : (i : Fin g) → (j : Fin (g -ᵛ i)) → i ≡ᵛ wkᵛ i j

  _≟ᵛ_ : ∀ {g} → (i : Fin g) → (j : Fin g) → i ≡ᵛ j
  zero ≟ᵛ zero            = same
  zero ≟ᵛ suc j           = diff zero j
  suc i ≟ᵛ zero           = diff (suc i) zero
  suc i ≟ᵛ suc j          with i ≟ᵛ j
  suc i ≟ᵛ suc .i         | same = same
  suc i ≟ᵛ suc .(wkᵛ i j) | diff .i j = diff (suc i) (suc j)

  wk : ∀ {g} → (i : Fin g) → Tm (g -ᵛ i) → Tm g
  wk i (! t)           = ! (wk i t)
  wk i (VAR[ n ] v)    = VAR[ n ] (wkᵛ i v)
  wk i (LAM[ n ] t)    = LAM[ n ] (wk (suc i) t)
  wk i (APP[ n ] t u)  = APP[ n ] (wk i t) (wk i u)
  wk i (UP[ n ] t)     = UP[ n ] (wk i t)
  wk i (DOWN[ n ] t)   = DOWN[ n ] (wk i t)
  wk i (PAIR[ n ] t u) = PAIR[ n ] (wk i t) (wk i u)
  wk i (FST[ n ] t)    = FST[ n ] (wk i t)
  wk i (SND[ n ] t)    = SND[ n ] (wk i t)
  wk i (BOOM[ n ] t)   = BOOM[ n ] (wk i t)

  substᵛ : ∀ {g} → ℕ → Fin g → (i : Fin g) → Tm (g -ᵛ i) → Tm (g -ᵛ i)
  substᵛ n v i s          with i ≟ᵛ v
  substᵛ n v .v s         | same = s
  substᵛ n .(wkᵛ v i) v s | diff .v i = VAR[ n ] i

  subst : ∀ {g} → Tm g → (i : Fin g) → Tm (g -ᵛ i) → Tm (g -ᵛ i)
  subst (! t) i s           = ! subst t i s
  subst (VAR[ n ] v) i s    = substᵛ n v i s
  subst (LAM[ n ] t) i s    = LAM[ n ] (subst t (suc i) (wk zero s))
  subst (APP[ n ] t u) i s  = APP[ n ] (subst t i s) (subst u i s)
  subst (UP[ n ] t) i s     = UP[ n ] (subst t i s)
  subst (DOWN[ n ] t) i s   = DOWN[ n ] (subst t i s)
  subst (PAIR[ n ] t u) i s = PAIR[ n ] (subst t i s) (subst u i s)
  subst (FST[ n ] t) i s    = FST[ n ] (subst t i s)
  subst (SND[ n ] t) i s    = SND[ n ] (subst t i s)
  subst (BOOM[ n ] t) i s   = BOOM[ n ] (subst t i s)


-- Types

infixr 2 _⊃_
infixr 5 _∶_

data Ty (g : ℕ) : Set where
  _∶_ : Tm g → Ty g → Ty g
  _⊃_ : Ty g → Ty g → Ty g
  _∧_ : Ty g → Ty g → Ty g
  ⊥  : Ty g

⊤ : ∀ {g} → Ty g
⊤ = ⊥ ⊃ ⊥

¬_ : ∀ {g} → Ty g → Ty g
¬ A = A ⊃ ⊥

_⫗_ : ∀ {g} → Ty g → Ty g → Ty g
A ⫗ B = (A ⊃ B) ∧ (B ⊃ A)

module ty where
  open tm using (_-ᵛ_)

  wk : ∀ {g} → (i : Fin g) → Ty (g -ᵛ i) → Ty g
  wk i (t ∶ A) = tm.wk i t ∶ wk i A
  wk i (A ⊃ B) = wk i A ⊃ wk i B
  wk i (A ∧ B) = wk i A ∧ wk i B
  wk i ⊥      = ⊥

  subst : ∀ {g} → Ty g → (i : Fin g) → Tm (g -ᵛ i) → Ty (g -ᵛ i)
  subst (t ∶ A) i s = tm.subst t i s ∶ subst A i s
  subst (A ⊃ B) i s = subst A i s ⊃ subst B i s
  subst (A ∧ B) i s = subst A i s ∧ subst B i s
  subst ⊥ i s      = ⊥

ty-fnord : ∀ {g} → Ty (suc g) → Ty g
ty-fnord A = ty.subst A zero {!!}


-- Term vectors

infixr 5 _∷_

data Tms (g : ℕ) : ℕ → Set where
  []  : Tms g zero
  _∷_ : ∀ {n} → Tm g → Tms g n → Tms g (suc n)

map# : ∀ {g} → (ℕ → Tm g → Tm g) → (n : ℕ) → Tms g n → Tms g n
map# f zero []          = []
map# f (suc n) (t ∷ ts) = f (suc n) t ∷ map# f n ts

map#₂ : ∀ {g} → (ℕ → Tm g → Tm g → Tm g) → (n : ℕ) → Tms g n → Tms g n → Tms g n
map#₂ f zero [] []                = []
map#₂ f (suc n)  (t ∷ ts) (u ∷ us) = f (suc n) t u ∷ map#₂ f n ts us

VARs[_] : ∀ {g} → (n : ℕ) → Fin g → Tms g n
VARs[ zero ] i  = []
VARs[ suc n ] i = VAR[ n ] i ∷ VARs[ n ] i

LAMs[_] : ∀ {g} → (n : ℕ) → Tms (suc g) n → Tms g n
LAMs[ zero ] []        = []
LAMs[ suc n ] (t ∷ ts) = LAM[ n ] t ∷ LAMs[ n ] ts

APPs[_] : ∀ {g} → (n : ℕ) → Tms g n → Tms g n → Tms g n
APPs[_] = map#₂ APP[_]

UPs[_] : ∀ {g} → (n : ℕ) → Tms g n → Tms g n
UPs[_] = map# UP[_]

DOWNs[_] : ∀ {g} → (n : ℕ) → Tms g n → Tms g n
DOWNs[_] = map# DOWN[_]

PAIRs[_] : ∀ {g} → (n : ℕ) → Tms g n → Tms g n → Tms g n
PAIRs[_] = map#₂ PAIR[_]

FSTs[_] : ∀ {g} → (n : ℕ) → Tms g n → Tms g n
FSTs[_] = map# FST[_]

SNDs[_] : ∀ {g} → (n : ℕ) → Tms g n → Tms g n
SNDs[_] = map# SND[_]

BOOMs[_] : ∀ {g} → (n : ℕ) → Tms g n → Tms g n
BOOMs[_] = map# BOOM[_]


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


-- Level 0

infix 0 _⊢⁰_

data _⊢⁰_ (Γ : Cx) : Ty ⌊ Γ ⌋ᶜ → Set where
  var⁰ : {A : Ty ⌊ Γ ⌋ᶜ}
      → (v : Γ ∋ A)
      → Γ ⊢⁰ A

  lam⁰ : {A : Ty ⌊ Γ ⌋ᶜ} → {B : Ty (suc ⌊ Γ ⌋ᶜ)}
      → Γ , A ⊢⁰ B
      → Γ ⊢⁰ A ⊃ ty-fnord B

  app⁰ : {A B : Ty ⌊ Γ ⌋ᶜ}
      → Γ ⊢⁰ A ⊃ B    → Γ ⊢⁰ A
      → Γ ⊢⁰ B

  up⁰ : {u : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ}
      → Γ ⊢⁰ u ∶ A
      → Γ ⊢⁰ ! u ∶ u ∶ A

  down⁰ : {u : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ}
      → Γ ⊢⁰ u ∶ A
      → Γ ⊢⁰ A

  pair⁰ : {A B : Ty ⌊ Γ ⌋ᶜ}
      → Γ ⊢⁰ A    → Γ ⊢⁰ B
      → Γ ⊢⁰ A ∧ B

  fst⁰ : {A B : Ty ⌊ Γ ⌋ᶜ}
      → Γ ⊢⁰ A ∧ B
      → Γ ⊢⁰ A

  snd⁰ : {A B : Ty ⌊ Γ ⌋ᶜ}
      → Γ ⊢⁰ A ∧ B
      → Γ ⊢⁰ B

  boom⁰ : {A : Ty ⌊ Γ ⌋ᶜ}
      → Γ ⊢⁰ ⊥ {⌊ Γ ⌋ᶜ}
      → Γ ⊢⁰ A


-- Level 1

infix 0 _⊢¹_

data _⊢¹_ (Γ : Cx) : Ty ⌊ Γ ⌋ᶜ → Set where
  var¹ : {A : Ty ⌊ Γ ⌋ᶜ}
      → (v : Γ ∋ A)
      → Γ ⊢¹ VAR[ 0 ] ⌊ v ⌋ᵛ ∶ A

  lam¹ : {A : Ty ⌊ Γ ⌋ᶜ} → {t : Tm (suc ⌊ Γ ⌋ᶜ)} → {B : Ty (suc ⌊ Γ ⌋ᶜ)}
      → Γ , A ⊢¹ t ∶ B
      → Γ ⊢¹ LAM[ 0 ] t ∶ (A ⊃ ty-fnord B)

  app¹ : {t u : Tm ⌊ Γ ⌋ᶜ} → {A B : Ty ⌊ Γ ⌋ᶜ}
      → Γ ⊢¹ t ∶ (A ⊃ B)    → Γ ⊢¹ u ∶ A
      → Γ ⊢¹ APP[ 0 ] t u ∶ B

  up¹ : {t u : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ}
      → Γ ⊢¹ t ∶ u ∶ A
      → Γ ⊢¹ UP[ 0 ] t ∶ ! u ∶ u ∶ A

  down¹ : {t u : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ}
      → Γ ⊢¹ t ∶ u ∶ A
      → Γ ⊢¹ DOWN[ 0 ] t ∶ A

  pair¹ : {t u : Tm ⌊ Γ ⌋ᶜ} → {A B : Ty ⌊ Γ ⌋ᶜ}
      → Γ ⊢¹ t ∶ A    → Γ ⊢¹ u ∶ B
      → Γ ⊢¹ PAIR[ 0 ] t u ∶ (A ∧ B)

  fst¹ : {t : Tm ⌊ Γ ⌋ᶜ} → {A B : Ty ⌊ Γ ⌋ᶜ}
      → Γ ⊢¹ t ∶ (A ∧ B)
      → Γ ⊢¹ FST[ 0 ] t ∶ A

  snd¹ : {t : Tm ⌊ Γ ⌋ᶜ} → {A B : Ty ⌊ Γ ⌋ᶜ}
      → Γ ⊢¹ t ∶ (A ∧ B)
      → Γ ⊢¹ SND[ 0 ] t ∶ B

  boom¹ : {t : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ}
      → Γ ⊢¹ t ∶ ⊥ {⌊ Γ ⌋ᶜ}
      → Γ ⊢¹ BOOM[ 0 ] t ∶ A


-- Level 2

infix 0 _⊢²_

data _⊢²_ (Γ : Cx) : Ty ⌊ Γ ⌋ᶜ → Set where
  var² : {A : Ty ⌊ Γ ⌋ᶜ}
      → (v : Γ ∋ A)
      → Γ ⊢² VAR[ 1 ] ⌊ v ⌋ᵛ ∶ VAR[ 0 ] ⌊ v ⌋ᵛ ∶ A

  lam² : {A : Ty ⌊ Γ ⌋ᶜ} → {t₂ t : Tm (suc ⌊ Γ ⌋ᶜ)} → {B : Ty (suc ⌊ Γ ⌋ᶜ)}
      → Γ , A ⊢² t₂ ∶ t ∶ B
      → Γ ⊢² LAM[ 1 ] t₂ ∶ LAM[ 0 ] t ∶ (A ⊃ ty-fnord B)

  app² : {t₂ t u₂ u : Tm ⌊ Γ ⌋ᶜ} → {A B : Ty ⌊ Γ ⌋ᶜ}
      → Γ ⊢² t₂ ∶ t ∶ (A ⊃ B)    → Γ ⊢² u₂ ∶ u ∶ A
      → Γ ⊢² APP[ 1 ] t₂ u₂ ∶ APP[ 0 ] t u ∶ B

  up² : {t₂ t u : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ}
      → Γ ⊢² t₂ ∶ t ∶ u ∶ A
      → Γ ⊢² UP[ 1 ] t₂ ∶ UP[ 0 ] t ∶ ! u ∶ u ∶ A

  down² : {t₂ t u : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ}
      → Γ ⊢² t₂ ∶ t ∶ u ∶ A
      → Γ ⊢² DOWN[ 1 ] t₂ ∶ DOWN[ 0 ] t ∶ A

  pair² : {t₂ t u₂ u : Tm ⌊ Γ ⌋ᶜ} → {A B : Ty ⌊ Γ ⌋ᶜ}
      → Γ ⊢² t₂ ∶ t ∶ A    → Γ ⊢² u₂ ∶ u ∶ B
      → Γ ⊢² PAIR[ 1 ] t₂ u₂ ∶ PAIR[ 0 ] t u ∶ (A ∧ B)

  fst² : {t₂ t : Tm ⌊ Γ ⌋ᶜ} → {A B : Ty ⌊ Γ ⌋ᶜ}
      → Γ ⊢² t₂ ∶ t ∶ (A ∧ B)
      → Γ ⊢² FST[ 1 ] t₂ ∶ FST[ 0 ] t ∶ A

  snd² : {t₂ t : Tm ⌊ Γ ⌋ᶜ} → {A B : Ty ⌊ Γ ⌋ᶜ}
      → Γ ⊢² t₂ ∶ t ∶ (A ∧ B)
      → Γ ⊢² SND[ 1 ] t₂ ∶ SND[ 0 ] t ∶ B

  boom² : {t₂ t : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ}
      → Γ ⊢² t₂ ∶ t ∶ ⊥ {⌊ Γ ⌋ᶜ}
      → Γ ⊢² BOOM[ 1 ] t₂ ∶ BOOM[ 0 ] t ∶ A



-- infixr 5 _∴_
-- infix 0 _⊢_

-- _∴_ : ∀ {g k n} → Tms (g +ᴿ k) n → Ty g → Ty (g +ᴿ k)
-- [] ∴ A       = ty.wk* _ A
-- (t ∷ ts) ∴ A = t ∶ ts ∴ A


-- infixr 5 _∴_
--
-- _∴_ : ∀ {g n} → Tms g n → Ty {!!} → Ty {!!}
-- [] ∴ A = A
-- (t ∷ ts) ∴ A = t ∶ ts ∴ A


-- infix 0 _⊢_

-- data _⊢_ (Γ : Cx) : Ty ⌊ Γ ⌋ᶜ → Set where
-- --  var[_] : (n : ℕ) → {A : Ty zero}
-- --      → (v : A ∈ Γ) → {i : Fin ⌊ Γ ⌋ᶜ} → (p : ⌊ v ⌋ᵛ ≡ i)
-- --      → Γ ⊢ VARs[ n ] i ∴ A
-- --
-- --  lam[_] : (n : ℕ) → {ts : Tms (suc ⌊ Γ ⌋ᶜ) n} → {A B : Ty zero}
-- --      → Γ , A ⊢ ts ∴ B
-- --      → Γ ⊢ LAMs[ n ] ts ∴ (A ⊃ B)

--   app[_] : (n : ℕ) → {ts us : Tms ⌊ Γ ⌋ᶜ n} → {A B : Ty zero}
--       → Γ ⊢ ts ∴ (A ⊃ B)    → Γ ⊢ us ∴ A
--       → Γ ⊢ APPs[ n ] ts us ∴ B

--   up[_] : (n : ℕ) → {ts : Tms ⌊ Γ ⌋ᶜ n} → {u : Tm zero} → {A : Ty zero}
--       → Γ ⊢ ts ∴ u ∶ A
--       → Γ ⊢ UPs[ n ] ts ∴ ! u ∶ u ∶ A

--   down[_] : (n : ℕ) → {ts : Tms ⌊ Γ ⌋ᶜ n} → {u : Tm zero} → {A : Ty zero}
--       → Γ ⊢ ts ∴ u ∶ A
--       → Γ ⊢ DOWNs[ n ] ts ∴ A

--   pair[_] : (n : ℕ) → {ts us : Tms ⌊ Γ ⌋ᶜ n} → {A B : Ty zero}
--       → Γ ⊢ ts ∴ A    → Γ ⊢ us ∴ B
--       → Γ ⊢ PAIRs[ n ] ts us ∴ (A ∧ B)

--   fst[_] : (n : ℕ) → {ts : Tms ⌊ Γ ⌋ᶜ n} → {A B : Ty zero}
--       → Γ ⊢ ts ∴ (A ∧ B)
--       → Γ ⊢ FSTs[ n ] ts ∴ A

--   snd[_] : (n : ℕ) → {ts : Tms ⌊ Γ ⌋ᶜ n} → {A B : Ty zero}
--       → Γ ⊢ ts ∴ (A ∧ B)
--       → Γ ⊢ SNDs[ n ] ts ∴ B

--   boom[_] : (n : ℕ) → {ts : Tms ⌊ Γ ⌋ᶜ n} → {A : Ty zero}
--       → Γ ⊢ ts ∴ ⊥
--       → Γ ⊢ BOOMs[ n ] ts ∴ A


-- I : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → Γ ⊢ A ⊃ A
-- I = {!lam[ 0 ] {[]} ?!}


-- -- infixl 4 _-ᵛ_

-- -- _-ᵛ_ : ∀ {A} → (Γ : Cx) → A ∈ Γ → Cx
-- -- ∅ -ᵛ ()
-- -- (Γ , A) -ᵛ top   = Γ
-- -- (Γ , B) -ᵛ pop x = Γ -ᵛ x , B


-- -- wkᵛ : ∀ {Γ A B} → (x : A ∈ Γ) → B ∈ Γ -ᵛ x → B ∈ Γ
-- -- wkᵛ top y           = pop y
-- -- wkᵛ (pop x) top     = top
-- -- wkᵛ (pop x) (pop y) = pop (wkᵛ x y)


-- -- data _≡ᵛ_ {Γ : Cx} : ∀ {A B} → A ∈ Γ → B ∈ Γ → Set where
-- --   same : ∀ {A} → {x : A ∈ Γ} → x ≡ᵛ x
-- --   diff : ∀ {A B} → (x : A ∈ Γ) → (y : B ∈ Γ -ᵛ x) → x ≡ᵛ wkᵛ x y


-- -- _≟ᵛ_ : ∀ {Γ A B} → (x : A ∈ Γ) → (y : B ∈ Γ) → x ≡ᵛ y
-- -- top ≟ᵛ top              = same
-- -- top ≟ᵛ pop y            = diff top y
-- -- pop x ≟ᵛ top            = diff (pop x) top
-- -- pop x ≟ᵛ pop y          with x ≟ᵛ y
-- -- pop y ≟ᵛ pop .y         | same = same
-- -- pop x ≟ᵛ pop .(wkᵛ x y) | diff .x y = diff (pop x) (pop y)


-- -- -- wk : ∀ {Γ A B} → (x : A ∈ Γ) → Γ -ᵛ x ⊢ B → Γ ⊢ B
-- -- -- wk x (var[ n ] v p)  = {!!} -- var[ n ] (wkᵛ x v) {!!}
-- -- -- wk x (lam[ n ] d)    = {!lam[ n ] ?!} -- lam[ n ] (wk (pop x) d)
-- -- -- wk x (app[ n ] d e)  = {!!} -- app[ n ] (wk x d) (wk x e)
-- -- -- wk x (up[ n ] d)     = {!!} -- up[ n ] (wk x d)
-- -- -- wk x (down[ n ] d)   = {!!} -- down[ n ] (wk x d)
-- -- -- wk x (pair[ n ] d e) = {!!} -- pair[ n ] (wk x d) (wk x e)
-- -- -- wk x (fst[ n ] d)    = {!!} -- fst[ n ] (wk x d)
-- -- -- wk x (snd[ n ] d)    = {!!} -- snd[ n ] (wk x d)
-- -- -- wk x (boom[ n ] d)   = {!!} -- boom[ n ] (wk x d)
