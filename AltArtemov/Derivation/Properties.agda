module AltArtemov.Derivation.Properties where

open import Data.Nat using (ℕ ; zero ; suc ; _<′_ ; _⊓_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import AltArtemov.Context
open import AltArtemov.Derivation.Core
open import AltArtemov.Term
open import AltArtemov.Term.Properties using () renaming (lev to tm-lev)
open import AltArtemov.TermVector
open import AltArtemov.Type
open import AltArtemov.Type.Properties using (lower) renaming (lev to ty-lev)
open import Data.Nat.Missing


-- Derivations have types.
ty : ∀ {Γ A} (d : Γ ⊢ A) → Ty
ty {A = A} d = A


-- Derivations have levels.
lev : ∀ {Γ A} (d : Γ ⊢ A) → ℕ
lev (VAR[ n ] i)    = n
lev (LAM[ n ] d)    = n ⊓ lev d
lev (APP[ n ] d c)  = n ⊓ lev d ⊓ lev c
lev (UP[ n ] d)     = n ⊓ lev d
lev (DOWN[ n ] d)   = n ⊓ lev d


-- Derivations can be represented as terms.
repr : ∀ {Γ A} (d : Γ ⊢ A) → Tm
repr (VAR[ n ] i)   = var[ n ] (ix i)
repr (LAM[ n ] d)   = lam[ n ] (repr d)
repr (APP[ n ] d c) = app[ n ] (repr d) (repr c)
repr (UP[ n ] d)    = up[ n ] (repr d)
repr (DOWN[ n ] d)  = down[ n ] (repr d)


-- Representing a derivation preserves its level.
tm-lev-repr-d≡lev-d : ∀ {Γ A} (d : Γ ⊢ A) → tm-lev (repr d) ≡ lev d
tm-lev-repr-d≡lev-d (VAR[ n ] i)   = refl
tm-lev-repr-d≡lev-d (LAM[ n ] d)   rewrite tm-lev-repr-d≡lev-d d = refl
tm-lev-repr-d≡lev-d (APP[ n ] d c) rewrite tm-lev-repr-d≡lev-d d | tm-lev-repr-d≡lev-d c = refl
tm-lev-repr-d≡lev-d (UP[ n ] d)    rewrite tm-lev-repr-d≡lev-d d = refl
tm-lev-repr-d≡lev-d (DOWN[ n ] d)  rewrite tm-lev-repr-d≡lev-d d = refl


-- Derivations can be internalised.
int : ∀ {Γ A} (d : Γ ⊢ A) → Γ ⊢ repr d ∶ A
int (VAR[ n ] i)             = VAR[ suc n ] i
int (LAM[ n ] {ts} d)        = LAM[ suc n ] {ts = repr d ∷ ts} (int d)
int (APP[ n ] {ts} {ss} d c) = APP[ suc n ] {ts = repr d ∷ ts} {ss = repr c ∷ ss} (int d) (int c)
int (UP[ n ] {ts} d)         = UP[ suc n ] {ts = repr d ∷ ts} (int d)
int (DOWN[ n ] {ts} d)       = DOWN[ suc n ] {ts = repr d ∷ ts} (int d)


-- Necessitation is a special case of internalisation.
nec : ∀ {A} (d : ∅ ⊢ A) → ∅ ⊢ repr d ∶ A
nec = int


-- Internalising a derivation asserts its type.
ty-int-d≡repr-d∶ty-d : ∀ {Γ A} (d : Γ ⊢ A) → ty (int d) ≡ repr d ∶ A
ty-int-d≡repr-d∶ty-d d = refl


-- Internalising a derivation increments its level.
lev-int-d≡suc-lev-d : ∀ {Γ A} (d : Γ ⊢ A) → lev (int d) ≡ suc (lev d)
lev-int-d≡suc-lev-d (VAR[ n ] i)   = refl
lev-int-d≡suc-lev-d (LAM[ n ] d)   rewrite lev-int-d≡suc-lev-d d = refl
lev-int-d≡suc-lev-d (APP[ n ] d c) rewrite lev-int-d≡suc-lev-d d | lev-int-d≡suc-lev-d c = refl
lev-int-d≡suc-lev-d (UP[ n ] d)    rewrite lev-int-d≡suc-lev-d d = refl
lev-int-d≡suc-lev-d (DOWN[ n ] d)  rewrite lev-int-d≡suc-lev-d d = refl


-- Internalising a derivation increments the level of its type.
ty-lev-int-d≡suc-ty-lev-d : ∀ {Γ A} (d : Γ ⊢ A) → ty-lev (ty (int d)) ≡ suc (ty-lev A)
ty-lev-int-d≡suc-ty-lev-d d = refl


-- The level of an internalised derivation is greater than 0.
z<′lev-int-d : ∀ {Γ A} (d : Γ ⊢ A) → zero <′ lev (int d)
z<′lev-int-d (VAR[ n ] i)   = z<′sn
z<′lev-int-d (LAM[ n ] d)   rewrite lev-int-d≡suc-lev-d d = z<′sn
z<′lev-int-d (APP[ n ] d c) rewrite lev-int-d≡suc-lev-d d | lev-int-d≡suc-lev-d c = z<′sn
z<′lev-int-d (UP[ n ] d)    rewrite lev-int-d≡suc-lev-d d = z<′sn
z<′lev-int-d (DOWN[ n ] d)  rewrite lev-int-d≡suc-lev-d d = z<′sn


-- The level of the type of an internalised derivation is greater than 0.
z<′ty-lev-int-d : ∀ {Γ A} (d : Γ ⊢ A) → zero <′ ty-lev (ty (int d))
z<′ty-lev-int-d d = z<′sn


-- Derivations of level greater than 0, and of type that is of level greater than 0, can be uninternalised.
unint : ∀ {Γ A} (d : Γ ⊢ A) → zero <′ lev d → (z<′tl : zero <′ ty-lev A) → Γ ⊢ lower A z<′tl
unint (VAR[ zero ] i)                      ()   z<′tl
unint (LAM[ zero ] d)                      ()   z<′tl
unint (APP[ zero ] d c)                    ()   z<′tl
unint (UP[ zero ] d)                       ()   z<′tl
unint (DOWN[ zero ] d)                     ()   z<′tl
unint (VAR[ suc n ] i)                     z<′l z<′tl = VAR[ n ] i
unint (LAM[ suc n ] {t ∷ ts} d)            z<′l z<′tl = LAM[ n ] (unint d (z<′sm⊓n⇒z<′n z<′l) z<′sn)
unint (APP[ suc n ] {t ∷ ts} {s ∷ ss} d c) z<′l z<′tl = APP[ n ] (unint d (z<′sm⊓n⊓o⇒z<′n (lev c) z<′l) z<′sn)
                                                                 (unint c (z<′sm⊓n⊓o⇒z<′o (lev d) z<′l) z<′sn)
unint (UP[ suc n ] {t ∷ ts} d)             z<′l z<′tl = UP[ n ] (unint d (z<′sm⊓n⇒z<′n z<′l) z<′sn)
unint (DOWN[ suc n ] {t ∷ ts} d)           z<′l z<′tl = DOWN[ n ] (unint d (z<′sm⊓n⇒z<′n z<′l) z<′sn)


-- Unnecessitation is a special case of uninternalisation.
unnec : ∀ {A} (d : ∅ ⊢ A) → zero <′ lev d → (z<′tl : zero <′ ty-lev A) → ∅ ⊢ lower A z<′tl
unnec = unint
