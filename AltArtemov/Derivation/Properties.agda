module AltArtemov.Derivation.Properties where

open import Data.Empty using () renaming (⊥ to Empty)
open import Data.Nat using (ℕ ; zero ; suc ; _<′_ ; _⊓_) renaming (_≟_ to _ℕ≟_)
open import Data.Maybe using (Maybe ; nothing ; just)
open import Data.Unit using () renaming (⊤ to Unit)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; subst ; sym)
open import Relation.Nullary using (yes ; no)

open import AltArtemov.Context
open import AltArtemov.Derivation.Core
open import AltArtemov.Term
open import AltArtemov.TermVector
open import AltArtemov.Type
open import Data.Nat.Missing


-- Derivations have types.
ty : ∀ {Γ A} (d : Γ ⊢ A) → Ty
ty {A = A} d = A


-- Derivations of type that is of level greater than 0 have terms.
tm : ∀ {Γ A} (d : Γ ⊢ A) (z<′tl : zero <′ ty-lev A) → Tm
tm d z<′tl = ty-tm (ty d) z<′tl


-- Derivations have levels.
lev : ∀ {Γ A} (d : Γ ⊢ A) → ℕ
lev (VAR[ n ] i)    = n
lev (LAM[ n ] d)    = n ⊓ lev d
lev (APP[ n ] d c)  = n ⊓ lev d ⊓ lev c
lev (UP[ n ] d)     = n ⊓ lev d
lev (DOWN[ n ] d)   = n ⊓ lev d


-- Derivations can be represented as terms.
rep : ∀ {Γ A} (d : Γ ⊢ A) → Tm
rep (VAR[ n ] i)   = var[ n ] (ix i)
rep (LAM[ n ] d)   = lam[ n ] (rep d)
rep (APP[ n ] d c) = app[ n ] (rep d) (rep c)
rep (UP[ n ] d)    = up[ n ] (rep d)
rep (DOWN[ n ] d)  = down[ n ] (rep d)


-- Representing a derivation preserves its level.
tm-lev-rep-d≡lev-d : ∀ {Γ A} (d : Γ ⊢ A) → tm-lev (rep d) ≡ lev d
tm-lev-rep-d≡lev-d (VAR[ n ] i)   = refl
tm-lev-rep-d≡lev-d (LAM[ n ] d)   rewrite tm-lev-rep-d≡lev-d d = refl
tm-lev-rep-d≡lev-d (APP[ n ] d c) rewrite tm-lev-rep-d≡lev-d d | tm-lev-rep-d≡lev-d c = refl
tm-lev-rep-d≡lev-d (UP[ n ] d)    rewrite tm-lev-rep-d≡lev-d d = refl
tm-lev-rep-d≡lev-d (DOWN[ n ] d)  rewrite tm-lev-rep-d≡lev-d d = refl


-- Derivations can be internalised.
int : ∀ {Γ A} (d : Γ ⊢ A) → Γ ⊢ rep d ∶ A
int (VAR[ n ] i)             = VAR[ suc n ] i
int (LAM[ n ] {ts} d)        = LAM[ suc n ] {ts = rep d ∷ ts} (int d)
int (APP[ n ] {ts} {ss} d c) = APP[ suc n ] {ts = rep d ∷ ts} {ss = rep c ∷ ss} (int d) (int c)
int (UP[ n ] {ts} d)         = UP[ suc n ] {ts = rep d ∷ ts} (int d)
int (DOWN[ n ] {ts} d)       = DOWN[ suc n ] {ts = rep d ∷ ts} (int d)


-- Weakening a context preserves derivations from the context.
weak-dn : ∀ Γ Δ {A} (d : ∅ ++ Γ ⊢ A) → Δ ++ Γ ⊢ A
weak-dn Γ Δ (VAR[ n ] i)         rewrite sym (ix-weak-cx≡ix Γ i) = VAR[ n ] (weak-ix Γ Δ i)
weak-dn Γ Δ (LAM[ n ] {A = A} d) = LAM[ n ] (weak-dn (Γ , A) Δ d)
weak-dn Γ Δ (APP[ n ] d c)       = APP[ n ] (weak-dn Γ Δ d) (weak-dn Γ Δ c)
weak-dn Γ Δ (UP[ n ] d)          = UP[ n ] (weak-dn Γ Δ d)
weak-dn Γ Δ (DOWN[ n ] d)        = DOWN[ n ] (weak-dn Γ Δ d)


-- Necessitation is a special case of internalisation.
nec : ∀ {Γ A} (d : ∅ ⊢ A) → Γ ⊢ rep d ∶ A
nec {Γ} d = weak-dn ∅ Γ (int d)


-- Internalising a derivation asserts its type.
ty-int-d≡rep-d∶ty-d : ∀ {Γ A} (d : Γ ⊢ A) → ty (int d) ≡ rep d ∶ A
ty-int-d≡rep-d∶ty-d d = refl


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
unint : ∀ {Γ A} (d : Γ ⊢ A) (z<′l : zero <′ lev d) (z<′tl : zero <′ ty-lev A) → Γ ⊢ lower A z<′tl
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
unnec : ∀ {A} (d : ∅ ⊢ A) (z<′l : zero <′ lev d) (z<′tl : zero <′ ty-lev A) → ∅ ⊢ lower A z<′tl
unnec = unint


-- TODO

unint2 : ∀ {Γ A} (d : Γ ⊢ A) (z<′l : zero <′ lev d) {HA : HighTy A} → Γ ⊢ lower′ A {HA}
unint2 (VAR[ zero ] i)                      ()
unint2 (LAM[ zero ] d)                      ()
unint2 (APP[ zero ] d c)                    ()
unint2 (UP[ zero ] d)                       ()
unint2 (DOWN[ zero ] d)                     ()
unint2 (VAR[ suc n ] i)                     z<′l = VAR[ n ] i
unint2 (LAM[ suc n ] {t ∷ ts} d)            z<′l = LAM[ n ] (unint2 d (z<′sm⊓n⇒z<′n z<′l))
unint2 (APP[ suc n ] {t ∷ ts} {s ∷ ss} d c) z<′l = APP[ n ] (unint2 d (z<′sm⊓n⊓o⇒z<′n (lev c) z<′l))
                                                            (unint2 c (z<′sm⊓n⊓o⇒z<′o (lev d) z<′l))
unint2 (UP[ suc n ] {t ∷ ts} d)             z<′l = UP[ n ] (unint2 d (z<′sm⊓n⇒z<′n z<′l))
unint2 (DOWN[ suc n ] {t ∷ ts} d)           z<′l = DOWN[ n ] (unint2 d (z<′sm⊓n⇒z<′n z<′l))


can-unint : ∀ {Γ A} (d : Γ ⊢ A) {HA : HighTy A} → Maybe (Γ ⊢ lower′ A {HA})
can-unint d with lev d
...           | zero  = nothing
...           | suc n with suc n ℕ≟ lev d
...                   | no  sn≢l = nothing
...                   | yes sn≡l = just (unint2 d (subst (λ n → zero <′ n) sn≡l z<′sn))

HighDn : ∀ {A} (d : ∅ ⊢ A) {HA : HighTy A} → Set
HighDn d {HA} with can-unint d {HA}
...         | just d′ = Unit
...         | _       = Empty

unint′ : ∀ {A} (d : ∅ ⊢ A) {HA : HighTy A} {Hd : HighDn d {HA}} → ∅ ⊢ lower′ A {HA}
unint′ d {HA} {Hd} with can-unint d {HA}
unint′ d {HA} {Hd} | just d′ = d′
unint′ d {HA} {()} | nothing

unnec′ : ∀ {A} (d : ∅ ⊢ A) {HA : HighTy A} {Hd : HighDn d {HA}} → ∅ ⊢ lower′ A {HA}
unnec′ = unint′
