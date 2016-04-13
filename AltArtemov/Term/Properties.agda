module AltArtemov.Term.Properties where

open import Data.Nat using (ℕ ; zero ; suc ; _⊓_ ; _<′_ ; pred) renaming (_≟_ to _ℕ≟_)
open import Function using (_∘_)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Nullary using (yes ; no)

open import AltArtemov.Term.Core
open import AltArtemov.Term.Inversions
open import Data.Nat.Missing


-- Terms have levels.
lev : ∀ t → ℕ
lev (var[ n ] i)    = n
lev (lam[ n ] t)    = n ⊓ lev t
lev (app[ n ] t s)  = n ⊓ lev t ⊓ lev s
lev (up[ n ] t)     = n ⊓ lev t
lev (down[ n ] t)   = n ⊓ lev t


-- Terms can be quoted.
quo : ∀ t → Tm
quo (var[ n ] i)   = var[ suc n ] i
quo (lam[ n ] t)   = lam[ suc n ] (quo t)
quo (app[ n ] t s) = app[ suc n ] (quo t) (quo s)
quo (up[ n ] t)    = up[ suc n ] (quo t)
quo (down[ n ] t)  = down[ suc n ] (quo t)


-- Quoting a term increments its level.
lev-quo-t≡suc-lev-t : ∀ t → lev (quo t) ≡ suc (lev t)
lev-quo-t≡suc-lev-t (var[ n ] i)   = refl
lev-quo-t≡suc-lev-t (lam[ n ] t)   rewrite lev-quo-t≡suc-lev-t t = refl
lev-quo-t≡suc-lev-t (app[ n ] t s) rewrite lev-quo-t≡suc-lev-t t | lev-quo-t≡suc-lev-t s = refl
lev-quo-t≡suc-lev-t (up[ n ] t)    rewrite lev-quo-t≡suc-lev-t t = refl
lev-quo-t≡suc-lev-t (down[ n ] t)  rewrite lev-quo-t≡suc-lev-t t = refl


-- The level of a quoted term is greater than 0.
z<′lev-quo-t : ∀ t → zero <′ lev (quo t)
z<′lev-quo-t (var[ n ] i)   = z<′sn
z<′lev-quo-t (lam[ n ] t)   rewrite lev-quo-t≡suc-lev-t t = z<′sn
z<′lev-quo-t (app[ n ] t s) rewrite lev-quo-t≡suc-lev-t t | lev-quo-t≡suc-lev-t s = z<′sn
z<′lev-quo-t (up[ n ] t)    rewrite lev-quo-t≡suc-lev-t t = z<′sn
z<′lev-quo-t (down[ n ] t)  rewrite lev-quo-t≡suc-lev-t t = z<′sn


-- Terms of level greater than 0 can be unquoted.
unquo : ∀ t → zero <′ lev t → Tm
unquo (var[ zero ] i)    ()
unquo (lam[ zero ] t)    ()
unquo (app[ zero ] t s)  ()
unquo (up[ zero ] t)     ()
unquo (down[ zero ] t)   ()
unquo (var[ suc n ] i)   z<′l = var[ n ] i
unquo (lam[ suc n ] t)   z<′l = lam[ n ] (unquo t (z<′sm⊓n⇒z<′n z<′l))
unquo (app[ suc n ] t s) z<′l = app[ n ] (unquo t (z<′sm⊓n⊓o⇒z<′n (lev s) z<′l))
                                         (unquo s (z<′sm⊓n⊓o⇒z<′o (lev t) z<′l))
unquo (up[ suc n ] t)    z<′l = up[ n ] (unquo t (z<′sm⊓n⇒z<′n z<′l))
unquo (down[ suc n ] t)  z<′l = down[ n ] (unquo t (z<′sm⊓n⇒z<′n z<′l))


-- Unquoting a term decrements its level.
lev-unquo-t≡pred-lev-t : ∀ t (z<′l : zero <′ lev t) → lev (unquo t z<′l) ≡ pred (lev t)
lev-unquo-t≡pred-lev-t (var[ zero ] i)    ()
lev-unquo-t≡pred-lev-t (lam[ zero ] t)    ()
lev-unquo-t≡pred-lev-t (app[ zero ] t s)  ()
lev-unquo-t≡pred-lev-t (up[ zero ] t)     ()
lev-unquo-t≡pred-lev-t (down[ zero ] t)   ()
lev-unquo-t≡pred-lev-t (var[ suc n ] i)   z<′l = refl
lev-unquo-t≡pred-lev-t (lam[ suc n ] t)   z<′l rewrite lev-unquo-t≡pred-lev-t t (z<′sm⊓n⇒z<′n z<′l) = m⊓pn≡p[sm⊓n] n (lev t)
lev-unquo-t≡pred-lev-t (app[ suc n ] t s) z<′l rewrite lev-unquo-t≡pred-lev-t t (z<′sm⊓n⊓o⇒z<′n (lev s) z<′l)
                                                     | lev-unquo-t≡pred-lev-t s (z<′sm⊓n⊓o⇒z<′o (lev t) z<′l) = m⊓pn⊓po≡p[sm⊓n⊓o] n (lev t) (lev s)
lev-unquo-t≡pred-lev-t (up[ suc n ] t)    z<′l rewrite lev-unquo-t≡pred-lev-t t (z<′sm⊓n⇒z<′n z<′l) = m⊓pn≡p[sm⊓n] n (lev t)
lev-unquo-t≡pred-lev-t (down[ suc n ] t)  z<′l rewrite lev-unquo-t≡pred-lev-t t (z<′sm⊓n⇒z<′n z<′l) = m⊓pn≡p[sm⊓n] n (lev t)



-- Unquoting after quoting is identity.
unquo-quo-t≡t : ∀ t → unquo (quo t) (z<′lev-quo-t t) ≡ t
unquo-quo-t≡t t = aux t (z<′lev-quo-t t)
  where
    aux : ∀ t (z<′l : zero <′ lev (quo t)) → unquo (quo t) z<′l ≡ t    -- TODO: Simplify!
    aux (var[ n ] i)   z<′l = refl
    aux (lam[ n ] t)   z<′l rewrite aux t (z<′sm⊓n⇒z<′n z<′l) = refl
    aux (app[ n ] t s) z<′l rewrite aux t (z<′sm⊓n⊓o⇒z<′n (lev (quo s)) z<′l)
                                  | aux s (z<′sm⊓n⊓o⇒z<′o (lev (quo t)) z<′l) = refl
    aux (up[ n ] t)    z<′l rewrite aux t (z<′sm⊓n⇒z<′n z<′l) = refl
    aux (down[ n ] t)  z<′l rewrite aux t (z<′sm⊓n⇒z<′n z<′l) = refl


-- Quoting after unquoting is identity.
quo-unquo-t≡t : ∀ t (z<′l : zero <′ lev t) → quo (unquo t z<′l) ≡ t
quo-unquo-t≡t (var[ zero ] i)    ()
quo-unquo-t≡t (lam[ zero ] t)    ()
quo-unquo-t≡t (app[ zero ] t s)  ()
quo-unquo-t≡t (up[ zero ] t)     ()
quo-unquo-t≡t (down[ zero ] t)   ()
quo-unquo-t≡t (var[ suc n ] i)   z<′l = refl
quo-unquo-t≡t (lam[ suc n ] t)   z<′l rewrite quo-unquo-t≡t t (z<′sm⊓n⇒z<′n z<′l) = refl
quo-unquo-t≡t (app[ suc n ] t s) z<′l rewrite quo-unquo-t≡t t (z<′sm⊓n⊓o⇒z<′n (lev s) z<′l)
                                            | quo-unquo-t≡t s (z<′sm⊓n⊓o⇒z<′o (lev t) z<′l) = refl
quo-unquo-t≡t (up[ suc n ] t)    z<′l rewrite quo-unquo-t≡t t (z<′sm⊓n⇒z<′n z<′l) = refl
quo-unquo-t≡t (down[ suc n ] t)  z<′l rewrite quo-unquo-t≡t t (z<′sm⊓n⇒z<′n z<′l) = refl


-- Term equality is decidable.
_≟_ : Decidable {A = Tm} _≡_
var[ n ] i   ≟ var[ n′ ] i′    with n ℕ≟ n′ | i ℕ≟ i′
var[ n ] i   ≟ var[ .n ] .i    | yes refl | yes refl = yes refl
...                            | no  n≢n′ | _        = no (n≢n′ ∘ var-inv-n)
...                            | _        | no  i≢i′ = no (i≢i′ ∘ var-inv-i)
var[ _ ] i   ≟ lam[ _ ] t′    = no λ ()
var[ _ ] i   ≟ app[ _ ] t′ s′ = no λ ()
var[ _ ] i   ≟ up[ _ ] t′     = no λ ()
var[ _ ] i   ≟ down[ _ ] t′   = no λ ()
lam[ _ ] t   ≟ var[ _ ] i′    = no λ ()
lam[ n ] t   ≟ lam[ n′ ] t′    with n ℕ≟ n′ | t ≟ t′
lam[ n ] t   ≟ lam[ .n ] .t    | yes refl | yes refl = yes refl
...                            | no  n≢n′ | _        = no (n≢n′ ∘ lam-inv-n)
...                            | _        | no  t≢t′ = no (t≢t′ ∘ lam-inv-t)
lam[ _ ] t   ≟ app[ _ ] t′ s′ = no λ ()
lam[ _ ] t   ≟ up[ _ ] t′     = no λ ()
lam[ _ ] t   ≟ down[ _ ] t′   = no λ ()
app[ _ ] t s ≟ var[ _ ] i′    = no λ ()
app[ _ ] t s ≟ lam[ _ ] t′    = no λ ()
app[ n ] t s ≟ app[ n′ ] t′ s′ with n ℕ≟ n′ | t ≟ t′ | s ≟ s′
app[ n ] t s ≟ app[ .n ] .t .s | yes refl | yes refl | yes refl = yes refl
...                            | no  n≢n′ | _        | _        = no (n≢n′ ∘ app-inv-n)
...                            | _        | no  t≢t′ | _        = no (t≢t′ ∘ app-inv-t)
...                            | _        | _        | no  s≢s′ = no (s≢s′ ∘ app-inv-s)
app[ _ ] t s ≟ up[ _ ] t′     = no λ ()
app[ _ ] t s ≟ down[ _ ] t′   = no λ ()
up[ _ ] t    ≟ var[ _ ] i′    = no λ ()
up[ _ ] t    ≟ lam[ _ ] t′    = no λ ()
up[ _ ] t    ≟ app[ _ ] t′ s′ = no λ ()
up[ n ] t    ≟ up[ n′ ] t′     with n ℕ≟ n′ | t ≟ t′
up[ n ] t    ≟ up[ .n ] .t     | yes refl | yes refl = yes refl
...                            | no  n≢n′ | _        = no (n≢n′ ∘ up-inv-n)
...                            | _        | no  t≢t′ = no (t≢t′ ∘ up-inv-t)
up[ _ ] t    ≟ down[ _ ] t′   = no λ ()
down[ _ ] t  ≟ var[ _ ] i′    = no λ ()
down[ _ ] t  ≟ lam[ _ ] t′    = no λ ()
down[ _ ] t  ≟ app[ _ ] t′ s′ = no λ ()
down[ _ ] t  ≟ up[ _ ] t′     = no λ ()
down[ n ] t  ≟ down[ n′ ] t′   with n ℕ≟ n′ | t ≟ t′
down[ n ] t  ≟ down[ .n ] .t   | yes refl | yes refl = yes refl
...                            | no  n≢n′ | _        = no (n≢n′ ∘ down-inv-n)
...                            | _        | no  t≢t′ = no (t≢t′ ∘ down-inv-t)
