module AltArtemov.Term.Properties where

open import Data.Empty using () renaming (⊥ to Empty)
open import Data.Nat using (ℕ ; zero ; suc ; _⊓_ ; _<′_ ; pred) renaming (_≟_ to _ℕ≟_)
open import Data.Maybe using (Maybe ; nothing ; just)
open import Data.Unit using () renaming (⊤ to Unit)
open import Function using (_∘_)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; subst)
open import Relation.Nullary using (yes ; no)

open import AltArtemov.Term.Core
open import AltArtemov.Term.Inversions
open import Data.Nat.Missing


-- Terms have levels.
lev : ∀ t → ℕ
lev (VAR[ n ] i)    = n
lev (LAM[ n ] t)    = n ⊓ lev t
lev (APP[ n ] t s)  = n ⊓ lev t ⊓ lev s
lev (PAIR[ n ] t s) = n ⊓ lev t ⊓ lev s
lev (FST[ n ] t)    = n ⊓ lev t
lev (SND[ n ] t)    = n ⊓ lev t
lev (UP[ n ] t)     = n ⊓ lev t
lev (DOWN[ n ] t)   = n ⊓ lev t
lev (BOOM[ n ] t)   = n ⊓ lev t


-- Terms can be quoted.
quo : ∀ t → Tm
quo (VAR[ n ] i)    = VAR[ suc n ] i
quo (LAM[ n ] t)    = LAM[ suc n ] (quo t)
quo (APP[ n ] t s)  = APP[ suc n ] (quo t) (quo s)
quo (PAIR[ n ] t s) = PAIR[ suc n ] (quo t) (quo s)
quo (FST[ n ] t)    = FST[ suc n ] (quo t)
quo (SND[ n ] t)    = SND[ suc n ] (quo t)
quo (UP[ n ] t)     = UP[ suc n ] (quo t)
quo (DOWN[ n ] t)   = DOWN[ suc n ] (quo t)
quo (BOOM[ n ] t)   = BOOM[ suc n ] (quo t)


-- Quoting a term increments its level.
lev-quo-t≡suc-lev-t : ∀ t → lev (quo t) ≡ suc (lev t)
lev-quo-t≡suc-lev-t (VAR[ n ] i)    = refl
lev-quo-t≡suc-lev-t (LAM[ n ] t)    rewrite lev-quo-t≡suc-lev-t t = refl
lev-quo-t≡suc-lev-t (APP[ n ] t s)  rewrite lev-quo-t≡suc-lev-t t | lev-quo-t≡suc-lev-t s = refl
lev-quo-t≡suc-lev-t (PAIR[ n ] t s) rewrite lev-quo-t≡suc-lev-t t | lev-quo-t≡suc-lev-t s = refl
lev-quo-t≡suc-lev-t (FST[ n ] t)    rewrite lev-quo-t≡suc-lev-t t = refl
lev-quo-t≡suc-lev-t (SND[ n ] t)    rewrite lev-quo-t≡suc-lev-t t = refl
lev-quo-t≡suc-lev-t (UP[ n ] t)     rewrite lev-quo-t≡suc-lev-t t = refl
lev-quo-t≡suc-lev-t (DOWN[ n ] t)   rewrite lev-quo-t≡suc-lev-t t = refl
lev-quo-t≡suc-lev-t (BOOM[ n ] t)   rewrite lev-quo-t≡suc-lev-t t = refl


-- The level of a quoted term is greater than 0.
z<′lev-quo-t : ∀ t → zero <′ lev (quo t)
z<′lev-quo-t (VAR[ n ] i)    = z<′sn
z<′lev-quo-t (LAM[ n ] t)    rewrite lev-quo-t≡suc-lev-t t = z<′sn
z<′lev-quo-t (APP[ n ] t s)  rewrite lev-quo-t≡suc-lev-t t | lev-quo-t≡suc-lev-t s = z<′sn
z<′lev-quo-t (PAIR[ n ] t s) rewrite lev-quo-t≡suc-lev-t t | lev-quo-t≡suc-lev-t s = z<′sn
z<′lev-quo-t (FST[ n ] t)    rewrite lev-quo-t≡suc-lev-t t = z<′sn
z<′lev-quo-t (SND[ n ] t)    rewrite lev-quo-t≡suc-lev-t t = z<′sn
z<′lev-quo-t (UP[ n ] t)     rewrite lev-quo-t≡suc-lev-t t = z<′sn
z<′lev-quo-t (DOWN[ n ] t)   rewrite lev-quo-t≡suc-lev-t t = z<′sn
z<′lev-quo-t (BOOM[ n ] t)   rewrite lev-quo-t≡suc-lev-t t = z<′sn


-- Terms of level greater than 0 can be unquoted.
unquo : ∀ t (z<′l : zero <′ lev t) → Tm
unquo (VAR[ zero ] i)     ()
unquo (LAM[ zero ] t)     ()
unquo (APP[ zero ] t s)   ()
unquo (PAIR[ zero ] t s)  ()
unquo (FST[ zero ] t)     ()
unquo (SND[ zero ] t)     ()
unquo (UP[ zero ] t)      ()
unquo (DOWN[ zero ] t)    ()
unquo (BOOM[ zero ] t)    ()
unquo (VAR[ suc n ] i)    z<′l = VAR[ n ] i
unquo (LAM[ suc n ] t)    z<′l = LAM[ n ] (unquo t (z<′sm⊓n⇒z<′n z<′l))
unquo (APP[ suc n ] t s)  z<′l = APP[ n ] (unquo t (z<′sm⊓n⊓o⇒z<′n (lev s) z<′l))
                                          (unquo s (z<′sm⊓n⊓o⇒z<′o (lev t) z<′l))
unquo (PAIR[ suc n ] t s) z<′l = PAIR[ n ] (unquo t (z<′sm⊓n⊓o⇒z<′n (lev s) z<′l))
                                           (unquo s (z<′sm⊓n⊓o⇒z<′o (lev t) z<′l))
unquo (FST[ suc n ] t)    z<′l = FST[ n ] (unquo t (z<′sm⊓n⇒z<′n z<′l))
unquo (SND[ suc n ] t)    z<′l = SND[ n ] (unquo t (z<′sm⊓n⇒z<′n z<′l))
unquo (UP[ suc n ] t)     z<′l = UP[ n ] (unquo t (z<′sm⊓n⇒z<′n z<′l))
unquo (DOWN[ suc n ] t)   z<′l = DOWN[ n ] (unquo t (z<′sm⊓n⇒z<′n z<′l))
unquo (BOOM[ suc n ] t)   z<′l = BOOM[ n ] (unquo t (z<′sm⊓n⇒z<′n z<′l))


-- Unquoting a term decrements its level.
lev-unquo-t≡pred-lev-t : ∀ t (z<′l : zero <′ lev t) → lev (unquo t z<′l) ≡ pred (lev t)
lev-unquo-t≡pred-lev-t (VAR[ zero ] i)     ()
lev-unquo-t≡pred-lev-t (LAM[ zero ] t)     ()
lev-unquo-t≡pred-lev-t (APP[ zero ] t s)   ()
lev-unquo-t≡pred-lev-t (PAIR[ zero ] t s)  ()
lev-unquo-t≡pred-lev-t (FST[ zero ] t)     ()
lev-unquo-t≡pred-lev-t (SND[ zero ] t)     ()
lev-unquo-t≡pred-lev-t (UP[ zero ] t)      ()
lev-unquo-t≡pred-lev-t (DOWN[ zero ] t)    ()
lev-unquo-t≡pred-lev-t (BOOM[ zero ] t)    ()
lev-unquo-t≡pred-lev-t (VAR[ suc n ] i)    z<′l = refl
lev-unquo-t≡pred-lev-t (LAM[ suc n ] t)    z<′l rewrite lev-unquo-t≡pred-lev-t t (z<′sm⊓n⇒z<′n z<′l) = m⊓pn≡p[sm⊓n] n (lev t)
lev-unquo-t≡pred-lev-t (APP[ suc n ] t s)  z<′l rewrite lev-unquo-t≡pred-lev-t t (z<′sm⊓n⊓o⇒z<′n (lev s) z<′l)
                                                      | lev-unquo-t≡pred-lev-t s (z<′sm⊓n⊓o⇒z<′o (lev t) z<′l) = m⊓pn⊓po≡p[sm⊓n⊓o] n (lev t) (lev s)
lev-unquo-t≡pred-lev-t (PAIR[ suc n ] t s) z<′l rewrite lev-unquo-t≡pred-lev-t t (z<′sm⊓n⊓o⇒z<′n (lev s) z<′l)
                                                      | lev-unquo-t≡pred-lev-t s (z<′sm⊓n⊓o⇒z<′o (lev t) z<′l) = m⊓pn⊓po≡p[sm⊓n⊓o] n (lev t) (lev s)
lev-unquo-t≡pred-lev-t (FST[ suc n ] t)    z<′l rewrite lev-unquo-t≡pred-lev-t t (z<′sm⊓n⇒z<′n z<′l) = m⊓pn≡p[sm⊓n] n (lev t)
lev-unquo-t≡pred-lev-t (SND[ suc n ] t)    z<′l rewrite lev-unquo-t≡pred-lev-t t (z<′sm⊓n⇒z<′n z<′l) = m⊓pn≡p[sm⊓n] n (lev t)
lev-unquo-t≡pred-lev-t (UP[ suc n ] t)     z<′l rewrite lev-unquo-t≡pred-lev-t t (z<′sm⊓n⇒z<′n z<′l) = m⊓pn≡p[sm⊓n] n (lev t)
lev-unquo-t≡pred-lev-t (DOWN[ suc n ] t)   z<′l rewrite lev-unquo-t≡pred-lev-t t (z<′sm⊓n⇒z<′n z<′l) = m⊓pn≡p[sm⊓n] n (lev t)
lev-unquo-t≡pred-lev-t (BOOM[ suc n ] t)   z<′l rewrite lev-unquo-t≡pred-lev-t t (z<′sm⊓n⇒z<′n z<′l) = m⊓pn≡p[sm⊓n] n (lev t)


-- Unquoting after quoting is identity.
unquo-quo-t≡t : ∀ t → unquo (quo t) (z<′lev-quo-t t) ≡ t
unquo-quo-t≡t t = aux t (z<′lev-quo-t t)
  where
    aux : ∀ t (z<′l : zero <′ lev (quo t)) → unquo (quo t) z<′l ≡ t    -- TODO: Simplify!
    aux (VAR[ n ] i)    z<′l = refl
    aux (LAM[ n ] t)    z<′l rewrite aux t (z<′sm⊓n⇒z<′n z<′l) = refl
    aux (APP[ n ] t s)  z<′l rewrite aux t (z<′sm⊓n⊓o⇒z<′n (lev (quo s)) z<′l)
                                   | aux s (z<′sm⊓n⊓o⇒z<′o (lev (quo t)) z<′l) = refl
    aux (PAIR[ n ] t s) z<′l rewrite aux t (z<′sm⊓n⊓o⇒z<′n (lev (quo s)) z<′l)
                                   | aux s (z<′sm⊓n⊓o⇒z<′o (lev (quo t)) z<′l) = refl
    aux (FST[ n ] t)    z<′l rewrite aux t (z<′sm⊓n⇒z<′n z<′l) = refl
    aux (SND[ n ] t)    z<′l rewrite aux t (z<′sm⊓n⇒z<′n z<′l) = refl
    aux (UP[ n ] t)     z<′l rewrite aux t (z<′sm⊓n⇒z<′n z<′l) = refl
    aux (DOWN[ n ] t)   z<′l rewrite aux t (z<′sm⊓n⇒z<′n z<′l) = refl
    aux (BOOM[ n ] t)   z<′l rewrite aux t (z<′sm⊓n⇒z<′n z<′l) = refl


-- Quoting after unquoting is identity.
quo-unquo-t≡t : ∀ t (z<′l : zero <′ lev t) → quo (unquo t z<′l) ≡ t
quo-unquo-t≡t (VAR[ zero ] i)     ()
quo-unquo-t≡t (LAM[ zero ] t)     ()
quo-unquo-t≡t (APP[ zero ] t s)   ()
quo-unquo-t≡t (PAIR[ zero ] t s)  ()
quo-unquo-t≡t (FST[ zero ] t)     ()
quo-unquo-t≡t (SND[ zero ] t)     ()
quo-unquo-t≡t (UP[ zero ] t)      ()
quo-unquo-t≡t (DOWN[ zero ] t)    ()
quo-unquo-t≡t (BOOM[ zero ] t)    ()
quo-unquo-t≡t (VAR[ suc n ] i)    z<′l = refl
quo-unquo-t≡t (LAM[ suc n ] t)    z<′l rewrite quo-unquo-t≡t t (z<′sm⊓n⇒z<′n z<′l) = refl
quo-unquo-t≡t (APP[ suc n ] t s)  z<′l rewrite quo-unquo-t≡t t (z<′sm⊓n⊓o⇒z<′n (lev s) z<′l)
                                             | quo-unquo-t≡t s (z<′sm⊓n⊓o⇒z<′o (lev t) z<′l) = refl
quo-unquo-t≡t (PAIR[ suc n ] t s) z<′l rewrite quo-unquo-t≡t t (z<′sm⊓n⊓o⇒z<′n (lev s) z<′l)
                                             | quo-unquo-t≡t s (z<′sm⊓n⊓o⇒z<′o (lev t) z<′l) = refl
quo-unquo-t≡t (FST[ suc n ] t)    z<′l rewrite quo-unquo-t≡t t (z<′sm⊓n⇒z<′n z<′l) = refl
quo-unquo-t≡t (SND[ suc n ] t)    z<′l rewrite quo-unquo-t≡t t (z<′sm⊓n⇒z<′n z<′l) = refl
quo-unquo-t≡t (UP[ suc n ] t)     z<′l rewrite quo-unquo-t≡t t (z<′sm⊓n⇒z<′n z<′l) = refl
quo-unquo-t≡t (DOWN[ suc n ] t)   z<′l rewrite quo-unquo-t≡t t (z<′sm⊓n⇒z<′n z<′l) = refl
quo-unquo-t≡t (BOOM[ suc n ] t)   z<′l rewrite quo-unquo-t≡t t (z<′sm⊓n⇒z<′n z<′l) = refl


-- Term equality is decidable.
_≟_ : Decidable {A = Tm} _≡_
VAR[ n ] i    ≟ VAR[ n′ ] i′     with n ℕ≟ n′ | i ℕ≟ i′
VAR[ n ] i    ≟ VAR[ .n ] .i     | yes refl | yes refl = yes refl
...                              | no  n≢n′ | _        = no (n≢n′ ∘ VAR-inv-n)
...                              | _        | no  i≢i′ = no (i≢i′ ∘ VAR-inv-i)
VAR[ _ ] _    ≟ LAM[ _ ] _       = no λ ()
VAR[ _ ] _    ≟ APP[ _ ] _ _     = no λ ()
VAR[ _ ] _    ≟ PAIR[ _ ] _ _    = no λ ()
VAR[ _ ] _    ≟ FST[ _ ] _       = no λ ()
VAR[ _ ] _    ≟ SND[ _ ] _       = no λ ()
VAR[ _ ] _    ≟ UP[ _ ] _        = no λ ()
VAR[ _ ] _    ≟ DOWN[ _ ] _      = no λ ()
VAR[ _ ] _    ≟ BOOM[ _ ] _      = no λ ()
LAM[ _ ] _    ≟ VAR[ _ ] _       = no λ ()
LAM[ n ] t    ≟ LAM[ n′ ] t′     with n ℕ≟ n′ | t ≟ t′
LAM[ n ] t    ≟ LAM[ .n ] .t     | yes refl | yes refl = yes refl
...                              | no  n≢n′ | _        = no (n≢n′ ∘ LAM-inv-n)
...                              | _        | no  t≢t′ = no (t≢t′ ∘ LAM-inv-t)
LAM[ _ ] _    ≟ APP[ _ ] _ _     = no λ ()
LAM[ _ ] _    ≟ PAIR[ _ ] _ _    = no λ ()
LAM[ _ ] _    ≟ FST[ _ ] _       = no λ ()
LAM[ _ ] _    ≟ SND[ _ ] _       = no λ ()
LAM[ _ ] _    ≟ UP[ _ ] _        = no λ ()
LAM[ _ ] _    ≟ DOWN[ _ ] _      = no λ ()
LAM[ _ ] _    ≟ BOOM[ _ ] _      = no λ ()
APP[ _ ] _ _  ≟ VAR[ _ ] _       = no λ ()
APP[ _ ] _ _  ≟ LAM[ _ ] _       = no λ ()
APP[ n ] t s  ≟ APP[ n′ ] t′ s′  with n ℕ≟ n′ | t ≟ t′ | s ≟ s′
APP[ n ] t s  ≟ APP[ .n ] .t .s  | yes refl | yes refl | yes refl = yes refl
...                              | no  n≢n′ | _        | _        = no (n≢n′ ∘ APP-inv-n)
...                              | _        | no  t≢t′ | _        = no (t≢t′ ∘ APP-inv-t)
...                              | _        | _        | no  s≢s′ = no (s≢s′ ∘ APP-inv-s)
APP[ _ ] _ _  ≟ PAIR[ _ ] _ _    = no λ ()
APP[ _ ] _ _  ≟ FST[ _ ] _       = no λ ()
APP[ _ ] _ _  ≟ SND[ _ ] _       = no λ ()
APP[ _ ] _ _  ≟ UP[ _ ] _        = no λ ()
APP[ _ ] _ _  ≟ DOWN[ _ ] _      = no λ ()
APP[ _ ] _ _  ≟ BOOM[ _ ] _      = no λ ()
PAIR[ _ ] _ _ ≟ VAR[ _ ] _       = no λ ()
PAIR[ _ ] _ _ ≟ LAM[ _ ] _       = no λ ()
PAIR[ _ ] _ _ ≟ APP[ _ ] _ _     = no λ ()
PAIR[ n ] t s ≟ PAIR[ n′ ] t′ s′ with n ℕ≟ n′ | t ≟ t′ | s ≟ s′
PAIR[ n ] t s ≟ PAIR[ .n ] .t .s | yes refl | yes refl | yes refl = yes refl
...                              | no  n≢n′ | _        | _        = no (n≢n′ ∘ PAIR-inv-n)
...                              | _        | no  t≢t′ | _        = no (t≢t′ ∘ PAIR-inv-t)
...                              | _        | _        | no  s≢s′ = no (s≢s′ ∘ PAIR-inv-s)
PAIR[ _ ] _ _ ≟ FST[ _ ] _       = no λ ()
PAIR[ _ ] _ _ ≟ SND[ _ ] _       = no λ ()
PAIR[ _ ] _ _ ≟ UP[ _ ] _        = no λ ()
PAIR[ _ ] _ _ ≟ DOWN[ _ ] _      = no λ ()
PAIR[ _ ] _ _ ≟ BOOM[ _ ] _      = no λ ()
FST[ _ ] _    ≟ VAR[ _ ] _       = no λ ()
FST[ _ ] _    ≟ LAM[ _ ] _       = no λ ()
FST[ _ ] _    ≟ APP[ _ ] _ _     = no λ ()
FST[ _ ] _    ≟ PAIR[ _ ] _ _    = no λ ()
FST[ n ] t    ≟ FST[ n′ ] t′     with n ℕ≟ n′ | t ≟ t′
FST[ n ] t    ≟ FST[ .n ] .t     | yes refl | yes refl = yes refl
...                              | no  n≢n′ | _        = no (n≢n′ ∘ FST-inv-n)
...                              | _        | no  t≢t′ = no (t≢t′ ∘ FST-inv-t)
FST[ _ ] _    ≟ SND[ _ ] _       = no λ ()
FST[ _ ] _    ≟ UP[ _ ] _        = no λ ()
FST[ _ ] _    ≟ DOWN[ _ ] _      = no λ ()
FST[ _ ] _    ≟ BOOM[ _ ] _      = no λ ()
SND[ _ ] _    ≟ VAR[ _ ] _       = no λ ()
SND[ _ ] _    ≟ LAM[ _ ] _       = no λ ()
SND[ _ ] _    ≟ APP[ _ ] _ _     = no λ ()
SND[ _ ] _    ≟ PAIR[ _ ] _ _    = no λ ()
SND[ _ ] _    ≟ FST[ _ ] _       = no λ ()
SND[ n ] t    ≟ SND[ n′ ] t′     with n ℕ≟ n′ | t ≟ t′
SND[ n ] t    ≟ SND[ .n ] .t     | yes refl | yes refl = yes refl
...                              | no  n≢n′ | _        = no (n≢n′ ∘ SND-inv-n)
...                              | _        | no  t≢t′ = no (t≢t′ ∘ SND-inv-t)
SND[ _ ] _    ≟ UP[ _ ] _        = no λ ()
SND[ _ ] _    ≟ DOWN[ _ ] _      = no λ ()
SND[ _ ] _    ≟ BOOM[ _ ] _      = no λ ()
UP[ _ ] _     ≟ VAR[ _ ] _       = no λ ()
UP[ _ ] _     ≟ LAM[ _ ] _       = no λ ()
UP[ _ ] _     ≟ APP[ _ ] _ _     = no λ ()
UP[ _ ] _     ≟ PAIR[ _ ] _ _    = no λ ()
UP[ _ ] _     ≟ FST[ _ ] _       = no λ ()
UP[ _ ] _     ≟ SND[ _ ] _       = no λ ()
UP[ n ] t     ≟ UP[ n′ ] t′      with n ℕ≟ n′ | t ≟ t′
UP[ n ] t     ≟ UP[ .n ] .t      | yes refl | yes refl = yes refl
...                              | no  n≢n′ | _        = no (n≢n′ ∘ UP-inv-n)
...                              | _        | no  t≢t′ = no (t≢t′ ∘ UP-inv-t)
UP[ _ ] _     ≟ DOWN[ _ ] _      = no λ ()
UP[ _ ] _     ≟ BOOM[ _ ] _      = no λ ()
DOWN[ _ ] _   ≟ VAR[ _ ] _       = no λ ()
DOWN[ _ ] _   ≟ LAM[ _ ] _       = no λ ()
DOWN[ _ ] _   ≟ APP[ _ ] _ _     = no λ ()
DOWN[ _ ] _   ≟ PAIR[ _ ] _ _    = no λ ()
DOWN[ _ ] _   ≟ FST[ _ ] _       = no λ ()
DOWN[ _ ] _   ≟ SND[ _ ] _       = no λ ()
DOWN[ _ ] _   ≟ UP[ _ ] _        = no λ ()
DOWN[ n ] t   ≟ DOWN[ n′ ] t′    with n ℕ≟ n′ | t ≟ t′
DOWN[ n ] t   ≟ DOWN[ .n ] .t    | yes refl | yes refl = yes refl
...                              | no  n≢n′ | _        = no (n≢n′ ∘ DOWN-inv-n)
...                              | _        | no  t≢t′ = no (t≢t′ ∘ DOWN-inv-t)
DOWN[ _ ] _   ≟ BOOM[ _ ] _      = no λ ()
BOOM[ _ ] _   ≟ VAR[ _ ] _       = no λ ()
BOOM[ _ ] _   ≟ LAM[ _ ] _       = no λ ()
BOOM[ _ ] _   ≟ APP[ _ ] _ _     = no λ ()
BOOM[ _ ] _   ≟ PAIR[ _ ] _ _    = no λ ()
BOOM[ _ ] _   ≟ FST[ _ ] _       = no λ ()
BOOM[ _ ] _   ≟ SND[ _ ] _       = no λ ()
BOOM[ _ ] _   ≟ UP[ _ ] _        = no λ ()
BOOM[ _ ] _   ≟ DOWN[ _ ] _      = no λ ()
BOOM[ n ] t   ≟ BOOM[ n′ ] t′    with n ℕ≟ n′ | t ≟ t′
BOOM[ n ] t   ≟ BOOM[ .n ] .t    | yes refl | yes refl = yes refl
...                              | no  n≢n′ | _        = no (n≢n′ ∘ BOOM-inv-n)
...                              | _        | no  t≢t′ = no (t≢t′ ∘ BOOM-inv-t)


-- TODO

can-unquo : ∀ t → Maybe Tm
can-unquo t with lev t
...           | zero  = nothing
...           | suc n with suc n ℕ≟ lev t
...                   | no  sn≢l = nothing
...                   | yes sn≡l = just (unquo t (subst (λ n → zero <′ n) sn≡l z<′sn))

HighTm : ∀ t → Set
HighTm t with can-unquo t
...      | just t′ = Unit
...      | _       = Empty

unquo′ : ∀ t {Ht : HighTm t} → Tm
unquo′ t {Ht} with can-unquo t
unquo′ t {Ht} | just t′ = t′
unquo′ t {()} | nothing
