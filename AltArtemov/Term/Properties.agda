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
lev (var[ n ] i)   = n
lev (lam[ n ] t)   = n ⊓ lev t
lev (app[ n ] t s) = n ⊓ lev t ⊓ lev s


-- Terms can be quoted.
quo : ∀ t → Tm
quo (var[ n ] i)   = var[ suc n ] i
quo (lam[ n ] t)   = lam[ suc n ] (quo t)
quo (app[ n ] t s) = app[ suc n ] (quo t) (quo s)


-- Quoting a term increments its level.
lev-quo-t≡suc-lev-t : ∀ t → lev (quo t) ≡ suc (lev t)
lev-quo-t≡suc-lev-t (var[ n ] i)   = refl
lev-quo-t≡suc-lev-t (lam[ n ] t)   rewrite lev-quo-t≡suc-lev-t t = refl
lev-quo-t≡suc-lev-t (app[ n ] t s) rewrite lev-quo-t≡suc-lev-t t | lev-quo-t≡suc-lev-t s = refl


-- The level of a quoted term is greater than 0.
z<′lev-quo-t : ∀ t → zero <′ lev (quo t)
z<′lev-quo-t (var[ n ] i)   = z<′sn
z<′lev-quo-t (lam[ n ] t)   rewrite lev-quo-t≡suc-lev-t t = z<′sn
z<′lev-quo-t (app[ n ] t s) rewrite lev-quo-t≡suc-lev-t t | lev-quo-t≡suc-lev-t s = z<′sn


next-lev-un : ∀ {n} t → zero <′ suc n ⊓ lev t → zero <′ lev t
next-lev-un {n} t z<′l = <′-dropᴸ-⊓ (suc n) z<′l

next-lev-binᴸ : ∀ {n} t s → zero <′ suc n ⊓ lev t ⊓ lev s → zero <′ lev t
next-lev-binᴸ {n} t s z<′l = <′-dropᴸ-⊓ (suc n) (<′-dropᴿ-⊓ (lev s) z<′l)

next-lev-binᴿ : ∀ {n} t s → zero <′ suc n ⊓ lev t ⊓ lev s → zero <′ lev s
next-lev-binᴿ {n} t s z<′l = <′-dropᴸ-⊓ (suc n ⊓ lev t) z<′l


lm1 : ∀ m n → m ⊓ pred n ≡ pred (suc m ⊓ n)  -- TODO: Rename!
lm1 m zero    rewrite ⊓-comm m zero = refl
lm1 m (suc n) rewrite ⊓-comm m n    = refl

postulate
  lm2 : ∀ m n o → (m ⊓ pred n) ⊓ pred o ≡ pred ((suc m ⊓ n) ⊓ o)  -- TODO: Prove! Rename!


-- Terms of level greater than 0 can be unquoted.
unquo : ∀ t → zero <′ lev t → Tm
unquo (var[ zero ] i)    ()
unquo (lam[ zero ] t)    ()
unquo (app[ zero ] t s)  ()
unquo (var[ suc n ] i)   z<′l = var[ n ] i
unquo (lam[ suc n ] t)   z<′l = lam[ n ] (unquo t (next-lev-un t z<′l))
unquo (app[ suc n ] t s) z<′l = app[ n ] (unquo t (next-lev-binᴸ t s z<′l)) (unquo s (next-lev-binᴿ t s z<′l))


-- Unquoting a term decrements its level.
lev-unquo-t≡pred-lev-t : ∀ t → (z<′l : zero <′ lev t) → lev (unquo t z<′l) ≡ pred (lev t)
lev-unquo-t≡pred-lev-t (var[ zero ]  i)   ()
lev-unquo-t≡pred-lev-t (lam[ zero ]  t)   ()
lev-unquo-t≡pred-lev-t (app[ zero ]  t s) ()
lev-unquo-t≡pred-lev-t (var[ suc n ] i)   z<′l = refl
lev-unquo-t≡pred-lev-t (lam[ suc n ] t)   z<′l rewrite lev-unquo-t≡pred-lev-t t (next-lev-un t z<′l) = lm1 n (lev t)
lev-unquo-t≡pred-lev-t (app[ suc n ] t s) z<′l rewrite lev-unquo-t≡pred-lev-t t (next-lev-binᴸ t s z<′l)
                                                     | lev-unquo-t≡pred-lev-t s (next-lev-binᴿ t s z<′l) = lm2 n (lev t) (lev s)


-- Unquoting after quoting is identity.
unquo-quo-t≡t : ∀ t → unquo (quo t) (z<′lev-quo-t t) ≡ t
unquo-quo-t≡t t = aux t (z<′lev-quo-t t)
  where
    aux : ∀ t → (z<′l : zero <′ lev (quo t)) → unquo (quo t) z<′l ≡ t    -- TODO: Simplify!
    aux (var[ n ] i)   z<′l = refl
    aux (lam[ n ] t)   z<′l rewrite aux t (next-lev-un (quo t) z<′l) = refl
    aux (app[ n ] t s) z<′l rewrite aux t (next-lev-binᴸ (quo t) (quo s) z<′l)
                                  | aux s (next-lev-binᴿ (quo t) (quo s) z<′l) = refl


-- Quoting after unquoting is identity.
quo-unquo-t≡t : ∀ t → (z<′l : zero <′ lev t) → quo (unquo t z<′l) ≡ t
quo-unquo-t≡t (var[ zero ]  i)   ()
quo-unquo-t≡t (lam[ zero ]  t)   ()
quo-unquo-t≡t (app[ zero ]  t s) ()
quo-unquo-t≡t (var[ suc n ] i)   z<′l = refl
quo-unquo-t≡t (lam[ suc n ] t)   z<′l rewrite quo-unquo-t≡t t (next-lev-un t z<′l) = refl
quo-unquo-t≡t (app[ suc n ] t s) z<′l rewrite quo-unquo-t≡t t (next-lev-binᴸ t s z<′l)
                                            | quo-unquo-t≡t s (next-lev-binᴿ t s z<′l) = refl


-- Term equality is decidable.
_≟_ : Decidable {A = Tm} _≡_
var[_] n i   ≟ var[_] n′ i′    with n ℕ≟ n′ | i ℕ≟ i′
var[_] n i   ≟ var[_] .n .i    | yes refl | yes refl = yes refl
var[_] n i   ≟ var[_] .n i′    | yes refl | no  i≢i′ = no (i≢i′ ∘ var-inv-i)
...                            | no  n≢n′ | _        = no (n≢n′ ∘ var-inv-n)
var[_] n i   ≟ lam[_] n′ t′    = no λ ()
var[_] n i   ≟ app[_] n′ t′ s′ = no λ ()
lam[_] n t   ≟ var[_] n′ i′    = no λ ()
lam[_] n t   ≟ lam[_] n′ t′    with n ℕ≟ n′ | t ≟ t′
lam[_] n t   ≟ lam[_] .n .t    | yes refl | yes refl = yes refl
lam[_] n t   ≟ lam[_] .n t′    | yes refl | no  t≢t′ = no (t≢t′ ∘ lam-inv-t)
...                            | no  n≢n′ | _        = no (n≢n′ ∘ lam-inv-n)
lam[_] n t   ≟ app[_] n′ t′ s′ = no λ ()
app[_] n t s ≟ var[_] n′ i′    = no λ ()
app[_] n t s ≟ lam[_] n′ t′    = no λ ()
app[_] n t s ≟ app[_] n′ t′ s′ with n ℕ≟ n′ | t ≟ t′ | s ≟ s′
app[_] n t s ≟ app[_] .n .t .s | yes refl | yes refl | yes refl = yes refl
app[_] n t s ≟ app[_] .n .t s′ | yes refl | yes refl | no  s≢s′ = no (s≢s′ ∘ app-inv-s)
app[_] n t s ≟ app[_] .n t′ s′ | yes refl | no  t≢t′ | _        = no (t≢t′ ∘ app-inv-t)
...                            | no  n≢n′ | _        | _        = no (n≢n′ ∘ app-inv-n)
