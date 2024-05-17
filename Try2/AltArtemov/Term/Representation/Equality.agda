module Try2.AltArtemov.Term.Representation.Equality where

open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Nullary using (Dec ; yes ; no)
import Data.Nat as ℕ

open import Try2.AltArtemov.Term.Representation.Core
open import Try2.AltArtemov.Term.Representation.Inversion
open import Try2.AltArtemov.Variable.Representation


_≟ᵗ_ : ∀ {g} → (t t′ : g ⊢◌) → Dec (t ≡ t′)

VAR[ n ] i    ≟ᵗ VAR[ n′ ] i′     with n ℕ.≟ n′ | i ≟ⁱ i′
VAR[ n ] i    ≟ᵗ VAR[ .n ] .i     | yes refl | yes refl = yes refl
...                               | no  n≢n′ | _        = no (n≢n′ ∘ inv-VAR-n)
...                               | _        | no  i≢i′ = no (i≢i′ ∘ inv-VAR-i)
VAR[ _ ] _    ≟ᵗ LAM[ _ ] _       = no λ ()
VAR[ _ ] _    ≟ᵗ APP[ _ ] _ _     = no λ ()
VAR[ _ ] _    ≟ᵗ PAIR[ _ ] _ _    = no λ ()
VAR[ _ ] _    ≟ᵗ FST[ _ ] _       = no λ ()
VAR[ _ ] _    ≟ᵗ SND[ _ ] _       = no λ ()
VAR[ _ ] _    ≟ᵗ UP[ _ ] _        = no λ ()
VAR[ _ ] _    ≟ᵗ DOWN[ _ ] _      = no λ ()
VAR[ _ ] _    ≟ᵗ BOOM[ _ ] _      = no λ ()
VAR[ _ ] _    ≟ᵗ (! _)            = no λ ()

LAM[ _ ] _    ≟ᵗ VAR[ _ ] _       = no λ ()
LAM[ n ] t    ≟ᵗ LAM[ n′ ] t′     with n ℕ.≟ n′ | t ≟ᵗ t′
LAM[ n ] t    ≟ᵗ LAM[ .n ] .t     | yes refl | yes refl = yes refl
...                               | no  n≢n′ | _        = no (n≢n′ ∘ inv-LAM-n)
...                               | _        | no  t≢t′ = no (t≢t′ ∘ inv-LAM-t)
LAM[ _ ] _    ≟ᵗ APP[ _ ] _ _     = no λ ()
LAM[ _ ] _    ≟ᵗ PAIR[ _ ] _ _    = no λ ()
LAM[ _ ] _    ≟ᵗ FST[ _ ] _       = no λ ()
LAM[ _ ] _    ≟ᵗ SND[ _ ] _       = no λ ()
LAM[ _ ] _    ≟ᵗ UP[ _ ] _        = no λ ()
LAM[ _ ] _    ≟ᵗ DOWN[ _ ] _      = no λ ()
LAM[ _ ] _    ≟ᵗ BOOM[ _ ] _      = no λ ()
LAM[ _ ] _    ≟ᵗ (! _)            = no λ ()

APP[ _ ] _ _  ≟ᵗ VAR[ _ ] _       = no λ ()
APP[ _ ] _ _  ≟ᵗ LAM[ _ ] _       = no λ ()
APP[ n ] t u  ≟ᵗ APP[ n′ ] t′ u′  with n ℕ.≟ n′ | t ≟ᵗ t′ | u ≟ᵗ u′
APP[ n ] t u  ≟ᵗ APP[ .n ] .t .u  | yes refl | yes refl | yes refl = yes refl
...                               | no  n≢n′ | _        | _        = no (n≢n′ ∘ inv-APP-n)
...                               | _        | no  t≢t′ | _        = no (t≢t′ ∘ inv-APP-t)
...                               | _        | _        | no  u≢u′ = no (u≢u′ ∘ inv-APP-u)
APP[ _ ] _ _  ≟ᵗ PAIR[ _ ] _ _    = no λ ()
APP[ _ ] _ _  ≟ᵗ FST[ _ ] _       = no λ ()
APP[ _ ] _ _  ≟ᵗ SND[ _ ] _       = no λ ()
APP[ _ ] _ _  ≟ᵗ UP[ _ ] _        = no λ ()
APP[ _ ] _ _  ≟ᵗ DOWN[ _ ] _      = no λ ()
APP[ _ ] _ _  ≟ᵗ BOOM[ _ ] _      = no λ ()
APP[ _ ] _ _  ≟ᵗ (! _)            = no λ ()

PAIR[ _ ] _ _ ≟ᵗ VAR[ _ ] _       = no λ ()
PAIR[ _ ] _ _ ≟ᵗ LAM[ _ ] _       = no λ ()
PAIR[ _ ] _ _ ≟ᵗ APP[ _ ] _ _     = no λ ()
PAIR[ n ] t u ≟ᵗ PAIR[ n′ ] t′ u′ with n ℕ.≟ n′ | t ≟ᵗ t′ | u ≟ᵗ u′
PAIR[ n ] t u ≟ᵗ PAIR[ .n ] .t .u | yes refl | yes refl | yes refl = yes refl
...                               | no  n≢n′ | _        | _        = no (n≢n′ ∘ inv-PAIR-n)
...                               | _        | no  t≢t′ | _        = no (t≢t′ ∘ inv-PAIR-t)
...                               | _        | _        | no  u≢u′ = no (u≢u′ ∘ inv-PAIR-u)
PAIR[ _ ] _ _ ≟ᵗ FST[ _ ] _       = no λ ()
PAIR[ _ ] _ _ ≟ᵗ SND[ _ ] _       = no λ ()
PAIR[ _ ] _ _ ≟ᵗ UP[ _ ] _        = no λ ()
PAIR[ _ ] _ _ ≟ᵗ DOWN[ _ ] _      = no λ ()
PAIR[ _ ] _ _ ≟ᵗ BOOM[ _ ] _      = no λ ()
PAIR[ _ ] _ _ ≟ᵗ (! _)            = no λ ()

FST[ _ ] _    ≟ᵗ VAR[ _ ] _       = no λ ()
FST[ _ ] _    ≟ᵗ LAM[ _ ] _       = no λ ()
FST[ _ ] _    ≟ᵗ APP[ _ ] _ _     = no λ ()
FST[ _ ] _    ≟ᵗ PAIR[ _ ] _ _    = no λ ()
FST[ n ] t    ≟ᵗ FST[ n′ ] t′     with n ℕ.≟ n′ | t ≟ᵗ t′
FST[ n ] t    ≟ᵗ FST[ .n ] .t     | yes refl | yes refl = yes refl
...                               | no  n≢n′ | _        = no (n≢n′ ∘ inv-FST-n)
...                               | _        | no  t≢t′ = no (t≢t′ ∘ inv-FST-t)
FST[ _ ] _    ≟ᵗ SND[ _ ] _       = no λ ()
FST[ _ ] _    ≟ᵗ UP[ _ ] _        = no λ ()
FST[ _ ] _    ≟ᵗ DOWN[ _ ] _      = no λ ()
FST[ _ ] _    ≟ᵗ BOOM[ _ ] _      = no λ ()
FST[ _ ] _    ≟ᵗ (! _)            = no λ ()

SND[ _ ] _    ≟ᵗ VAR[ _ ] _       = no λ ()
SND[ _ ] _    ≟ᵗ LAM[ _ ] _       = no λ ()
SND[ _ ] _    ≟ᵗ APP[ _ ] _ _     = no λ ()
SND[ _ ] _    ≟ᵗ PAIR[ _ ] _ _    = no λ ()
SND[ _ ] _    ≟ᵗ FST[ _ ] _       = no λ ()
SND[ n ] t    ≟ᵗ SND[ n′ ] t′     with n ℕ.≟ n′ | t ≟ᵗ t′
SND[ n ] t    ≟ᵗ SND[ .n ] .t     | yes refl | yes refl = yes refl
...                               | no  n≢n′ | _        = no (n≢n′ ∘ inv-SND-n)
...                               | _        | no  t≢t′ = no (t≢t′ ∘ inv-SND-t)
SND[ _ ] _    ≟ᵗ UP[ _ ] _        = no λ ()
SND[ _ ] _    ≟ᵗ DOWN[ _ ] _      = no λ ()
SND[ _ ] _    ≟ᵗ BOOM[ _ ] _      = no λ ()
SND[ _ ] _    ≟ᵗ (! _)            = no λ ()

UP[ _ ] _     ≟ᵗ VAR[ _ ] _       = no λ ()
UP[ _ ] _     ≟ᵗ LAM[ _ ] _       = no λ ()
UP[ _ ] _     ≟ᵗ APP[ _ ] _ _     = no λ ()
UP[ _ ] _     ≟ᵗ PAIR[ _ ] _ _    = no λ ()
UP[ _ ] _     ≟ᵗ FST[ _ ] _       = no λ ()
UP[ _ ] _     ≟ᵗ SND[ _ ] _       = no λ ()
UP[ n ] t     ≟ᵗ UP[ n′ ] t′      with n ℕ.≟ n′ | t ≟ᵗ t′
UP[ n ] t     ≟ᵗ UP[ .n ] .t      | yes refl | yes refl = yes refl
...                               | no  n≢n′ | _        = no (n≢n′ ∘ inv-UP-n)
...                               | _        | no  t≢t′ = no (t≢t′ ∘ inv-UP-t)
UP[ _ ] _     ≟ᵗ DOWN[ _ ] _      = no λ ()
UP[ _ ] _     ≟ᵗ BOOM[ _ ] _      = no λ ()
UP[ _ ] _     ≟ᵗ (! _)            = no λ ()

DOWN[ _ ] _   ≟ᵗ VAR[ _ ] _       = no λ ()
DOWN[ _ ] _   ≟ᵗ LAM[ _ ] _       = no λ ()
DOWN[ _ ] _   ≟ᵗ APP[ _ ] _ _     = no λ ()
DOWN[ _ ] _   ≟ᵗ PAIR[ _ ] _ _    = no λ ()
DOWN[ _ ] _   ≟ᵗ FST[ _ ] _       = no λ ()
DOWN[ _ ] _   ≟ᵗ SND[ _ ] _       = no λ ()
DOWN[ _ ] _   ≟ᵗ UP[ _ ] _        = no λ ()
DOWN[ n ] t   ≟ᵗ DOWN[ n′ ] t′    with n ℕ.≟ n′ | t ≟ᵗ t′
DOWN[ n ] t   ≟ᵗ DOWN[ .n ] .t    | yes refl | yes refl = yes refl
...                               | no  n≢n′ | _        = no (n≢n′ ∘ inv-DOWN-n)
...                               | _        | no  t≢t′ = no (t≢t′ ∘ inv-DOWN-t)
DOWN[ _ ] _   ≟ᵗ BOOM[ _ ] _      = no λ ()
DOWN[ _ ] _   ≟ᵗ (! _)            = no λ ()

BOOM[ _ ] _   ≟ᵗ VAR[ _ ] _       = no λ ()
BOOM[ _ ] _   ≟ᵗ LAM[ _ ] _       = no λ ()
BOOM[ _ ] _   ≟ᵗ APP[ _ ] _ _     = no λ ()
BOOM[ _ ] _   ≟ᵗ PAIR[ _ ] _ _    = no λ ()
BOOM[ _ ] _   ≟ᵗ FST[ _ ] _       = no λ ()
BOOM[ _ ] _   ≟ᵗ SND[ _ ] _       = no λ ()
BOOM[ _ ] _   ≟ᵗ UP[ _ ] _        = no λ ()
BOOM[ _ ] _   ≟ᵗ DOWN[ _ ] _      = no λ ()
BOOM[ n ] t   ≟ᵗ BOOM[ n′ ] t′    with n ℕ.≟ n′ | t ≟ᵗ t′
BOOM[ n ] t   ≟ᵗ BOOM[ .n ] .t    | yes refl | yes refl = yes refl
...                               | no  n≢n′ | _        = no (n≢n′ ∘ inv-BOOM-n)
...                               | _        | no  t≢t′ = no (t≢t′ ∘ inv-BOOM-t)
BOOM[ _ ] _   ≟ᵗ (! _)            = no λ ()

(! _)         ≟ᵗ VAR[ _ ] _       = no λ ()
(! _)         ≟ᵗ LAM[ _ ] _       = no λ ()
(! _)         ≟ᵗ APP[ _ ] _ _     = no λ ()
(! _)         ≟ᵗ PAIR[ _ ] _ _    = no λ ()
(! _)         ≟ᵗ FST[ _ ] _       = no λ ()
(! _)         ≟ᵗ SND[ _ ] _       = no λ ()
(! _)         ≟ᵗ UP[ _ ] _        = no λ ()
(! _)         ≟ᵗ DOWN[ _ ] _      = no λ ()
(! _)         ≟ᵗ BOOM[ _ ] _      = no λ ()
(! t)         ≟ᵗ (! t′)           with t ≟ᵗ t′
(! t)         ≟ᵗ (! .t)           | yes refl = yes refl
...                               | no  t≢t′ = no (t≢t′ ∘ inv-!)
