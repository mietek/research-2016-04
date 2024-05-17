module AltArtemov.Hereditary where


module Fin where
  open import Data.Nat using (ℕ)
  open import Data.Fin using (Fin ; zero ; suc)
  open import Function using (_∘_)
  open import Relation.Binary using (Decidable)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
  open import Relation.Nullary using (yes ; no)

  max : (n : ℕ) → Fin (ℕ.suc n)
  max ℕ.zero    = zero
  max (ℕ.suc n) = suc (max n)

  inv-suc : ∀ {n} {i i′ : Fin n} → suc i ≡ suc i′ → i ≡ i′
  inv-suc refl = refl

  _≟_ : ∀ {n} → Decidable {A = Fin n} _≡_
  zero  ≟ zero   = yes refl
  zero  ≟ suc _  = no λ ()
  suc _ ≟ zero   = no λ ()
  suc i ≟ suc i′ with i ≟ i′
  suc i ≟ suc .i | yes refl = yes refl
  ...            | no  i≢i′ = no (i≢i′ ∘ inv-suc)


module Lev where
  open import Data.Nat using (ℕ)
  open import Function using (_∘_)
  open import Relation.Binary using (Decidable)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
  open import Relation.Nullary using (yes ; no)
  import Data.Nat as ℕ

  data Lev : Set where
    zero : Lev
    suc  : Lev → Lev

  inv-suc : ∀ {n n′ : Lev} → suc n ≡ suc n′ → n ≡ n′
  inv-suc refl = refl

  _≟_ : Decidable {A = Lev} _≡_
  zero  ≟ zero   = yes refl
  zero  ≟ suc _ = no λ ()
  suc _ ≟ zero   = no λ ()
  suc n ≟ suc n′ with n ≟ n′
  suc n ≟ suc .n | yes refl = yes refl
  ...            | no  n≢n′ = no (n≢n′ ∘ inv-suc)

open Lev using (Lev ; zero ; suc)


module Grt where
  open import Data.Nat using (ℕ ; zero ; suc)
  open import Function using (_∘_)
  open import Relation.Binary using (Decidable)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
  open import Relation.Nullary using (yes ; no)

  infix 2 _,◌

  data Grt : Set where
    ∅   : Grt
    _,◌ : Grt → Grt

  ⌊_⌋ : Grt → ℕ
  ⌊ ∅ ⌋    = zero
  ⌊ g ,◌ ⌋ = suc ⌊ g ⌋

  inv-,◌ : ∀ {g g′ : Grt} → (g ,◌) ≡ (g′ ,◌) → g ≡ g′
  inv-,◌ refl = refl

  _≟_ : Decidable {A = Grt} _≡_
  ∅      ≟ ∅       = yes refl
  ∅      ≟ (_ ,◌)  = no λ ()
  (_ ,◌) ≟ ∅       = no λ ()
  (g ,◌) ≟ (g′ ,◌) with g ≟ g′
  (g ,◌) ≟ (.g ,◌) | yes refl = yes refl
  ...              | no  g≢g′ = no (g≢g′ ∘ inv-,◌)

open Grt using (Grt ; ∅ ; _,◌) renaming (⌊_⌋ to ⌊_⌋ᵍ)


module Idx where
  open import Data.Fin using (Fin ; zero ; suc)
  open import Function using (_∘_)
  open import Relation.Binary using (Decidable)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
  open import Relation.Nullary using (yes ; no)

  infix 1 ◌∈_

  data ◌∈_ : Grt → Set where
    top : ∀ {g} → ◌∈ g ,◌
    pop : ∀ {g} → ◌∈ g → ◌∈ g ,◌

  ⌊_⌋ : ∀ {g} → ◌∈ g → Fin ⌊ g ⌋ᵍ
  ⌊ top ⌋   = zero
  ⌊ pop i ⌋ = suc ⌊ i ⌋

  inv-pop : ∀ {g} {i i′ : ◌∈ g} → pop i ≡ pop i′ → i ≡ i′
  inv-pop refl = refl

  _≟_ : ∀ {g} → Decidable {A = ◌∈ g} _≡_
  top   ≟ top    = yes refl
  top   ≟ pop _  = no λ ()
  pop _ ≟ top    = no λ ()
  pop i ≟ pop i′ with i ≟ i′
  pop i ≟ pop .i | yes refl = yes refl
  ...            | no  i≢i′ = no (i≢i′ ∘ inv-pop)

open Idx using (◌∈_ ; top ; pop) renaming (⌊_⌋ to ⌊_⌋ⁱ)


module Tm where
  open import Data.Fin using (Fin ; zero ; suc)
  open import Data.Nat using (ℕ ; zero ; suc)
  open import Function using (_∘_)
  open import Relation.Binary using (Decidable)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
  open import Relation.Nullary using (yes ; no)

  infix 0 _⊢◌

  data _⊢◌ (g : Grt) : Set where
    VAR[_]  : Lev → ◌∈ g → g ⊢◌
    LAM[_]  : Lev → g ,◌ ⊢◌ → g ⊢◌
    APP[_]  : Lev → g ⊢◌ → g ⊢◌ → g ⊢◌
    PAIR[_] : Lev → g ⊢◌ → g ⊢◌ → g ⊢◌
    FST[_]  : Lev → g ⊢◌ → g ⊢◌
    SND[_]  : Lev → g ⊢◌ → g ⊢◌
    UP[_]   : Lev → g ⊢◌ → g ⊢◌
    DOWN[_] : Lev → g ⊢◌ → g ⊢◌
    BOOM[_] : Lev → g ⊢◌ → g ⊢◌
    !_      : g ⊢◌ → g ⊢◌

  infixl 5 _∖ᵍ_ _∖ᵍ⋆_

  _∖ᵍ_ : (g : Grt) → ◌∈ g → Grt
  ∅      ∖ᵍ ()
  (g ,◌) ∖ᵍ top   = g
  (g ,◌) ∖ᵍ pop i = g ∖ᵍ i ,◌

  _∖ᵍ⋆_ : (g : Grt) → Fin (suc ⌊ g ⌋ᵍ) → Grt
  g      ∖ᵍ⋆ zero   = g
  ∅      ∖ᵍ⋆ suc ()
  (g ,◌) ∖ᵍ⋆ suc k  = g ∖ᵍ⋆ k

  ∖ᵍ⋆-zero : (g : Grt) → ∅ ≡ g ∖ᵍ⋆ Fin.max ⌊ g ⌋ᵍ
  ∖ᵍ⋆-zero ∅      = refl
  ∖ᵍ⋆-zero (g ,◌) = ∖ᵍ⋆-zero g

  wkᵛ : ∀ {g} → (i : ◌∈ g) → ◌∈ g ∖ᵍ i → ◌∈ g
  wkᵛ top     j       = pop j
  wkᵛ (pop i) top     = top
  wkᵛ (pop i) (pop j) = pop (wkᵛ i j)

  wkᵛ⋆ : ∀ {g} → (k : Fin (suc ⌊ g ⌋ᵍ)) → ◌∈ g ∖ᵍ⋆ k → ◌∈ g
  wkᵛ⋆ {g}    zero     i = i
  wkᵛ⋆ {∅}    (suc ()) i
  wkᵛ⋆ {g ,◌} (suc k)  i = wkᵛ top (wkᵛ⋆ k i)

  data _=ᵛ_ {g : Grt} : ◌∈ g → ◌∈ g → Set where
    same : {i : ◌∈ g} → i =ᵛ i
    diff : (i : ◌∈ g) → (j : ◌∈ g ∖ᵍ i) → i =ᵛ wkᵛ i j

  _=ᵛ?_ : ∀ {g} → (i j : ◌∈ g) → i =ᵛ j
  top   =ᵛ? top            = same
  top   =ᵛ? pop j          = diff top j
  pop i =ᵛ? top            = diff (pop i) top
  pop i =ᵛ? pop j          with i =ᵛ? j
  pop i =ᵛ? pop .i         | same = same
  pop i =ᵛ? pop .(wkᵛ i j) | diff .i j = diff (pop i) (pop j)

  wk : ∀ {g} → (i : ◌∈ g) → g ∖ᵍ i ⊢◌ → g ⊢◌
  wk i (VAR[ n ] v)    = VAR[ n ] (wkᵛ i v)
  wk i (LAM[ n ] t)    = LAM[ n ] (wk (pop i) t)
  wk i (APP[ n ] t u)  = APP[ n ] (wk i t) (wk i u)
  wk i (PAIR[ n ] t u) = PAIR[ n ] (wk i t) (wk i u)
  wk i (FST[ n ] t)    = FST[ n ] (wk i t)
  wk i (SND[ n ] t)    = SND[ n ] (wk i t)
  wk i (UP[ n ] t)     = UP[ n ] (wk i t)
  wk i (DOWN[ n ] t)   = DOWN[ n ] (wk i t)
  wk i (BOOM[ n ] t)   = BOOM[ n ] (wk i t)
  wk i (! t)           = ! (wk i t)

  wk⋆ : ∀ {g} → (k : Fin (suc ⌊ g ⌋ᵍ)) → g ∖ᵍ⋆ k ⊢◌ → g ⊢◌
  wk⋆ {g}    zero     t = t
  wk⋆ {∅}    (suc ()) t
  wk⋆ {g ,◌} (suc k)  t = wk top (wk⋆ k t)

  substᵛ : ∀ {g} → Lev → ◌∈ g → (i : ◌∈ g) → g ∖ᵍ i ⊢◌ → g ∖ᵍ i ⊢◌
  substᵛ n v          i  s with i =ᵛ? v
  substᵛ n v          .v s | same = s
  substᵛ n .(wkᵛ v i) v  s | diff .v i = VAR[ n ] i

  subst : ∀ {g} → g ⊢◌ → (i : ◌∈ g) → g ∖ᵍ i ⊢◌ → g ∖ᵍ i ⊢◌
  subst (VAR[ n ] v) i s    = substᵛ n v i s
  subst (LAM[ n ] t) i s    = LAM[ n ] (subst t (pop i) (wk top s))
  subst (APP[ n ] t u) i s  = APP[ n ] (subst t i s) (subst u i s)
  subst (PAIR[ n ] t u) i s = PAIR[ n ] (subst t i s) (subst u i s)
  subst (FST[ n ] t) i s    = FST[ n ] (subst t i s)
  subst (SND[ n ] t) i s    = SND[ n ] (subst t i s)
  subst (UP[ n ] t) i s     = UP[ n ] (subst t i s)
  subst (DOWN[ n ] t) i s   = DOWN[ n ] (subst t i s)
  subst (BOOM[ n ] t) i s   = BOOM[ n ] (subst t i s)
  subst (! t) i s           = ! subst t i s

  data _▷_ {g : Grt} : g ⊢◌ → g ⊢◌ → Set where
    ▷-refl : {t : g ⊢◌}
        → t ▷ t

    ▷-sym : {t t′ : g ⊢◌}
        → t ▷ t′
        → t′ ▷ t

    ▷-trans : {t t′ t″ : g ⊢◌}
        → t ▷ t′    → t′ ▷ t″
        → t ▷ t″

    ▷-cong-LAM : ∀ {n} → {t t′ : g ,◌ ⊢◌}
        → t ▷ t′
        → LAM[ n ] t ▷ LAM[ n ] t′

    ▷-cong-APP : ∀ {n} → {t t′ u u′ : g ⊢◌}
        → t ▷ t′    → u ▷ u′
        → APP[ n ] t u ▷ APP[ n ] t′ u′

    ▷-cong-PAIR : ∀ {n} → {t t′ u u′ : g ⊢◌}
        → t ▷ t′    → u ▷ u′
        → PAIR[ n ] t u ▷ PAIR[ n ] t′ u′

    ▷-cong-FST : ∀ {n} → {t t′ : g ⊢◌}
        → t ▷ t′
        → FST[ n ] t ▷ FST[ n ] t′

    ▷-cong-SND : ∀ {n} → {t t′ : g ⊢◌}
        → t ▷ t′
        → SND[ n ] t ▷ SND[ n ] t′

    ▷-cong-UP : ∀ {n} → {t t′ : g ⊢◌}
        → t ▷ t
        → UP[ n ] t ▷ UP[ n ] t′

    ▷-cong-DOWN : ∀ {n} → {t t′ : g ⊢◌}
        → t ▷ t′
        → DOWN[ n ] t ▷ DOWN[ n ] t′

    ▷-cong-BOOM : ∀ {n} → {t t′ : g ⊢◌}
        → t ▷ t′
        → BOOM[ n ] t ▷ BOOM[ n ] t′

    ▷-red-APP : ∀ {n} → {t : g ,◌ ⊢◌} → {u : g ⊢◌}
        → APP[ n ] (LAM[ n ] t) u ▷ subst t top u

    ▷-exp-LAM : ∀ {n} → {t : g ⊢◌}
        → LAM[ n ] (APP[ n ] (wk top t) (VAR[ n ] top)) ▷ t

    ▷-red-FST : ∀ {n} → {t u : g ⊢◌}
        → FST[ n ] (PAIR[ n ] t u) ▷ t

    ▷-red-SND : ∀ {n} → {t u : g ⊢◌}
        → SND[ n ] (PAIR[ n ] t u) ▷ u

    ▷-exp-PAIR : ∀ {n} → {t : g ⊢◌}
        → PAIR[ n ] (FST[ n ] t) (SND[ n ] t) ▷ t

    ▷-red-DOWN : ∀ {n} → {t : g ⊢◌}
        → DOWN[ n ] (UP[ n ] t) ▷ t

    ▷-exp-UP : ∀ {n} → {t : g ⊢◌}
        → UP[ n ] (DOWN[ n ] t) ▷ t

  inv-VAR-n : ∀ {g n n′} {i i′ : ◌∈ g} → VAR[ n ] i ≡ VAR[ n′ ] i′ → n ≡ n′
  inv-VAR-n refl = refl

  inv-VAR-i : ∀ {g n n′} {i i′ : ◌∈ g} → VAR[ n ] i ≡ VAR[ n′ ] i′ → i ≡ i′
  inv-VAR-i refl = refl

  inv-LAM-n : ∀ {g n n′} {t t′ : g ,◌ ⊢◌} → LAM[ n ] t ≡ LAM[ n′ ] t′ → n ≡ n′
  inv-LAM-n refl = refl

  inv-LAM-t : ∀ {g n n′} {t t′ : g ,◌ ⊢◌} → LAM[ n ] t ≡ LAM[ n′ ] t′ → t ≡ t′
  inv-LAM-t refl = refl

  inv-APP-n : ∀ {g n n′} {t t′ u u′ : g ⊢◌} → APP[ n ] t u ≡ APP[ n′ ] t′ u′ → n ≡ n′
  inv-APP-n refl = refl

  inv-APP-t : ∀ {g n n′} {t t′ u u′ : g ⊢◌} → APP[ n ] t u ≡ APP[ n′ ] t′ u′ → t ≡ t′
  inv-APP-t refl = refl

  inv-APP-u : ∀ {g n n′} {t t′ u u′ : g ⊢◌} → APP[ n ] t u ≡ APP[ n′ ] t′ u′ → u ≡ u′
  inv-APP-u refl = refl

  inv-PAIR-n : ∀ {g n n′} {t t′ u u′ : g ⊢◌} → PAIR[ n ] t u ≡ PAIR[ n′ ] t′ u′ → n ≡ n′
  inv-PAIR-n refl = refl

  inv-PAIR-t : ∀ {g n n′} {t t′ u u′ : g ⊢◌} → PAIR[ n ] t u ≡ PAIR[ n′ ] t′ u′ → t ≡ t′
  inv-PAIR-t refl = refl

  inv-PAIR-u : ∀ {g n n′} {t t′ u u′ : g ⊢◌} → PAIR[ n ] t u ≡ PAIR[ n′ ] t′ u′ → u ≡ u′
  inv-PAIR-u refl = refl

  inv-FST-n : ∀ {g n n′} {t t′ : g ⊢◌} → FST[ n ] t ≡ FST[ n′ ] t′ → n ≡ n′
  inv-FST-n refl = refl

  inv-FST-t : ∀ {g n n′} {t t′ : g ⊢◌} → FST[ n ] t ≡ FST[ n′ ] t′ → t ≡ t′
  inv-FST-t refl = refl

  inv-SND-n : ∀ {g n n′} {t t′ : g ⊢◌} → SND[ n ] t ≡ SND[ n′ ] t′ → n ≡ n′
  inv-SND-n refl = refl

  inv-SND-t : ∀ {g n n′} {t t′ : g ⊢◌} → SND[ n ] t ≡ SND[ n′ ] t′ → t ≡ t′
  inv-SND-t refl = refl

  inv-UP-n : ∀ {g n n′} {t t′ : g ⊢◌} → UP[ n ] t ≡ UP[ n′ ] t′ → n ≡ n′
  inv-UP-n refl = refl

  inv-UP-t : ∀ {g n n′} {t t′ : g ⊢◌} → UP[ n ] t ≡ UP[ n′ ] t′ → t ≡ t′
  inv-UP-t refl = refl

  inv-DOWN-n : ∀ {g n n′} {t t′ : g ⊢◌} → DOWN[ n ] t ≡ DOWN[ n′ ] t′ → n ≡ n′
  inv-DOWN-n refl = refl

  inv-DOWN-t : ∀ {g n n′} {t t′ : g ⊢◌} → DOWN[ n ] t ≡ DOWN[ n′ ] t′ → t ≡ t′
  inv-DOWN-t refl = refl

  inv-BOOM-n : ∀ {g n n′} {t t′ : g ⊢◌} → BOOM[ n ] t ≡ BOOM[ n′ ] t′ → n ≡ n′
  inv-BOOM-n refl = refl

  inv-BOOM-t : ∀ {g n n′} {t t′ : g ⊢◌} → BOOM[ n ] t ≡ BOOM[ n′ ] t′ → t ≡ t′
  inv-BOOM-t refl = refl

  inv-! : ∀ {g} {t t′ : g ⊢◌} → (! t) ≡ (! t′) → t ≡ t′
  inv-! refl = refl

  _≟_ : ∀ {g} → Decidable {A = g ⊢◌} _≡_
  VAR[ n ] i    ≟ VAR[ n′ ] i′     with n Lev.≟ n′ | i Idx.≟ i′
  VAR[ n ] i    ≟ VAR[ .n ] .i     | yes refl | yes refl = yes refl
  ...                              | no  n≢n′ | _        = no (n≢n′ ∘ inv-VAR-n)
  ...                              | _        | no  i≢i′ = no (i≢i′ ∘ inv-VAR-i)
  VAR[ _ ] _    ≟ LAM[ _ ] _       = no λ ()
  VAR[ _ ] _    ≟ APP[ _ ] _ _     = no λ ()
  VAR[ _ ] _    ≟ PAIR[ _ ] _ _    = no λ ()
  VAR[ _ ] _    ≟ FST[ _ ] _       = no λ ()
  VAR[ _ ] _    ≟ SND[ _ ] _       = no λ ()
  VAR[ _ ] _    ≟ UP[ _ ] _        = no λ ()
  VAR[ _ ] _    ≟ DOWN[ _ ] _      = no λ ()
  VAR[ _ ] _    ≟ BOOM[ _ ] _      = no λ ()
  VAR[ _ ] _    ≟ (! _)            = no λ ()
  LAM[ _ ] _    ≟ VAR[ _ ] _       = no λ ()
  LAM[ n ] t    ≟ LAM[ n′ ] t′     with n Lev.≟ n′ | t ≟ t′
  LAM[ n ] t    ≟ LAM[ .n ] .t     | yes refl | yes refl = yes refl
  ...                              | no  n≢n′ | _        = no (n≢n′ ∘ inv-LAM-n)
  ...                              | _        | no  t≢t′ = no (t≢t′ ∘ inv-LAM-t)
  LAM[ _ ] _    ≟ APP[ _ ] _ _     = no λ ()
  LAM[ _ ] _    ≟ PAIR[ _ ] _ _    = no λ ()
  LAM[ _ ] _    ≟ FST[ _ ] _       = no λ ()
  LAM[ _ ] _    ≟ SND[ _ ] _       = no λ ()
  LAM[ _ ] _    ≟ UP[ _ ] _        = no λ ()
  LAM[ _ ] _    ≟ DOWN[ _ ] _      = no λ ()
  LAM[ _ ] _    ≟ BOOM[ _ ] _      = no λ ()
  LAM[ _ ] _    ≟ (! _)            = no λ ()
  APP[ _ ] _ _  ≟ VAR[ _ ] _       = no λ ()
  APP[ _ ] _ _  ≟ LAM[ _ ] _       = no λ ()
  APP[ n ] t u  ≟ APP[ n′ ] t′ u′  with n Lev.≟ n′ | t ≟ t′ | u ≟ u′
  APP[ n ] t u  ≟ APP[ .n ] .t .u  | yes refl | yes refl | yes refl = yes refl
  ...                              | no  n≢n′ | _        | _        = no (n≢n′ ∘ inv-APP-n)
  ...                              | _        | no  t≢t′ | _        = no (t≢t′ ∘ inv-APP-t)
  ...                              | _        | _        | no  u≢u′ = no (u≢u′ ∘ inv-APP-u)
  APP[ _ ] _ _  ≟ PAIR[ _ ] _ _    = no λ ()
  APP[ _ ] _ _  ≟ FST[ _ ] _       = no λ ()
  APP[ _ ] _ _  ≟ SND[ _ ] _       = no λ ()
  APP[ _ ] _ _  ≟ UP[ _ ] _        = no λ ()
  APP[ _ ] _ _  ≟ DOWN[ _ ] _      = no λ ()
  APP[ _ ] _ _  ≟ BOOM[ _ ] _      = no λ ()
  APP[ _ ] _ _  ≟ (! _)            = no λ ()
  PAIR[ _ ] _ _ ≟ VAR[ _ ] _       = no λ ()
  PAIR[ _ ] _ _ ≟ LAM[ _ ] _       = no λ ()
  PAIR[ _ ] _ _ ≟ APP[ _ ] _ _     = no λ ()
  PAIR[ n ] t u ≟ PAIR[ n′ ] t′ u′ with n Lev.≟ n′ | t ≟ t′ | u ≟ u′
  PAIR[ n ] t u ≟ PAIR[ .n ] .t .u | yes refl | yes refl | yes refl = yes refl
  ...                              | no  n≢n′ | _        | _        = no (n≢n′ ∘ inv-PAIR-n)
  ...                              | _        | no  t≢t′ | _        = no (t≢t′ ∘ inv-PAIR-t)
  ...                              | _        | _        | no  u≢u′ = no (u≢u′ ∘ inv-PAIR-u)
  PAIR[ _ ] _ _ ≟ FST[ _ ] _       = no λ ()
  PAIR[ _ ] _ _ ≟ SND[ _ ] _       = no λ ()
  PAIR[ _ ] _ _ ≟ UP[ _ ] _        = no λ ()
  PAIR[ _ ] _ _ ≟ DOWN[ _ ] _      = no λ ()
  PAIR[ _ ] _ _ ≟ BOOM[ _ ] _      = no λ ()
  PAIR[ _ ] _ _ ≟ (! _)            = no λ ()
  FST[ _ ] _    ≟ VAR[ _ ] _       = no λ ()
  FST[ _ ] _    ≟ LAM[ _ ] _       = no λ ()
  FST[ _ ] _    ≟ APP[ _ ] _ _     = no λ ()
  FST[ _ ] _    ≟ PAIR[ _ ] _ _    = no λ ()
  FST[ n ] t    ≟ FST[ n′ ] t′     with n Lev.≟ n′ | t ≟ t′
  FST[ n ] t    ≟ FST[ .n ] .t     | yes refl | yes refl = yes refl
  ...                              | no  n≢n′ | _        = no (n≢n′ ∘ inv-FST-n)
  ...                              | _        | no  t≢t′ = no (t≢t′ ∘ inv-FST-t)
  FST[ _ ] _    ≟ SND[ _ ] _       = no λ ()
  FST[ _ ] _    ≟ UP[ _ ] _        = no λ ()
  FST[ _ ] _    ≟ DOWN[ _ ] _      = no λ ()
  FST[ _ ] _    ≟ BOOM[ _ ] _      = no λ ()
  FST[ _ ] _    ≟ (! _)            = no λ ()
  SND[ _ ] _    ≟ VAR[ _ ] _       = no λ ()
  SND[ _ ] _    ≟ LAM[ _ ] _       = no λ ()
  SND[ _ ] _    ≟ APP[ _ ] _ _     = no λ ()
  SND[ _ ] _    ≟ PAIR[ _ ] _ _    = no λ ()
  SND[ _ ] _    ≟ FST[ _ ] _       = no λ ()
  SND[ n ] t    ≟ SND[ n′ ] t′     with n Lev.≟ n′ | t ≟ t′
  SND[ n ] t    ≟ SND[ .n ] .t     | yes refl | yes refl = yes refl
  ...                              | no  n≢n′ | _        = no (n≢n′ ∘ inv-SND-n)
  ...                              | _        | no  t≢t′ = no (t≢t′ ∘ inv-SND-t)
  SND[ _ ] _    ≟ UP[ _ ] _        = no λ ()
  SND[ _ ] _    ≟ DOWN[ _ ] _      = no λ ()
  SND[ _ ] _    ≟ BOOM[ _ ] _      = no λ ()
  SND[ _ ] _    ≟ (! _)            = no λ ()
  UP[ _ ] _     ≟ VAR[ _ ] _       = no λ ()
  UP[ _ ] _     ≟ LAM[ _ ] _       = no λ ()
  UP[ _ ] _     ≟ APP[ _ ] _ _     = no λ ()
  UP[ _ ] _     ≟ PAIR[ _ ] _ _    = no λ ()
  UP[ _ ] _     ≟ FST[ _ ] _       = no λ ()
  UP[ _ ] _     ≟ SND[ _ ] _       = no λ ()
  UP[ n ] t     ≟ UP[ n′ ] t′      with n Lev.≟ n′ | t ≟ t′
  UP[ n ] t     ≟ UP[ .n ] .t      | yes refl | yes refl = yes refl
  ...                              | no  n≢n′ | _        = no (n≢n′ ∘ inv-UP-n)
  ...                              | _        | no  t≢t′ = no (t≢t′ ∘ inv-UP-t)
  UP[ _ ] _     ≟ DOWN[ _ ] _      = no λ ()
  UP[ _ ] _     ≟ BOOM[ _ ] _      = no λ ()
  UP[ _ ] _     ≟ (! _)            = no λ ()
  DOWN[ _ ] _   ≟ VAR[ _ ] _       = no λ ()
  DOWN[ _ ] _   ≟ LAM[ _ ] _       = no λ ()
  DOWN[ _ ] _   ≟ APP[ _ ] _ _     = no λ ()
  DOWN[ _ ] _   ≟ PAIR[ _ ] _ _    = no λ ()
  DOWN[ _ ] _   ≟ FST[ _ ] _       = no λ ()
  DOWN[ _ ] _   ≟ SND[ _ ] _       = no λ ()
  DOWN[ _ ] _   ≟ UP[ _ ] _        = no λ ()
  DOWN[ n ] t   ≟ DOWN[ n′ ] t′    with n Lev.≟ n′ | t ≟ t′
  DOWN[ n ] t   ≟ DOWN[ .n ] .t    | yes refl | yes refl = yes refl
  ...                              | no  n≢n′ | _        = no (n≢n′ ∘ inv-DOWN-n)
  ...                              | _        | no  t≢t′ = no (t≢t′ ∘ inv-DOWN-t)
  DOWN[ _ ] _   ≟ BOOM[ _ ] _      = no λ ()
  DOWN[ _ ] _   ≟ (! _)            = no λ ()
  BOOM[ _ ] _   ≟ VAR[ _ ] _       = no λ ()
  BOOM[ _ ] _   ≟ LAM[ _ ] _       = no λ ()
  BOOM[ _ ] _   ≟ APP[ _ ] _ _     = no λ ()
  BOOM[ _ ] _   ≟ PAIR[ _ ] _ _    = no λ ()
  BOOM[ _ ] _   ≟ FST[ _ ] _       = no λ ()
  BOOM[ _ ] _   ≟ SND[ _ ] _       = no λ ()
  BOOM[ _ ] _   ≟ UP[ _ ] _        = no λ ()
  BOOM[ _ ] _   ≟ DOWN[ _ ] _      = no λ ()
  BOOM[ n ] t   ≟ BOOM[ n′ ] t′    with n Lev.≟ n′ | t ≟ t′
  BOOM[ n ] t   ≟ BOOM[ .n ] .t    | yes refl | yes refl = yes refl
  ...                              | no  n≢n′ | _        = no (n≢n′ ∘ inv-BOOM-n)
  ...                              | _        | no  t≢t′ = no (t≢t′ ∘ inv-BOOM-t)
  BOOM[ _ ] _   ≟ (! _)            = no λ ()
  (! _)         ≟ VAR[ _ ] _       = no λ ()
  (! _)         ≟ LAM[ _ ] _       = no λ ()
  (! _)         ≟ APP[ _ ] _ _     = no λ ()
  (! _)         ≟ PAIR[ _ ] _ _    = no λ ()
  (! _)         ≟ FST[ _ ] _       = no λ ()
  (! _)         ≟ SND[ _ ] _       = no λ ()
  (! _)         ≟ UP[ _ ] _        = no λ ()
  (! _)         ≟ DOWN[ _ ] _      = no λ ()
  (! _)         ≟ BOOM[ _ ] _      = no λ ()
  (! t)         ≟ (! t′)           with t ≟ t′
  (! t)         ≟ (! .t)           | yes refl = yes refl
  ...                              | no  t≢t′ = no (t≢t′ ∘ inv-!)






open import Data.Fin using (Fin ; zero ; suc)
open import Data.Nat using (ℕ ; zero ; suc)
open import Function using (_∘_)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)
open import Relation.Nullary using (yes ; no)
import Data.Fin as Fin
import Data.Nat as ℕ




-- -- Types

-- module Ty where
--   infixr 2 _⊃_
--   infixr 5 _∶_

--   data Ty (g : Grt) : Set where
--     _∶_ : g ⊢◌ → Ty g → Ty g
--     _⊃_ : Ty ∅ → Ty ∅ → Ty g
--     _∧_ : Ty ∅ → Ty ∅ → Ty g
--     ⊥  : Ty g

--   ⊤ : Ty ∅
--   ⊤ = ⊥ ⊃ ⊥

--   ¬_ : Ty ∅ → Ty ∅
--   ¬ A = A ⊃ ⊥

--   wk : ∀ {g} → (i : ◌∈ g) → Ty (g ∖ᵍ i) → Ty g
--   wk i (t ∶ A) = Tm.wk i t ∶ wk i A
--   wk i (A ⊃ B) = A ⊃ B
--   wk i (A ∧ B) = A ∧ B
--   wk i ⊥      = ⊥

--   wk⋆ : ∀ {g} → (k : Fin (suc ⌊ g ⌋ᵍ)) → Ty (g ∖ᵍ⋆ k) → Ty g
--   wk⋆ {g}    zero     A = A
--   wk⋆ {∅}    (suc ()) A
--   wk⋆ {g ,◌} (suc k)  A = wk top (wk⋆ k A)

--   subst : ∀ {g} → Ty g → (i : ◌∈ g) → g ∖ᵍ i ⊢◌ → Ty (g ∖ᵍ i)
--   subst (t ∶ A) i s = Tm.subst t i s ∶ subst A i s
--   subst (A ⊃ B) i s = A ⊃ B
--   subst (A ∧ B) i s = A ∧ B
--   subst ⊥      i s = ⊥

--   _⫗_ : Ty ∅ → Ty ∅ → Ty ∅
--   A ⫗ B = (A ⊃ B) ∧ (B ⊃ A)

-- open Ty using (Ty ; _∶_ ; _⊃_ ; _∧_ ; ⊥ ; ⊤ ; ¬_ ; _⫗_)


-- -- Term vectors

-- module Vec where
--   infixr 5 _∷_

--   data Vec (g : Grt) : Lev → Set where
--     []  : Vec g zero
--     _∷_ : ∀ {n} → g ⊢◌ → Vec g n → Vec g (suc n)

--   vec : ∀ {g} → (Lev → g ⊢◌ → g ⊢◌) → (n : Lev) → Vec g n → Vec g n
--   vec f zero    []       = []
--   vec f (suc n) (t ∷ ts) = f n t ∷ vec f n ts

--   vec₂ : ∀ {g} → (Lev → g ⊢◌ → g ⊢◌ → g ⊢◌) → (n : Lev) → Vec g n → Vec g n → Vec g n
--   vec₂ f zero    []       []       = []
--   vec₂ f (suc n) (t ∷ ts) (u ∷ us) = f n t u ∷ vec₂ f n ts us

--   wk : ∀ {g n} → (i : ◌∈ g) → Vec (g ∖ᵍ i) n → Vec g n
--   wk i []       = []
--   wk i (t ∷ ts) = Tm.wk i t ∷ wk i ts

-- open Vec using (Vec ; [] ; _∷_ ; vec ; vec₂)


-- -- Term vector notation

-- VARs[_] : ∀ {g} → (n : Lev) → ◌∈ g → Vec g n
-- VARs[ zero ]  i = []
-- VARs[ suc n ] i = VAR[ n ] i ∷ VARs[ n ] i

-- LAMs[_] : ∀ {g} → (n : Lev) → Vec (g ,◌) n → Vec g n
-- LAMs[ zero ]  []       = []
-- LAMs[ suc n ] (t ∷ ts) = LAM[ n ] t ∷ LAMs[ n ] ts

-- APPs[_] PAIRs[_] : ∀ {g} → (n : Lev) → Vec g n → Vec g n → Vec g n
-- APPs[_]  = vec₂ APP[_]
-- PAIRs[_] = vec₂ PAIR[_]

-- FSTs[_] SNDs[_] UPs[_] DOWNs[_] BOOMs[_] : ∀ {g} → (n : Lev) → Vec g n → Vec g n
-- FSTs[_]  = vec FST[_]
-- SNDs[_]  = vec SND[_]
-- UPs[_]   = vec UP[_]
-- DOWNs[_] = vec DOWN[_]
-- BOOMs[_] = vec BOOM[_]


-- -- Contexts

-- infixl 2 _,_

-- data Ctx : Set where
--   ∅   : Ctx
--   _,_ : Ctx → Ty ∅ → Ctx

-- ⌊_⌋ᶜ : Ctx → Grt
-- ⌊ ∅ ⌋ᶜ     = ∅
-- ⌊ Γ , A ⌋ᶜ = ⌊ Γ ⌋ᶜ ,◌

-- ⌊_⌋ᵍᶜ : Ctx → ℕ
-- ⌊_⌋ᵍᶜ = ⌊_⌋ᵍ ∘ ⌊_⌋ᶜ


-- -- Variables

-- infixr 1 _∈_

-- data _∈_ (A : Ty ∅) : Ctx → Set where
--   top : ∀ {Γ} → A ∈ Γ , A
--   pop : ∀ {Γ B} → A ∈ Γ → A ∈ Γ , B

-- ⌊_⌋ᵛ : ∀ {Γ A} → A ∈ Γ → ◌∈ ⌊ Γ ⌋ᶜ
-- ⌊ top ⌋ᵛ   = top
-- ⌊ pop x ⌋ᵛ = pop ⌊ x ⌋ᵛ

-- ⌊_⌋ⁱᵛ : ∀ {Γ A} → A ∈ Γ → Fin ⌊ Γ ⌋ᵍᶜ
-- ⌊_⌋ⁱᵛ = ⌊_⌋ⁱ ∘ ⌊_⌋ᵛ


-- -- Derivations

-- infixr 5 _∴_

-- _∴_ : ∀ {g n} → Vec g n → Ty ∅ → Ty g
-- _∴_ {g} []       A rewrite ∖ᵍ⋆-zero g = Ty.wk⋆ (Fin.max ⌊ g ⌋ᵍ) A
-- _∴_ {g} (t ∷ ts) A = t ∶ ts ∴ A


-- infix 0 _⊢_

-- data _⊢_ (Γ : Ctx) : Ty ⌊ Γ ⌋ᶜ → Set where
--   var[_] : (n : Lev) → {A : Ty ∅} → {Z : Ty ⌊ Γ ⌋ᶜ}
--       → (v : A ∈ Γ)
--       → {{_ : VARs[ n ] ⌊ v ⌋ᵛ ∴ A ≡ Z}}
--       → Γ ⊢ Z

--   lam[_] : (n : Lev) → {ts : Vec (⌊ Γ ⌋ᶜ ,◌) n} → {A B : Ty ∅} → {Z : Ty ⌊ Γ ⌋ᶜ}
--       → Γ , A ⊢ ts ∴ B
--       → {{_ : LAMs[ n ] ts ∴ (A ⊃ B) ≡ Z}}
--       → Γ ⊢ Z

--   app[_] : (n : Lev) → {ts us : Vec ⌊ Γ ⌋ᶜ n} → {A B : Ty ∅} → {Z : Ty ⌊ Γ ⌋ᶜ}
--       → Γ ⊢ ts ∴ (A ⊃ B)    → Γ ⊢ us ∴ A
--       → {{_ : APPs[ n ] ts us ∴ B ≡ Z}}
--       → Γ ⊢ Z

--   pair[_] : (n : Lev) → {ts us : Vec ⌊ Γ ⌋ᶜ n} → {A B : Ty ∅} → {Z : Ty ⌊ Γ ⌋ᶜ}
--       → Γ ⊢ ts ∴ A    → Γ ⊢ us ∴ B
--       → {{_ : PAIRs[ n ] ts us ∴ (A ∧ B) ≡ Z}}
--       → Γ ⊢ Z

--   fst[_] : (n : Lev) → {ts : Vec ⌊ Γ ⌋ᶜ n} → {A B : Ty ∅} → {Z : Ty ⌊ Γ ⌋ᶜ}
--       → Γ ⊢ ts ∴ (A ∧ B)
--       → {{_ : FSTs[ n ] ts ∴ A ≡ Z}}
--       → Γ ⊢ Z

--   snd[_] : (n : Lev) → {ts : Vec ⌊ Γ ⌋ᶜ n} → {A B : Ty ∅} → {Z : Ty ⌊ Γ ⌋ᶜ}
--       → Γ ⊢ ts ∴ (A ∧ B)
--       → {{_ : SNDs[ n ] ts ∴ B ≡ Z}}
--       → Γ ⊢ Z

--   up[_] : (n : Lev) → {ts : Vec ⌊ Γ ⌋ᶜ n} → {u : ∅ ⊢◌} → {A : Ty ∅} → {Z : Ty ⌊ Γ ⌋ᶜ}
--       → Γ ⊢ ts ∴ u ∶ A
--       → {{_ : UPs[ n ] ts ∴ ! u ∶ u ∶ A ≡ Z}}
--       → Γ ⊢ Z

--   down[_] : (n : Lev) → {ts : Vec ⌊ Γ ⌋ᶜ n} → {u : ∅ ⊢◌} → {A : Ty ∅} → {Z : Ty ⌊ Γ ⌋ᶜ}
--       → Γ ⊢ ts ∴ u ∶ A
--       → {{_ : DOWNs[ n ] ts ∴ A ≡ Z}}
--       → Γ ⊢ Z

--   boom[_] : (n : Lev) → {ts : Vec ⌊ Γ ⌋ᶜ n} → {A : Ty ∅} → {Z : Ty ⌊ Γ ⌋ᶜ}
--       → Γ ⊢ ts ∴ ⊥
--       → {{_ : BOOMs[ n ] ts ∴ A ≡ Z}}
--       → Γ ⊢ Z

-- ⌊_⌋ : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → Γ ⊢ A → ⌊ Γ ⌋ᶜ ⊢◌
-- ⌊ var[ n ] v ⌋    = VAR[ n ] ⌊ v ⌋ᵛ
-- ⌊ lam[ n ] d ⌋    = LAM[ n ] ⌊ d ⌋
-- ⌊ app[ n ] d e ⌋  = APP[ n ] ⌊ d ⌋ ⌊ e ⌋
-- ⌊ pair[ n ] d e ⌋ = PAIR[ n ] ⌊ d ⌋ ⌊ e ⌋
-- ⌊ fst[ n ] d ⌋    = FST[ n ] ⌊ d ⌋
-- ⌊ snd[ n ] d ⌋    = SND[ n ] ⌊ d ⌋
-- ⌊ up[ n ] d ⌋     = UP[ n ] ⌊ d ⌋
-- ⌊ down[ n ] d ⌋   = DOWN[ n ] ⌊ d ⌋
-- ⌊ boom[ n ] d ⌋   = BOOM[ n ] ⌊ d ⌋


-- infixl 5 _∖ᶜ_ _∖ᶜ⋆_

-- _∖ᶜ_ : (Γ : Ctx) → {A : Ty ∅} → A ∈ Γ → Ctx
-- ∅       ∖ᶜ ()
-- (Γ , A) ∖ᶜ top   = Γ
-- (Γ , B) ∖ᶜ pop x = Γ ∖ᶜ x , B

-- ∖-dist : ∀ {Γ A} → (x : A ∈ Γ) → ⌊ Γ ∖ᶜ x ⌋ᶜ ≡ ⌊ Γ ⌋ᶜ ∖ᵍ ⌊ x ⌋ᵛ
-- ∖-dist top     = refl
-- ∖-dist (pop x) = cong _,◌ (∖-dist x)

-- _∖ᶜ⋆_ : (Γ : Ctx) → Fin (suc ⌊ Γ ⌋ᵍᶜ) → Ctx
-- Γ       ∖ᶜ⋆ zero   = Γ
-- ∅       ∖ᶜ⋆ suc ()
-- (Γ , _) ∖ᶜ⋆ suc k  = Γ ∖ᶜ⋆ k

-- ∖ᶜ⋆-zero : (Γ : Ctx) → ∅ ≡ Γ ∖ᶜ⋆ Fin.max ⌊ Γ ⌋ᵍᶜ
-- ∖ᶜ⋆-zero ∅       = refl
-- ∖ᶜ⋆-zero (Γ , _) = ∖ᶜ⋆-zero Γ


-- module Dn where
--   wkᵛ : ∀ {Γ X} → (x : X ∈ Γ) → X ∈ Γ ∖ᶜ x → X ∈ Γ
--   wkᵛ top     y       = pop y
--   wkᵛ (pop x) top     = top
--   wkᵛ (pop x) (pop y) = pop (wkᵛ x y)

--   ty-wk : ∀ {Γ X} → (x : X ∈ Γ) → Ty ⌊ Γ ∖ᶜ x ⌋ᶜ → Ty ⌊ Γ ⌋ᶜ
--   ty-wk top     A = Ty.wk top A
--   ty-wk (pop x) A rewrite ∖-dist x = Ty.wk (pop ⌊ x ⌋ᵛ) A

--   ty-wk⋆ : ∀ {Γ} → (k : Fin (suc ⌊ Γ ⌋ᵍᶜ)) → Ty ⌊ Γ ∖ᶜ⋆ k ⌋ᶜ → Ty ⌊ Γ ⌋ᶜ
--   ty-wk⋆ {Γ}     zero     A = A
--   ty-wk⋆ {∅}     (suc ()) A
--   ty-wk⋆ {Γ , X} (suc k)  A = ty-wk {X = X} top (ty-wk⋆ k A)

--   vec-wk : ∀ {Γ X n} → (x : X ∈ Γ) → Vec ⌊ Γ ∖ᶜ x ⌋ᶜ n → Vec ⌊ Γ ⌋ᶜ n
--   vec-wk top     ts = Vec.wk top ts
--   vec-wk (pop x) ts rewrite ∖-dist x = Vec.wk (pop ⌊ x ⌋ᵛ) ts

--   ∴-dist : ∀ {Γ X n} → (x : X ∈ Γ) → (ts : Vec ⌊ Γ ∖ᶜ x ⌋ᶜ n) → (A : Ty ∅) → vec-wk x ts ∴ A ≡ ty-wk x (ts ∴ A)
--   ∴-dist x []       A with vec-wk x [] ∴ A | ty-wk x ([] ∴ A)
--   ... | p | q = {!!}
--   ∴-dist x (t ∷ ts) A = {!!}

-- --   wk : ∀ {Γ A} → (x : A ∈ Γ) → {B : Ty ⌊ Γ ∖ᶜ x ⌋ᶜ} → {B′ : Ty ⌊ Γ ⌋ᶜ}
-- --       → Γ ∖ᶜ x ⊢ B
-- --       → {{_ : ty-wk x B ≡ B′}}
-- --       → Γ ⊢ B′
-- --   wk x (var[ n ] v)              {{refl}} = {!!} -- var[ n ] {!!}
-- --   wk x (lam[ n ] {ts} d)         {{refl}} = {!!} -- lam[ n ] {!!}
-- --   wk x (app[ n ] {ts} {us} d e)  {{refl}} = {!!} -- app[ n ] {!!} {!!}
-- --   wk x (pair[ n ] {ts} {us} d e) {{refl}} = {!!} -- pair[ n ] {!!} {!!}
-- --   wk x (fst[ n ] {ts} {A} {B} d {{refl}}) {{refl}} =
-- --      fst[ n ]
-- --        {ts = vec-wk x ts}
-- --        {A = {!A!}}
-- --        {B = B}
-- --        (wk x d {{{!refl!}}})
-- --   wk x (snd[ n ] {ts} d)         {{refl}} = {!!} -- snd[ n ] {!!}
-- --   wk x (up[ n ] {ts} d)          {{refl}} = {!!} -- up[ n ] {!!}
-- --   wk x (down[ n ] {ts} d)        {{refl}} = {!!} -- down[ n ] {!!}
-- --   wk x (boom[ n ] {ts} d)        {{refl}} = {!!} -- boom[ n ] {!!}









-- -- --  ty-wk′ : ∀ {Γ A} → (x : A ∈ Γ) → Ty (⌊ Γ ⌋ᶜ ∖ᵍ ⌊ x ⌋ᵛ) → Ty ⌊ Γ ⌋ᶜ
-- -- --  ty-wk′ top     B = Ty.wk top B
-- -- --  ty-wk′ (pop x) B = Ty.wk (pop ⌊ x ⌋ᵛ) B
-- -- --
-- -- --  ugh : ∀ {Γ A} → (x : A ∈ Γ) → Ty ⌊ Γ ∖ᶜ x ⌋ᶜ → Ty (⌊ Γ ⌋ᶜ ∖ᵍ ⌊ x ⌋ᵛ)
-- -- --  ugh x B rewrite ∖-dist x = B


-- -- -- -- -- -- Term notation

-- -- -- -- -- VAR  : ∀ {g} → Fin g → Tm g
-- -- -- -- -- LAM  : ∀ {g} → Tm (suc g) → Tm g
-- -- -- -- -- APP  : ∀ {g} → Tm g → Tm g → Tm g
-- -- -- -- -- PAIR : ∀ {g} → Tm g → Tm g → Tm g
-- -- -- -- -- FST  : ∀ {g} → Tm g → Tm g
-- -- -- -- -- SND  : ∀ {g} → Tm g → Tm g
-- -- -- -- -- UP   : ∀ {g} → Tm g → Tm g
-- -- -- -- -- DOWN : ∀ {g} → Tm g → Tm g
-- -- -- -- -- BOOM : ∀ {g} → Tm g → Tm g
-- -- -- -- -- VAR  = VAR[ 0 ]
-- -- -- -- -- LAM  = LAM[ 0 ]
-- -- -- -- -- APP  = APP[ 0 ]
-- -- -- -- -- PAIR = PAIR[ 0 ]
-- -- -- -- -- FST  = FST[ 0 ]
-- -- -- -- -- SND  = SND[ 0 ]
-- -- -- -- -- UP   = UP[ 0 ]
-- -- -- -- -- DOWN = DOWN[ 0 ]
-- -- -- -- -- BOOM = BOOM[ 0 ]

-- -- -- -- -- VAR²  : ∀ {g} → Fin g → Tm g
-- -- -- -- -- LAM²  : ∀ {g} → Tm (suc g) → Tm g
-- -- -- -- -- APP²  : ∀ {g} → Tm g → Tm g → Tm g
-- -- -- -- -- PAIR² : ∀ {g} → Tm g → Tm g → Tm g
-- -- -- -- -- FST²  : ∀ {g} → Tm g → Tm g
-- -- -- -- -- SND²  : ∀ {g} → Tm g → Tm g
-- -- -- -- -- UP²   : ∀ {g} → Tm g → Tm g
-- -- -- -- -- DOWN² : ∀ {g} → Tm g → Tm g
-- -- -- -- -- BOOM² : ∀ {g} → Tm g → Tm g
-- -- -- -- -- VAR²  = VAR[ 1 ]
-- -- -- -- -- LAM²  = LAM[ 1 ]
-- -- -- -- -- APP²  = APP[ 1 ]
-- -- -- -- -- PAIR² = PAIR[ 1 ]
-- -- -- -- -- FST²  = FST[ 1 ]
-- -- -- -- -- SND²  = SND[ 1 ]
-- -- -- -- -- UP²   = UP[ 1 ]
-- -- -- -- -- DOWN² = DOWN[ 1 ]
-- -- -- -- -- BOOM² = BOOM[ 1 ]

-- -- -- -- -- VAR³  : ∀ {g} → Fin g → Tm g
-- -- -- -- -- LAM³  : ∀ {g} → Tm (suc g) → Tm g
-- -- -- -- -- APP³  : ∀ {g} → Tm g → Tm g → Tm g
-- -- -- -- -- PAIR³ : ∀ {g} → Tm g → Tm g → Tm g
-- -- -- -- -- FST³  : ∀ {g} → Tm g → Tm g
-- -- -- -- -- SND³  : ∀ {g} → Tm g → Tm g
-- -- -- -- -- UP³   : ∀ {g} → Tm g → Tm g
-- -- -- -- -- DOWN³ : ∀ {g} → Tm g → Tm g
-- -- -- -- -- BOOM³ : ∀ {g} → Tm g → Tm g
-- -- -- -- -- VAR³  = VAR[ 2 ]
-- -- -- -- -- LAM³  = LAM[ 2 ]
-- -- -- -- -- APP³  = APP[ 2 ]
-- -- -- -- -- PAIR³ = PAIR[ 2 ]
-- -- -- -- -- FST³  = FST[ 2 ]
-- -- -- -- -- SND³  = SND[ 2 ]
-- -- -- -- -- UP³   = UP[ 2 ]
-- -- -- -- -- DOWN³ = DOWN[ 2 ]
-- -- -- -- -- BOOM³ = BOOM[ 2 ]

-- -- -- -- -- V0 : ∀ {g} → Tm (suc g)
-- -- -- -- -- V1 : ∀ {g} → Tm (suc (suc g))
-- -- -- -- -- V2 : ∀ {g} → Tm (suc (suc (suc g)))
-- -- -- -- -- V0 = VAR zero
-- -- -- -- -- V1 = VAR (suc zero)
-- -- -- -- -- V2 = VAR (suc (suc zero))

-- -- -- -- -- V0² : ∀ {g} → Tm (suc g)
-- -- -- -- -- V1² : ∀ {g} → Tm (suc (suc g))
-- -- -- -- -- V2² : ∀ {g} → Tm (suc (suc (suc g)))
-- -- -- -- -- V0² = VAR² zero
-- -- -- -- -- V1² = VAR² (suc zero)
-- -- -- -- -- V2² = VAR² (suc (suc zero))

-- -- -- -- -- V0³ : ∀ {g} → Tm (suc g)
-- -- -- -- -- V1³ : ∀ {g} → Tm (suc (suc g))
-- -- -- -- -- V2³ : ∀ {g} → Tm (suc (suc (suc g)))
-- -- -- -- -- V0³ = VAR³ zero
-- -- -- -- -- V1³ = VAR³ (suc zero)
-- -- -- -- -- V2³ = VAR³ (suc (suc zero))


-- -- -- -- -- -- Variable notation

-- -- -- -- -- 0ᵛ : ∀ {Γ} → {A : Ty zero} → Γ , A ∋ A
-- -- -- -- -- 0ᵛ = top

-- -- -- -- -- 1ᵛ : ∀ {Γ} → {A B : Ty zero} → Γ , A , B ∋ A
-- -- -- -- -- 1ᵛ = pop top

-- -- -- -- -- 2ᵛ : ∀ {Γ} → {A B C : Ty zero} → Γ , A , B , C ∋ A
-- -- -- -- -- 2ᵛ = pop (pop top)


-- -- -- -- -- -- -- Derivation notation, level 1

-- -- -- -- -- -- var : ∀ {Γ} → {A : Ty zero}
-- -- -- -- -- --     → (v : Γ ∋ A)
-- -- -- -- -- --     → Γ ⊢ A
-- -- -- -- -- -- var = var[ 0 ]

-- -- -- -- -- -- lam : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → {B : Ty (suc ⌊ Γ ⌋ᶜ)}
-- -- -- -- -- --     → Γ , A ⊢ B
-- -- -- -- -- --     → Γ ⊢ A ⊃ B
-- -- -- -- -- -- lam = lam[ 0 ] {ts = []}

-- -- -- -- -- -- app : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → {B : Ty (suc ⌊ Γ ⌋ᶜ)}
-- -- -- -- -- --     → Γ ⊢ A ⊃ B    → (e : Γ ⊢ A)
-- -- -- -- -- --     → Γ ⊢ ty.subst B zero ⌊ e ⌋
-- -- -- -- -- -- app = app[ 0 ] {ts = []} {us = []}

-- -- -- -- -- -- pair : ∀ {Γ} → {A B : Ty ⌊ Γ ⌋ᶜ}
-- -- -- -- -- --     → Γ ⊢ A    → Γ ⊢ B
-- -- -- -- -- --     → Γ ⊢ A ∧ B
-- -- -- -- -- -- pair = pair[ 0 ] {ts = []} {us = []}

-- -- -- -- -- -- fst : ∀ {Γ} → {A B : Ty ⌊ Γ ⌋ᶜ}
-- -- -- -- -- --     → Γ ⊢ A ∧ B
-- -- -- -- -- --     → Γ ⊢ A
-- -- -- -- -- -- fst = fst[ 0 ] {ts = []}

-- -- -- -- -- -- snd : ∀ {Γ} → {A B : Ty ⌊ Γ ⌋ᶜ}
-- -- -- -- -- --     → Γ ⊢ A ∧ B
-- -- -- -- -- --     → Γ ⊢ B
-- -- -- -- -- -- snd = snd[ 0 ] {ts = []}

-- -- -- -- -- -- up : ∀ {Γ} → {u : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ}
-- -- -- -- -- --     → Γ ⊢ u ∶ A
-- -- -- -- -- --     → Γ ⊢ ! u ∶ u ∶ A
-- -- -- -- -- -- up = up[ 0 ] {ts = []}

-- -- -- -- -- -- down : ∀ {Γ} → {u : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ}
-- -- -- -- -- --     → Γ ⊢ u ∶ A
-- -- -- -- -- --     → Γ ⊢ A
-- -- -- -- -- -- down = down[ 0 ] {ts = []}

-- -- -- -- -- -- boom : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ}
-- -- -- -- -- --     → Γ ⊢ ⊥ {⌊ Γ ⌋ᶜ}
-- -- -- -- -- --     → Γ ⊢ A
-- -- -- -- -- -- boom = boom[ 0 ] {ts = []}

-- -- -- -- -- -- v0 : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → Γ , A ⊢ ty.wk zero A
-- -- -- -- -- -- v0 = var 0ᵛ

-- -- -- -- -- -- v1 : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → {B : Ty (suc ⌊ Γ ⌋ᶜ)} → Γ , A , B ⊢ ty.wk zero (ty.wk zero A)
-- -- -- -- -- -- v1 = var 1ᵛ

-- -- -- -- -- -- v2 : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → {B : Ty (suc ⌊ Γ ⌋ᶜ)} → {C : Ty (suc (suc ⌊ Γ ⌋ᶜ))} → Γ , A , B , C ⊢ ty.wk zero (ty.wk zero (ty.wk zero A))
-- -- -- -- -- -- v2 = var 2ᵛ


-- -- -- -- -- -- -- Derivation notation, level 2

-- -- -- -- -- -- var² : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ}
-- -- -- -- -- --     → (v : Γ ∋ A)
-- -- -- -- -- --     → Γ ⊢ VAR[ 0 ] ⌊ v ⌋ᵛ ∶ A
-- -- -- -- -- -- var² = var[ 1 ]

-- -- -- -- -- -- lam² : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → {t : Tm (suc ⌊ Γ ⌋ᶜ)} → {B : Ty (suc ⌊ Γ ⌋ᶜ)}
-- -- -- -- -- --     → Γ , A ⊢ t ∶ B
-- -- -- -- -- --     → Γ ⊢ LAM[ 0 ] t ∶ (A ⊃ B)
-- -- -- -- -- -- lam² {t = t} = lam[ 1 ] {ts = t ∷ []}

-- -- -- -- -- -- app² : ∀ {Γ} → {t u : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ} → {B : Ty (suc ⌊ Γ ⌋ᶜ)}
-- -- -- -- -- --     → Γ ⊢ t ∶ (A ⊃ B)    → (e : Γ ⊢ u ∶ A)
-- -- -- -- -- --     → Γ ⊢ APP[ 0 ] t u ∶ ty.subst B zero ⌊ e ⌋
-- -- -- -- -- -- app² {t = t} {u} = app[ 1 ] {ts = t ∷ []} {us = u ∷ []}

-- -- -- -- -- -- pair² : ∀ {Γ} → {t u : Tm ⌊ Γ ⌋ᶜ} → {A B : Ty ⌊ Γ ⌋ᶜ}
-- -- -- -- -- --     → Γ ⊢ t ∶ A    → Γ ⊢ u ∶ B
-- -- -- -- -- --     → Γ ⊢ PAIR[ 0 ] t u ∶ (A ∧ B)
-- -- -- -- -- -- pair² {t = t} {u} = pair[ 1 ] {ts = t ∷ []} {us = u ∷ []}

-- -- -- -- -- -- fst² : ∀ {Γ} → {t : Tm ⌊ Γ ⌋ᶜ} → {A B : Ty ⌊ Γ ⌋ᶜ}
-- -- -- -- -- --     → Γ ⊢ t ∶ (A ∧ B)
-- -- -- -- -- --     → Γ ⊢ FST[ 0 ] t ∶ A
-- -- -- -- -- -- fst² {t = t} = fst[ 1 ] {ts = t ∷ []}

-- -- -- -- -- -- snd² : ∀ {Γ} → {t : Tm ⌊ Γ ⌋ᶜ} → {A B : Ty ⌊ Γ ⌋ᶜ}
-- -- -- -- -- --     → Γ ⊢ t ∶ (A ∧ B)
-- -- -- -- -- --     → Γ ⊢ SND[ 0 ] t ∶ B
-- -- -- -- -- -- snd² {t = t} = snd[ 1 ] {ts = t ∷ []}

-- -- -- -- -- -- up² : ∀ {Γ} → {t u : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ}
-- -- -- -- -- --     → Γ ⊢ t ∶ u ∶ A
-- -- -- -- -- --     → Γ ⊢ UP[ 0 ] t ∶ ! u ∶ u ∶ A
-- -- -- -- -- -- up² {t = t} = up[ 1 ] {ts = t ∷ []}

-- -- -- -- -- -- down² : ∀ {Γ} → {t u : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ}
-- -- -- -- -- --     → Γ ⊢ t ∶ u ∶ A
-- -- -- -- -- --     → Γ ⊢ DOWN[ 0 ] t ∶ A
-- -- -- -- -- -- down² {t = t} = down[ 1 ] {ts = t ∷ []}

-- -- -- -- -- -- boom² : ∀ {Γ} → {t : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ}
-- -- -- -- -- --     → Γ ⊢ t ∶ ⊥ {⌊ Γ ⌋ᶜ}
-- -- -- -- -- --     → Γ ⊢ BOOM[ 0 ] t ∶ A
-- -- -- -- -- -- boom² {t = t} = boom[ 1 ] {ts = t ∷ []}

-- -- -- -- -- -- v0² : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → Γ , A ⊢ V0 ∶ ty.wk zero A
-- -- -- -- -- -- v0² = var² 0ᵛ

-- -- -- -- -- -- v1² : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → {B : Ty (suc ⌊ Γ ⌋ᶜ)} → Γ , A , B ⊢ V1 ∶ ty.wk zero (ty.wk zero A)
-- -- -- -- -- -- v1² = var² 1ᵛ

-- -- -- -- -- -- v2² : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → {B : Ty (suc ⌊ Γ ⌋ᶜ)} → {C : Ty (suc (suc ⌊ Γ ⌋ᶜ))} → Γ , A , B , C ⊢ V2 ∶ ty.wk zero (ty.wk zero (ty.wk zero A))
-- -- -- -- -- -- v2² = var² 2ᵛ


-- -- -- -- -- -- -- Derivation notation, level 3

-- -- -- -- -- -- var³ : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ}
-- -- -- -- -- --     → (v : Γ ∋ A)
-- -- -- -- -- --     → Γ ⊢ VAR[ 1 ] ⌊ v ⌋ᵛ ∶ VAR[ 0 ] ⌊ v ⌋ᵛ ∶ A
-- -- -- -- -- -- var³ = var[ 2 ]

-- -- -- -- -- -- lam³ : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → {t₂ t : Tm (suc ⌊ Γ ⌋ᶜ)} → {B : Ty (suc ⌊ Γ ⌋ᶜ)}
-- -- -- -- -- --     → Γ , A ⊢ t₂ ∶ t ∶ B
-- -- -- -- -- --     → Γ ⊢ LAM[ 1 ] t₂ ∶ LAM[ 0 ] t ∶ (A ⊃ B)
-- -- -- -- -- -- lam³ {t₂ = t₂} {t} = lam[ 2 ] {ts = t₂ ∷ t ∷ []}

-- -- -- -- -- -- app³ : ∀ {Γ} → {t₂ t u₂ u : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ} → {B : Ty (suc ⌊ Γ ⌋ᶜ)}
-- -- -- -- -- --     → Γ ⊢ t₂ ∶ t ∶ (A ⊃ B)    → (e : Γ ⊢ u₂ ∶ u ∶ A)
-- -- -- -- -- --     → Γ ⊢ APP[ 1 ] t₂ u₂ ∶ APP[ 0 ] t u ∶ ty.subst B zero ⌊ e ⌋
-- -- -- -- -- -- app³ {t₂ = t₂} {t} {u₂} {u} = app[ 2 ] {ts = t₂ ∷ t ∷ []} {us = u₂ ∷ u ∷ []}

-- -- -- -- -- -- pair³ : ∀ {Γ} → {t₂ t u₂ u : Tm ⌊ Γ ⌋ᶜ} → {A B : Ty ⌊ Γ ⌋ᶜ}
-- -- -- -- -- --     → Γ ⊢ t₂ ∶ t ∶ A    → Γ ⊢ u₂ ∶ u ∶ B
-- -- -- -- -- --     → Γ ⊢ PAIR[ 1 ] t₂ u₂ ∶ PAIR[ 0 ] t u ∶ (A ∧ B)
-- -- -- -- -- -- pair³ {t₂ = t₂} {t} {u₂} {u} = pair[ 2 ] {ts = t₂ ∷ t ∷ []} {us = u₂ ∷ u ∷ []}

-- -- -- -- -- -- fst³ : ∀ {Γ} → {t₂ t : Tm ⌊ Γ ⌋ᶜ} → {A B : Ty ⌊ Γ ⌋ᶜ}
-- -- -- -- -- --     → Γ ⊢ t₂ ∶ t ∶ (A ∧ B)
-- -- -- -- -- --     → Γ ⊢ FST[ 1 ] t₂ ∶ FST[ 0 ] t ∶ A
-- -- -- -- -- -- fst³ {t₂ = t₂} {t} = fst[ 2 ] {ts = t₂ ∷ t ∷ []}

-- -- -- -- -- -- snd³ : ∀ {Γ} → {t₂ t : Tm ⌊ Γ ⌋ᶜ} → {A B : Ty ⌊ Γ ⌋ᶜ}
-- -- -- -- -- --     → Γ ⊢ t₂ ∶ t ∶ (A ∧ B)
-- -- -- -- -- --     → Γ ⊢ SND[ 1 ] t₂ ∶ SND[ 0 ] t ∶ B
-- -- -- -- -- -- snd³ {t₂ = t₂} {t} = snd[ 2 ] {ts = t₂ ∷ t ∷ []}

-- -- -- -- -- -- up³ : ∀ {Γ} → {t₂ t u : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ}
-- -- -- -- -- --     → Γ ⊢ t₂ ∶ t ∶ u ∶ A
-- -- -- -- -- --     → Γ ⊢ UP[ 1 ] t₂ ∶ UP[ 0 ] t ∶ ! u ∶ u ∶ A
-- -- -- -- -- -- up³ {t₂ = t₂} {t} = up[ 2 ] {ts = t₂ ∷ t ∷ []}

-- -- -- -- -- -- down³ : ∀ {Γ} → {t₂ t u : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ}
-- -- -- -- -- --     → Γ ⊢ t₂ ∶ t ∶ u ∶ A
-- -- -- -- -- --     → Γ ⊢ DOWN[ 1 ] t₂ ∶ DOWN[ 0 ] t ∶ A
-- -- -- -- -- -- down³ {t₂ = t₂} {t} = down[ 2 ] {ts = t₂ ∷ t ∷ []}

-- -- -- -- -- -- boom³ : ∀ {Γ} → {t₂ t : Tm ⌊ Γ ⌋ᶜ} → {A : Ty ⌊ Γ ⌋ᶜ}
-- -- -- -- -- --     → Γ ⊢ t₂ ∶ t ∶ ⊥ {⌊ Γ ⌋ᶜ}
-- -- -- -- -- --     → Γ ⊢ BOOM[ 1 ] t₂ ∶ BOOM[ 0 ] t ∶ A
-- -- -- -- -- -- boom³ {t₂ = t₂} {t} = boom[ 2 ] {ts = t₂ ∷ t ∷ []}

-- -- -- -- -- -- v0³ : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → Γ , A ⊢ V0² ∶ V0 ∶ ty.wk zero A
-- -- -- -- -- -- v0³ = var³ 0ᵛ

-- -- -- -- -- -- v1³ : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → {B : Ty (suc ⌊ Γ ⌋ᶜ)} → Γ , A , B ⊢ V1² ∶ V1 ∶ ty.wk zero (ty.wk zero A)
-- -- -- -- -- -- v1³ = var³ 1ᵛ

-- -- -- -- -- -- v2³ : ∀ {Γ} → {A : Ty ⌊ Γ ⌋ᶜ} → {B : Ty (suc ⌊ Γ ⌋ᶜ)} → {C : Ty (suc (suc ⌊ Γ ⌋ᶜ))} → Γ , A , B , C ⊢ V2² ∶ V2 ∶ ty.wk zero (ty.wk zero (ty.wk zero A))
-- -- -- -- -- -- v2³ = var³ 2ᵛ


-- -- -- -- -- -- -- Examples

-- -- -- -- -- -- module ex where
-- -- -- -- -- --   open ty renaming (wk to w)

-- -- -- -- -- --   I : ∀ {Γ} {A : Ty ⌊ Γ ⌋ᶜ} → Γ ⊢ A ⊃ w zero A
-- -- -- -- -- --   I = lam v0

-- -- -- -- -- --   K : ∀ {Γ} {A B : Ty ⌊ Γ ⌋ᶜ} → Γ ⊢ A ⊃ w zero B ⊃ w zero (w zero A)
-- -- -- -- -- --   K = lam (lam v1)
