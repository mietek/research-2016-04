module Data.Nat.Missing where

open import Data.Empty renaming (⊥-elim to expl)
open import Data.Nat using (ℕ ; zero ; suc ; pred ; _⊓_ ; ≤-pred ; _≤_ ; z≤n ; s≤s ; _≤?_ ; _≤′_ ; ≤′-refl ; ≤′-step ; _<_ ; _<′_)
open import Data.Nat.Properties using (≤⇒≤′ ; ≤′⇒≤ ; z≤′n ; s≤′s)
open import Data.Product using (proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Function using (_∘_)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)
open import Relation.Nullary using (¬_ ; yes ; no)

open import Algebra using (module CommutativeSemiringWithoutOne ; module DistributiveLattice)
import Data.Nat.Properties as ℕ
open module ℕCSWO = CommutativeSemiringWithoutOne ℕ.⊔-⊓-0-commutativeSemiringWithoutOne using (*-isSemigroup) renaming (zero to ⊓-zero)
open module ℕDL = DistributiveLattice ℕ.distributiveLattice using () renaming (∨-comm to ⊓-comm ; ∨-assoc to ⊓-assoc) public

open import Relation.Binary using (module DecTotalOrder)
import Data.Nat as ℕ
open module ℕDTO = DecTotalOrder ℕ.decTotalOrder using () renaming (trans to ≤-trans ; total to ≤-total) public


⊓-zeroᴸ : ∀ n → zero ⊓ n ≡ zero
⊓-zeroᴸ = proj₁ ⊓-zero

⊓-zeroᴿ : ∀ n → n ⊓ zero ≡ zero
⊓-zeroᴿ = proj₂ ⊓-zero


m⊓pn≡p[sm⊓n] : ∀ m n → m ⊓ pred n ≡ pred (suc m ⊓ n)
m⊓pn≡p[sm⊓n] m zero    rewrite ⊓-comm m zero = refl
m⊓pn≡p[sm⊓n] m (suc n) rewrite ⊓-comm m n    = refl

m⊓pn⊓po≡p[sm⊓n⊓o] : ∀ m n o → (m ⊓ pred n) ⊓ pred o ≡ pred ((suc m ⊓ n) ⊓ o)
m⊓pn⊓po≡p[sm⊓n⊓o] m n       zero    rewrite ⊓-zeroᴿ (m ⊓ pred n) | ⊓-zeroᴿ (suc m ⊓ n) = refl
m⊓pn⊓po≡p[sm⊓n⊓o] m zero    (suc o) rewrite ⊓-comm m zero = refl
m⊓pn⊓po≡p[sm⊓n⊓o] m (suc n) (suc o) = refl


n≤sn : ∀ {n} → n ≤ suc n
n≤sn {zero}  = z≤n
n≤sn {suc m} = s≤s n≤sn

sm≤n⇒m≤n : ∀ {m n} → suc m ≤ n → m ≤ n
sm≤n⇒m≤n sm≤n = ≤-trans n≤sn sm≤n


_<?_ : Decidable _<_
zero  <? zero  = no λ ()
zero  <? suc n = yes (s≤s z≤n)
suc m <? zero  = no λ ()
suc m <? suc n with m <? n
...            | yes m<n = yes (s≤s m<n)
...            | no  m≮n = no (m≮n ∘ ≤-pred)

_<′?_ : Decidable _<′_
m <′? n with m <? n
... | yes m<n = yes (≤⇒≤′ m<n)
... | no  m≮n = no  (m≮n ∘ ≤′⇒≤)


z<′sn : ∀ {n} → zero <′ suc n
z<′sn {zero}  = ≤′-refl
z<′sn {suc n} = s≤′s z≤′n


≤′-pred : ∀ {m n} → suc m ≤′ suc n → m ≤′ n
≤′-pred = ≤⇒≤′ ∘ ≤-pred ∘ ≤′⇒≤

≤′-trans : ∀ {m n o} → m ≤′ n → n ≤′ o → m ≤′ o
≤′-trans m≤′n n≤′o = ≤⇒≤′ (≤-trans (≤′⇒≤ m≤′n) (≤′⇒≤ n≤′o))

≤′-total : ∀ m n → m ≤′ n ⊎ n ≤′ m
≤′-total m n with ≤-total m n
...          | inj₁ m≤n = inj₁ (≤⇒≤′ m≤n)
...          | inj₂ n≤m = inj₂ (≤⇒≤′ n≤m)


_≤′?_ : Decidable _≤′_
m ≤′? n with m ≤? n
... | yes m≤n = yes (≤⇒≤′ m≤n)
... | no  m≰n = no  (m≰n ∘ ≤′⇒≤)


_≰′_ : ℕ → ℕ → Set
n ≰′ m = ¬ n ≤′ m

≰′-excl : ∀ {m n} → m ≰′ n → n ≤′ m
≰′-excl {m} {n} m≰′n with ≤′-total m n
...                  | inj₁ m≤′n = expl (m≰′n m≤′n)
...                  | inj₂ n≤′m = n≤′m


≤′-idᴿ-⊓ : ∀ {m n} → m ≤′ n → m ⊓ n ≡ m
≤′-idᴿ-⊓ {zero}  {n}     m≤′n   = refl
≤′-idᴿ-⊓ {suc m} {zero}  ()
≤′-idᴿ-⊓ {suc m} {suc n} sm≤′sn = cong suc (≤′-idᴿ-⊓ (≤′-pred sm≤′sn))

≰′-idᴸ-⊓ : ∀ {m n} → m ≰′ n → m ⊓ n ≡ n
≰′-idᴸ-⊓ {m} {n} m≰′n rewrite ⊓-comm m n = ≤′-idᴿ-⊓ (≰′-excl m≰′n)


k<′m⊓n⇒k<′n : ∀ m {n k} → k <′ m ⊓ n → k <′ n
k<′m⊓n⇒k<′n m {n} k<′m⊓n with m ≤′? n
...                     | yes m≤′n rewrite ≤′-idᴿ-⊓ m≤′n = ≤′-trans k<′m⊓n m≤′n
...                     | no  m≰′n rewrite ≰′-idᴸ-⊓ m≰′n = k<′m⊓n

k<′m⊓n⇒k<′m : ∀ {m} n {k} → k <′ m ⊓ n → k <′ m
k<′m⊓n⇒k<′m {m} n k<′m⊓n rewrite ⊓-comm m n = k<′m⊓n⇒k<′n n k<′m⊓n


z<′sn⊓m⇒z<′m : ∀ n {m} → zero <′ suc n ⊓ m → zero <′ m
z<′sn⊓m⇒z<′m n z<′l = k<′m⊓n⇒k<′n (suc n) z<′l

z<′sn⊓m⊓o⇒z<′m : ∀ n {m} o → zero <′ suc n ⊓ m ⊓ o → zero <′ m
z<′sn⊓m⊓o⇒z<′m n {m} o z<′l = k<′m⊓n⇒k<′n (suc n) (k<′m⊓n⇒k<′m o z<′l)

z<′sn⊓m⊓o⇒z<′o : ∀ n m {o} → zero <′ suc n ⊓ m ⊓ o → zero <′ o
z<′sn⊓m⊓o⇒z<′o n m {o} z<′l = k<′m⊓n⇒k<′n (suc n ⊓ m) z<′l
