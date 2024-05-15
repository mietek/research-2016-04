module AltArtemov.Type.Properties where

open import Data.Empty using () renaming (⊥ to Empty)
open import Data.Nat using (ℕ ; zero ; suc ; _<′_) renaming (_≟_ to _ℕ≟_)
open import Data.Maybe using (Maybe ; nothing ; just)
open import Data.Unit using () renaming (⊤ to Unit)
open import Function using (_∘_)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Nullary using (yes ; no)

open import AltArtemov.Term
open import AltArtemov.Type.Core
open import AltArtemov.Type.Inversions
open import Data.Nat.Missing


-- Types have levels.
lev : ∀ (A : Ty) → ℕ
lev ⊥      = 0
lev (A ⊃ B) = 0
lev (A ∧ B) = 0
lev (t ∶ A) = suc (lev A)
lev (A ≑ B) = 0


-- Asserting a type increments its level.
lev-t∶A≡suc-lev-A : ∀ t A → lev (t ∶ A) ≡ suc (lev A)
lev-t∶A≡suc-lev-A t A = refl


-- The level of a type assertion is greater than 0.
z<′lev-t∶A : ∀ t A → zero <′ lev (t ∶ A)
z<′lev-t∶A t A = z<′sn


-- Types of level greater than 0 can be lowered.
lower : ∀ A (z<′l : zero <′ lev A) → Ty
lower ⊥      ()
lower (A ⊃ B) ()
lower (A ∧ B) ()
lower (t ∶ A) z<′l = A
lower (A ≑ B) ()


-- Lowering a type assertion gives the asserted type.
lower-t∶A≡A : ∀ t A → lower (t ∶ A) (z<′lev-t∶A t A) ≡ A
lower-t∶A≡A t A = refl


-- Types of level greater than 0 have terms.
tm : ∀ A (z<′l : zero <′ lev A) → Tm
tm ⊥      ()
tm (A ⊃ B) ()
tm (A ∧ B) ()
tm (t ∶ A) z<′l = t
tm (A ≑ B) ()


-- Type equality is decidable.
_≟_ : Decidable {A = Ty} _≡_
⊥      ≟ ⊥        = yes refl
⊥      ≟ (_ ⊃ _)   = no λ ()
⊥      ≟ (_ ∧ _)   = no λ ()
⊥      ≟ (_ ∶ _)   = no λ ()
⊥      ≟ (_ ≑ _)   = no λ ()
(_ ⊃ _) ≟ ⊥        = no λ ()
(A ⊃ B) ≟ (A′ ⊃ B′) with A ≟ A′ | B ≟ B′
(A ⊃ B) ≟ (.A ⊃ .B) | yes refl | yes refl = yes refl
...                 | no  A≢A′ | _        = no (A≢A′ ∘ ⊃-inv-A)
...                 | _        | no  B≢B′ = no (B≢B′ ∘ ⊃-inv-B)
(_ ⊃ _) ≟ (_ ∧ _)   = no λ ()
(_ ⊃ _) ≟ (_ ∶ _)   = no λ ()
(_ ⊃ _) ≟ (_ ≑ _)   = no λ ()
(_ ∧ _) ≟ ⊥        = no λ ()
(_ ∧ _) ≟ (_ ⊃ _)   = no λ ()
(A ∧ B) ≟ (A′ ∧ B′) with A ≟ A′ | B ≟ B′
(A ∧ B) ≟ (.A ∧ .B) | yes refl | yes refl = yes refl
...                 | no  A≢A′ | _        = no (A≢A′ ∘ ∧-inv-A)
...                 | _        | no  B≢B′ = no (B≢B′ ∘ ∧-inv-B)
(_ ∧ _) ≟ (_ ∶ _)   = no λ ()
(_ ∧ _) ≟ (_ ≑ _)   = no λ ()
(_ ∶ _) ≟ ⊥        = no λ ()
(_ ∶ _) ≟ (_ ⊃ _)   = no λ ()
(_ ∶ _) ≟ (_ ∧ _)   = no λ ()
(t ∶ A) ≟ (t′ ∶ A′) with t Tm≟ t′ | A ≟ A′
(t ∶ A) ≟ (.t ∶ .A) | yes refl | yes refl = yes refl
...                 | no  t≢t′ | _        = no (t≢t′ ∘ ∶-inv-t)
...                 | _        | no  A≢A′ = no (A≢A′ ∘ ∶-inv-A)
(_ ∶ _) ≟ (_ ≑ _)   = no λ ()
(_ ≑ _) ≟ ⊥        = no λ ()
(_ ≑ _) ≟ (_ ⊃ _)   = no λ ()
(_ ≑ _) ≟ (_ ∧ _)   = no λ ()
(_ ≑ _) ≟ (_ ∶ _)   = no λ ()
(A ≑ B) ≟ (A′ ≑ B′) with A ≟ A′ | B ≟ B′
(A ≑ B) ≟ (.A ≑ .B) | yes refl | yes refl = yes refl
...                 | no  A≢A′ | _        = no (A≢A′ ∘ ≑-inv-A)
...                 | _        | no  B≢B′ = no (B≢B′ ∘ ≑-inv-B)


-- TODO

can-lower : ∀ (A : Ty) → Maybe Ty
can-lower ⊥      = nothing
can-lower (A ⊃ B) = nothing
can-lower (A ∧ B) = nothing
can-lower (t ∶ A) = just A
can-lower (A ≑ B) = nothing

HighTy : ∀ A → Set
HighTy A with can-lower A
...      | just A′ = Unit
...      | _       = Empty

lower′ : ∀ A {HA : HighTy A} → Ty
lower′ A {HA} with can-lower A
lower′ A {HA} | just A′ = A′
lower′ A {()} | nothing
