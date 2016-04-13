module AltArtemov.Type.Properties where

open import Data.Nat using (ℕ ; zero ; suc ; _<′_)
open import Function using (_∘_)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Nullary using (yes ; no)

open import AltArtemov.Term.Properties using () renaming (_≟_ to _Tm≟_)
open import AltArtemov.Type.Core
open import AltArtemov.Type.Inversions
open import Data.Nat.Missing


-- Types have levels.
lev : ∀ A → ℕ
lev ⊥      = 0
lev (A ⊃ B) = 0
lev (t ∶ A) = suc (lev A)


-- Asserting a type increments its level.
lev-t∶A≡suc-lev-A : ∀ {t A} → lev (t ∶ A) ≡ suc (lev A)
lev-t∶A≡suc-lev-A = refl


-- The level of a type assertion is greater than 0.
z<′lev-t∶A : ∀ t A → zero <′ lev (t ∶ A)
z<′lev-t∶A t A = z<′sn


-- Types of level greater than 0 can be lowered.
lower : ∀ A → zero <′ lev A → Ty
lower ⊥      ()
lower (A ⊃ B) ()
lower (t ∶ A) z<′l = A


-- Lowering a type assertion gives the asserted type.
lower-t∶A≡A : ∀ {t A} → lower (t ∶ A) (z<′lev-t∶A t A) ≡ A
lower-t∶A≡A = refl


-- Type equality is decidable.
_≟_ : Decidable {A = Ty} _≡_
⊥      ≟ ⊥        = yes refl
⊥      ≟ (_ ⊃ _)   = no λ ()
⊥      ≟ (_ ∶ _)   = no λ ()
(_ ⊃ _) ≟ ⊥        = no λ ()
(A ⊃ B) ≟ (A′ ⊃ B′) with A ≟ A′ | B ≟ B′
(A ⊃ B) ≟ (.A ⊃ .B) | yes refl | yes refl = yes refl
...                 | no  A≢A′ | _        = no (A≢A′ ∘ ⊃-inv-A)
...                 | _        | no  B≢B′ = no (B≢B′ ∘ ⊃-inv-B)
(_ ⊃ _) ≟ (_ ∶ _)   = no λ ()
(_ ∶ _) ≟ ⊥        = no λ ()
(_ ∶ _) ≟ (_ ⊃ _)   = no λ ()
(t ∶ A) ≟ (t′ ∶ A′) with t Tm≟ t′ | A ≟ A′
(t ∶ A) ≟ (.t ∶ .A) | yes refl | yes refl = yes refl
...                 | no  t≢t′ | _        = no (t≢t′ ∘ ∶-inv-t)
...                 | _        | no  A≢A′ = no (A≢A′ ∘ ∶-inv-A)
