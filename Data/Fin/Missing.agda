module Data.Fin.Missing where

open import Data.Fin using (Fin ; zero ; suc)
open import Function using (_∘_)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Nullary using (yes ; no)


suc-inv : ∀ {n} {i j : Fin n} → suc i ≡ suc j → i ≡ j
suc-inv refl = refl


_≟_ : ∀ {n} → Decidable {A = Fin n} _≡_
zero  ≟ zero   = yes refl
suc i ≟ suc j  with i ≟ j
suc i ≟ suc .i | yes refl = yes refl
suc i ≟ suc j  | no  i≢j  = no (i≢j ∘ suc-inv)
zero  ≟ suc j  = no λ ()
suc i ≟ zero   = no λ ()
