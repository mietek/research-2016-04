module Data.Fin.Missing where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin ; zero ; suc)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Nullary using (Dec ; yes ; no)


sup : (n : ℕ) → Fin (ℕ.suc n)
sup ℕ.zero    = zero
sup (ℕ.suc n) = suc (sup n)


inv-suc : ∀ {n} {i i′ : Fin n} → suc i ≡ suc i′ → i ≡ i′
inv-suc refl = refl


_≡?_ : ∀ {n} → (i i′ : Fin n) → Dec (i ≡ i′)
zero  ≡? zero   = yes refl
zero  ≡? suc _  = no λ ()
suc _ ≡? zero   = no λ ()
suc i ≡? suc i′ with i ≡? i′
suc i ≡? suc .i | yes refl = yes refl
...             | no  i≢i′ = no (i≢i′ ∘ inv-suc)
