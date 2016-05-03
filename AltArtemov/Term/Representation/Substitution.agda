module AltArtemov.Term.Representation.Substitution where

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Fin using (Fin ; zero ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)

open import AltArtemov.Context.Representation
open import AltArtemov.Term.Representation.Core
open import AltArtemov.Term.Representation.Vector
open import AltArtemov.Variable.Representation
open import Data.Fin.Missing


_∖ᵍ_ : (g : CxR) → ◌∈ g → CxR
∅      ∖ᵍ ()
(g ,◌) ∖ᵍ top   = g
(g ,◌) ∖ᵍ pop i = (g ∖ᵍ i) ,◌


wkⁱ : ∀ {g} → (i : ◌∈ g) → ◌∈ (g ∖ᵍ i) → ◌∈ g
wkⁱ top     j       = pop j
wkⁱ (pop i) top     = top
wkⁱ (pop i) (pop j) = pop (wkⁱ i j)


data _≈ⁱ_ {g : CxR} : ◌∈ g → ◌∈ g → Set where
  same : {i : ◌∈ g} → i ≈ⁱ i
  diff : (i : ◌∈ g) → (j : ◌∈ (g ∖ᵍ i)) → i ≈ⁱ wkⁱ i j


_≈?ⁱ_ : ∀ {g} → (i j : ◌∈ g) → i ≈ⁱ j
top   ≈?ⁱ top            = same
top   ≈?ⁱ pop j          = diff top j
pop i ≈?ⁱ top            = diff (pop i) top
pop i ≈?ⁱ pop j          with i ≈?ⁱ j
pop i ≈?ⁱ pop .i         | same = same
pop i ≈?ⁱ pop .(wkⁱ i j) | diff .i j = diff (pop i) (pop j)


wkᵗ : ∀ {g} → (i : ◌∈ g) → (g ∖ᵍ i) ⊢◌ → g ⊢◌
wkᵗ i (VAR[ n ] j)    = VAR[ n ] (wkⁱ i j)
wkᵗ i (LAM[ n ] t)    = LAM[ n ] (wkᵗ (pop i) t)
wkᵗ i (APP[ n ] t u)  = APP[ n ] (wkᵗ i t) (wkᵗ i u)
wkᵗ i (PAIR[ n ] t u) = PAIR[ n ] (wkᵗ i t) (wkᵗ i u)
wkᵗ i (FST[ n ] t)    = FST[ n ] (wkᵗ i t)
wkᵗ i (SND[ n ] t)    = SND[ n ] (wkᵗ i t)
wkᵗ i (UP[ n ] t)     = UP[ n ] (wkᵗ i t)
wkᵗ i (DOWN[ n ] t)   = DOWN[ n ] (wkᵗ i t)
wkᵗ i (BOOM[ n ] t)   = BOOM[ n ] (wkᵗ i t)
wkᵗ i (! t)           = ! wkᵗ i t


wkᵛ : ∀ {g n} → (i : ◌∈ g) → Vec (g ∖ᵍ i) n → Vec g n
wkᵛ i []       = []
wkᵛ i (t ∷ ts) = wkᵗ i t ∷ wkᵛ i ts


substⁱ : ∀ {g} → ℕ → ◌∈ g → (i : ◌∈ g) → (g ∖ᵍ i) ⊢◌ → (g ∖ᵍ i) ⊢◌
substⁱ n j          i  s with i ≈?ⁱ j
substⁱ n i          .i s | same = s
substⁱ n .(wkⁱ i j) i  s | diff .i j = VAR[ n ] j


substᵗ : ∀ {g} → g ⊢◌ → (i : ◌∈ g) → (g ∖ᵍ i) ⊢◌ → (g ∖ᵍ i) ⊢◌
substᵗ (VAR[ n ] j)    i s = substⁱ n j i s
substᵗ (LAM[ n ] t)    i s = LAM[ n ] (substᵗ t (pop i) (wkᵗ top s))
substᵗ (APP[ n ] t u)  i s = APP[ n ] (substᵗ t i s) (substᵗ u i s)
substᵗ (PAIR[ n ] t u) i s = PAIR[ n ] (substᵗ t i s) (substᵗ u i s)
substᵗ (FST[ n ] t)    i s = FST[ n ] (substᵗ t i s)
substᵗ (SND[ n ] t)    i s = SND[ n ] (substᵗ t i s)
substᵗ (UP[ n ] t)     i s = UP[ n ] (substᵗ t i s)
substᵗ (DOWN[ n ] t)   i s = DOWN[ n ] (substᵗ t i s)
substᵗ (BOOM[ n ] t)   i s = BOOM[ n ] (substᵗ t i s)
substᵗ (! t)           i s = ! substᵗ t i s


substᵛ : ∀ {g n} → Vec g n → (i : ◌∈ g) → (g ∖ᵍ i) ⊢◌ → Vec (g ∖ᵍ i) n
substᵛ []       i s = []
substᵛ (t ∷ ts) i s = substᵗ t i s ∷ substᵛ ts i s
