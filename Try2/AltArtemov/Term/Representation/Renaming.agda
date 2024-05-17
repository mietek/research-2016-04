module Try2.AltArtemov.Term.Representation.Renaming where

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Fin using (Fin ; zero ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)

open import Try2.AltArtemov.Context.Representation
open import Try2.AltArtemov.Term.Representation.Core
open import Try2.AltArtemov.Term.Representation.Vector
open import Try2.AltArtemov.Variable.Representation


RRen : (CxR → Set) → CxR → CxR → Set
RRen X g g′ = X g → X g′


renⁱ : ∀ {g g′} → g′ ≥ᵍ g → RRen ◌∈_ g g′
renⁱ id       x       = x
renⁱ (weak r) x       = pop (renⁱ r x)
renⁱ (lift r) top     = top
renⁱ (lift r) (pop x) = pop (renⁱ r x)


renᵗ : ∀ {g g′} → g′ ≥ᵍ g → RRen _⊢◌ g g′
renᵗ r (VAR[ n ] i)    = VAR[ n ] (renⁱ r i)
renᵗ r (LAM[ n ] t)    = LAM[ n ] (renᵗ (lift r) t)
renᵗ r (APP[ n ] t u)  = APP[ n ] (renᵗ r t) (renᵗ r u)
renᵗ r (PAIR[ n ] t u) = PAIR[ n ] (renᵗ r t) (renᵗ r u)
renᵗ r (FST[ n ] t)    = FST[ n ] (renᵗ r t)
renᵗ r (SND[ n ] t)    = SND[ n ] (renᵗ r t)
renᵗ r (UP[ n ] t)     = UP[ n ] (renᵗ r t)
renᵗ r (DOWN[ n ] t)   = DOWN[ n ] (renᵗ r t)
renᵗ r (BOOM[ n ] t)   = BOOM[ n ] (renᵗ r t)
renᵗ r (! t)           = ! (renᵗ r t)


mutual
  ren-nenr : ∀ {d d′} → d′ ≥ᵍ d → RRen (NeR NfR) d d′
  ren-nenr r (VAR[ n ] i)   = VAR[ n ] (renⁱ r i)
  ren-nenr r (APP[ n ] t u) = APP[ n ] (ren-nenr r t) (ren-nfr r u)
  ren-nenr r (FST[ n ] t)   = FST[ n ] (ren-nenr r t)
  ren-nenr r (SND[ n ] t)   = SND[ n ] (ren-nenr r t)
  ren-nenr r (DOWN[ n ] t)  = DOWN[ n ] (ren-nenr r t)
  ren-nenr r (BOOM[ n ] t)  = BOOM[ n ] (ren-nenr r t)

  ren-nevr : ∀ {d d′} → d′ ≥ᵍ d → RRen (NeR ValR) d d′
  ren-nevr r (VAR[ n ] i)   = VAR[ n ] (renⁱ r i)
  ren-nevr r (APP[ n ] t u) = APP[ n ] (ren-nevr r t) (ren-valr r u)
  ren-nevr r (FST[ n ] t)   = FST[ n ] (ren-nevr r t)
  ren-nevr r (SND[ n ] t)   = SND[ n ] (ren-nevr r t)
  ren-nevr r (DOWN[ n ] t)  = DOWN[ n ] (ren-nevr r t)
  ren-nevr r (BOOM[ n ] t)  = BOOM[ n ] (ren-nevr r t)

  ren-nfr : ∀ {d d′} → d′ ≥ᵍ d → RRen NfR d d′
  ren-nfr r (NE v)          = NE (ren-nenr r v)
  ren-nfr r (LAM[ n ] t)    = LAM[ n ] (ren-nfr (lift r) t)
  ren-nfr r (PAIR[ n ] t u) = PAIR[ n ] (ren-nfr r t) (ren-nfr r u)
  ren-nfr r (UP[ n ] t)     = UP[ n ] (ren-nfr r t)
  ren-nfr r (! t)          = ! (ren-nfr r t)

  ren-valr : ∀ {d d′} → d′ ≥ᵍ d → RRen ValR d d′
  ren-valr r (NE v)          = NE (ren-nevr r v)
  ren-valr r (LAM[ n ] t e)  = LAM[ n ] t (ren-envr r e)
  ren-valr r (PAIR[ n ] t u) = PAIR[ n ] (ren-valr r t) (ren-valr r u)
  ren-valr r (UP[ n ] t)     = UP[ n ] (ren-valr r t)

  ren-envr : ∀ {d d′ g} → d′ ≥ᵍ d → EnvR d g → EnvR d′ g
  ren-envr r ∅       = ∅
  ren-envr r (e , t) = (ren-envr r e , ren-valr r t)
