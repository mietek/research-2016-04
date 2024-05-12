module Try2.AltArtemov.Context.Representation.Equality where

open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Nullary using (Dec ; yes ; no)

open import Try2.AltArtemov.Context.Representation.Core


_≟ᵍ_ : (g g′ : CxR) → Dec (g ≡ g′)
∅      ≟ᵍ ∅       = yes refl
∅      ≟ᵍ (_ ,◌)  = no λ ()
(_ ,◌) ≟ᵍ ∅       = no λ ()
(g ,◌) ≟ᵍ (g′ ,◌) with g ≟ᵍ g′
(g ,◌) ≟ᵍ (.g ,◌) | yes refl = yes refl
...               | no  g≢g′ = no (g≢g′ ∘ inv-,◌)
