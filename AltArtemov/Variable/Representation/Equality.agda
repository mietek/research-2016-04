module AltArtemov.Variable.Representation.Equality where

open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Nullary using (Dec ; yes ; no)

open import AltArtemov.Variable.Representation.Core


_≟ⁱ_ : ∀ {g} → (i i′ : ◌∈ g) → Dec (i ≡ i′)
top   ≟ⁱ top    = yes refl
top   ≟ⁱ pop _  = no λ ()
pop _ ≟ⁱ top    = no λ ()
pop i ≟ⁱ pop i′ with i ≟ⁱ i′
pop i ≟ⁱ pop .i | yes refl = yes refl
...             | no  i≢i′ = no (i≢i′ ∘ inv-pop)
