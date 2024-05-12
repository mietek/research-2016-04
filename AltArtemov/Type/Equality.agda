module Try2.AltArtemov.Type.Equality where

open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Nullary using (Dec ; yes ; no)

open import Try2.AltArtemov.Term.Representation
open import Try2.AltArtemov.Type.Core
open import Try2.AltArtemov.Type.Inversion


_≟ᴬ_ : ∀ {g} → (A A′ : Ty g) → Dec (A ≡ A′)

★       ≟ᴬ ★         = yes refl
★       ≟ᴬ (_ ∶ _)   = no λ ()
★       ≟ᴬ (_ ⊃ _)   = no λ ()
★       ≟ᴬ (_ ∧ _)   = no λ ()
★       ≟ᴬ ⊥        = no λ ()

(_ ∶ _) ≟ᴬ ★         = no λ ()
(t ∶ A) ≟ᴬ (t′ ∶ A′) with t ≟ᵗ t′ | A ≟ᴬ A′
(t ∶ A) ≟ᴬ (.t ∶ .A) | yes refl | yes refl = yes refl
...                  | no  t≢t′ | _        = no (t≢t′ ∘ inv-∶-t)
...                  | _        | no  A≢A′ = no (A≢A′ ∘ inv-∶-A)
(_ ∶ _) ≟ᴬ (_ ⊃ _)   = no λ ()
(_ ∶ _) ≟ᴬ (_ ∧ _)   = no λ ()
(_ ∶ _) ≟ᴬ ⊥        = no λ ()

(_ ⊃ _) ≟ᴬ ★         = no λ ()
(_ ⊃ _) ≟ᴬ (_ ∶ _)   = no λ ()
(A ⊃ B) ≟ᴬ (A′ ⊃ B′) with A ≟ᴬ A′ | B ≟ᴬ B′
(A ⊃ B) ≟ᴬ (.A ⊃ .B) | yes refl | yes refl = yes refl
...                  | no  A≢A′ | _        = no (A≢A′ ∘ inv-⊃-A)
...                  | _        | no  B≢B′ = no (B≢B′ ∘ inv-⊃-B)
(_ ⊃ _) ≟ᴬ (_ ∧ _)   = no λ ()
(_ ⊃ _) ≟ᴬ ⊥        = no λ ()

(_ ∧ _) ≟ᴬ ★         = no λ ()
(_ ∧ _) ≟ᴬ (_ ∶ _)   = no λ ()
(_ ∧ _) ≟ᴬ (_ ⊃ _)   = no λ ()
(A ∧ B) ≟ᴬ (A′ ∧ B′) with A ≟ᴬ A′ | B ≟ᴬ B′
(A ∧ B) ≟ᴬ (.A ∧ .B) | yes refl | yes refl = yes refl
...                  | no  A≢A′ | _        = no (A≢A′ ∘ inv-∧-A)
...                  | _        | no  B≢B′ = no (B≢B′ ∘ inv-∧-B)
(_ ∧ _) ≟ᴬ ⊥        = no λ ()

⊥      ≟ᴬ ★         = no λ ()
⊥      ≟ᴬ (_ ∶ _)   = no λ ()
⊥      ≟ᴬ (_ ⊃ _)   = no λ ()
⊥      ≟ᴬ (_ ∧ _)   = no λ ()
⊥      ≟ᴬ ⊥        = yes refl
