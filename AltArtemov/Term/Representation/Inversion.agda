module AltArtemov.Term.Representation.Inversion where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import AltArtemov.Context.Representation
open import AltArtemov.Term.Representation.Core
open import AltArtemov.Variable.Representation


inv-VAR-n : ∀ {g n n′} {i i′ : ◌∈ g} → _⊢◌.VAR[ n ] i ≡ VAR[ n′ ] i′ → n ≡ n′
inv-VAR-i : ∀ {g n n′} {i i′ : ◌∈ g} → _⊢◌.VAR[ n ] i ≡ VAR[ n′ ] i′ → i ≡ i′
inv-VAR-n refl = refl
inv-VAR-i refl = refl

inv-LAM-n : ∀ {g n n′} {t t′ : g ,◌ ⊢◌} → _⊢◌.LAM[ n ] t ≡ LAM[ n′ ] t′ → n ≡ n′
inv-LAM-t : ∀ {g n n′} {t t′ : g ,◌ ⊢◌} → _⊢◌.LAM[ n ] t ≡ LAM[ n′ ] t′ → t ≡ t′
inv-LAM-n refl = refl
inv-LAM-t refl = refl

inv-APP-n : ∀ {g n n′} {t t′ u u′ : g ⊢◌} → _⊢◌.APP[ n ] t u ≡ APP[ n′ ] t′ u′ → n ≡ n′
inv-APP-t : ∀ {g n n′} {t t′ u u′ : g ⊢◌} → _⊢◌.APP[ n ] t u ≡ APP[ n′ ] t′ u′ → t ≡ t′
inv-APP-u : ∀ {g n n′} {t t′ u u′ : g ⊢◌} → _⊢◌.APP[ n ] t u ≡ APP[ n′ ] t′ u′ → u ≡ u′
inv-APP-n refl = refl
inv-APP-t refl = refl
inv-APP-u refl = refl

inv-PAIR-n : ∀ {g n n′} {t t′ u u′ : g ⊢◌} → _⊢◌.PAIR[ n ] t u ≡ PAIR[ n′ ] t′ u′ → n ≡ n′
inv-PAIR-t : ∀ {g n n′} {t t′ u u′ : g ⊢◌} → _⊢◌.PAIR[ n ] t u ≡ PAIR[ n′ ] t′ u′ → t ≡ t′
inv-PAIR-u : ∀ {g n n′} {t t′ u u′ : g ⊢◌} → _⊢◌.PAIR[ n ] t u ≡ PAIR[ n′ ] t′ u′ → u ≡ u′
inv-PAIR-n refl = refl
inv-PAIR-t refl = refl
inv-PAIR-u refl = refl

inv-FST-n : ∀ {g n n′} {t t′ : g ⊢◌} → _⊢◌.FST[ n ] t ≡ FST[ n′ ] t′ → n ≡ n′
inv-FST-t : ∀ {g n n′} {t t′ : g ⊢◌} → _⊢◌.FST[ n ] t ≡ FST[ n′ ] t′ → t ≡ t′
inv-FST-n refl = refl
inv-FST-t refl = refl

inv-SND-n : ∀ {g n n′} {t t′ : g ⊢◌} → _⊢◌.SND[ n ] t ≡ SND[ n′ ] t′ → n ≡ n′
inv-SND-t : ∀ {g n n′} {t t′ : g ⊢◌} → _⊢◌.SND[ n ] t ≡ SND[ n′ ] t′ → t ≡ t′
inv-SND-n refl = refl
inv-SND-t refl = refl

inv-UP-n : ∀ {g n n′} {t t′ : g ⊢◌} → _⊢◌.UP[ n ] t ≡ UP[ n′ ] t′ → n ≡ n′
inv-UP-t : ∀ {g n n′} {t t′ : g ⊢◌} → _⊢◌.UP[ n ] t ≡ UP[ n′ ] t′ → t ≡ t′
inv-UP-n refl = refl
inv-UP-t refl = refl

inv-DOWN-n : ∀ {g n n′} {t t′ : g ⊢◌} → _⊢◌.DOWN[ n ] t ≡ DOWN[ n′ ] t′ → n ≡ n′
inv-DOWN-t : ∀ {g n n′} {t t′ : g ⊢◌} → _⊢◌.DOWN[ n ] t ≡ DOWN[ n′ ] t′ → t ≡ t′
inv-DOWN-n refl = refl
inv-DOWN-t refl = refl

inv-BOOM-n : ∀ {g n n′} {t t′ : g ⊢◌} → _⊢◌.BOOM[ n ] t ≡ BOOM[ n′ ] t′ → n ≡ n′
inv-BOOM-t : ∀ {g n n′} {t t′ : g ⊢◌} → _⊢◌.BOOM[ n ] t ≡ BOOM[ n′ ] t′ → t ≡ t′
inv-BOOM-n refl = refl
inv-BOOM-t refl = refl

inv-! : ∀ {g} {t t′ : g ⊢◌} → _⊢◌.! t ≡ ! t′ → t ≡ t′
inv-! refl = refl
