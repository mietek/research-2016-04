module Examples.Isomorphism where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import AltArtemov
open import Examples.AltArtemov


_⇑≡_ : ∀ {A} (d : ∅ ⊢ A) (d′ : ∅ ⊢ rep d ∶ A) → Set
d ⇑≡ d′ = nec d ≡ d′

_⇓≡_ : ∀ {A} (d : ∅ ⊢ A) {HA : HighTy A} {Hd : HighDn d {HA}} (d′ : ∅ ⊢ lower′ A {HA}) → Set
_⇓≡_ d {HA} {Ud} d′ = unnec′ d {HA} {Ud} ≡ d′


-- Demonstration of the isomorphism between propositional logic and the
-- λ-calculus.

I⇑≡I² : ∀ {A} → I {A} ⇑≡ I²
I⇑≡I² = refl

K⇑≡K² : ∀ {A B} → K {A} {B} ⇑≡ K²
K⇑≡K² = refl

S⇑≡S² : ∀ {A B C} → S {A} {B} {C} ⇑≡ S²
S⇑≡S² = refl

I²⇓≡I : ∀ {A} → I² {A} ⇓≡ I
I²⇓≡I = refl

K²⇓≡K : ∀ {A B} → K² {A} {B} ⇓≡ K
K²⇓≡K = refl

S²⇓≡S : ∀ {A B C} → S² {A} {B} {C} ⇓≡ S
S²⇓≡S = refl


-- Demonstration of the isomorphism between first- and second-level
-- realisations of theorems of the modal logic S4.

D⇑≡D² : ∀ {f x A B} → D {f} {x} {A} {B} ⇑≡ D²
D⇑≡D² = refl

T⇑≡T² : ∀ {x A} → T {x} {A} ⇑≡ T²
T⇑≡T² = refl

#4⇑≡#4² : ∀ {x A} → #4 {x} {A} ⇑≡ #4²
#4⇑≡#4² = refl

D²⇓≡D : ∀ {f x A B} → D² {f} {x} {A} {B} ⇓≡ D
D²⇓≡D = refl

T²⇓≡T : ∀ {x A} → T² {x} {A} ⇓≡ T
T²⇓≡T = refl

#4²⇓≡#4 : ∀ {x A} → #4² {x} {A} ⇓≡ #4
#4²⇓≡#4 = refl
