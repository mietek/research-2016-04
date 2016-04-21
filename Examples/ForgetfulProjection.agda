module Examples.ForgetfulProjection where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import AltArtemov
open import Examples.AltArtemov
open import S4 using (_∙_⊢_)
import Examples.S4 as S4


°[_] : ∀ A → S4.Ty
°[ ⊥ ]    = S4.⊥
°[ A ⊃ B ] = °[ A ] S4.⊃ °[ B ]
°[ t ∶ A ] = S4.□ °[ A ]

_°≡_ : ∀ {{Γ Δ′ Γ′}} {A A′} (d : Γ ⊢ A) (d′ : Δ′ ∙ Γ′ ⊢ A′) → Set
d °≡ d′ = °[ ty d ] ≡ S4.ty d′


-- Forgetful projection of some theorems of propositional logic.

I°≡I : ∀ {A} → I {A} °≡ S4.I
I°≡I = refl

K°≡K : ∀ {A B} → K {A} {B} °≡ S4.K
K°≡K = refl

S°≡S : ∀ {A B C} → S {A} {B} {C} °≡ S4.S
S°≡S = refl


-- Forgetful projection of some theorems of the λ-calculus.

I²°≡□I : ∀ {A} → I² {A} °≡ S4.□I
I²°≡□I = refl

K²°≡□K : ∀ {A B} → K² {A} {B} °≡ S4.□K
K²°≡□K = refl

S²°≡□S : ∀ {A B C} → S² {A} {B} {C} °≡ S4.□S
S²°≡□S = refl


-- Forgetful projection of some theorems of third-level logic.

I³°≡□□I : ∀ {A} → I³ {A} °≡ S4.□□I
I³°≡□□I = refl

K³°≡□□K : ∀ {A B} → K³ {A} {B} °≡ S4.□□K
K³°≡□□K = refl

S³°≡□□S : ∀ {A B C} → S³ {A} {B} {C} °≡ S4.□□S
S³°≡□□S = refl


-- Forgetful projection of some first-level realisations of theorems of the
-- modal logic S4.

D°≡D : ∀ {f x A B} → D {f} {x} {A} {B} °≡ S4.D
D°≡D = refl

T°≡T : ∀ {x A} → T {x} {A} °≡ S4.T
T°≡T = refl

#4°≡#4 : ∀ {x A} → #4 {x} {A} °≡ S4.#4
#4°≡#4 = refl


-- Forgetful projection of some second-level realisations of theorems of the
-- modal logic S4.

D²°≡□D : ∀ {f x A B} → D² {f} {x} {A} {B} °≡ S4.□D
D²°≡□D = refl

T²°≡□T : ∀ {x A} → T² {x} {A} °≡ S4.□T
T²°≡□T = refl

#4²°≡□#T : ∀ {x A} → #4² {x} {A} °≡ S4.□#4
#4²°≡□#T = refl


-- Forgetful projection of some third-level realisations of theorems of the
-- modal logic S4.

D³°≡□□D : ∀ {f x A B} → D³ {f} {x} {A} {B} °≡ S4.□□D
D³°≡□□D = refl

T³°≡□□T : ∀ {x A} → T³ {x} {A} °≡ S4.□□T
T³°≡□□T = refl

#4³°≡□□#T : ∀ {x A} → #4³ {x} {A} °≡ S4.□□#4
#4³°≡□□#T = refl
