module Examples.Shallow.AltArtemov where

open import Shallow.AltArtemov


-- Some theorems of propositional logic.

I : ∀ {A : Set} → A → A
I x = x

K : ∀ {A B : Set} → A → B → A
K x y = x

S : ∀ {A B C : Set} → (A → B → C) → (A → B) → A → C
S f g x = (f x) (g x)


-- Some theorems of the λ-calculus.

I² : ∀ {A : Set} → (A → A) ▷ I
I² = [ I ]

K² : ∀ {A B : Set} → (A → B → A) ▷ K
K² = [ K ]

S² : ∀ {A B C : Set} → ((A → B → C) → (A → B) → A → C) ▷ S
S² = [ S ]


-- Some theorems of third-level logic.

I³ : ∀ {A : Set} → (A → A) ▷ I ▷ [ I ]
I³ = [ [ I ] ]

K³ : ∀ {A B : Set} → (A → B → A) ▷ K ▷ [ K ]
K³ = [ [ K ] ]

S³ : ∀ {A B C : Set} → ((A → B → C) → (A → B) → A → C) ▷ S ▷ [ S ]
S³ = [ [ S ] ]


-- Some first-level realisations of theorems of the modal logic S4.

D : ∀ {A B : Set} {f : A → B} {x : A} → (A → B) ▷ f → A ▷ x → B ▷ f x
D [ f ] [ x ] = [ f x ]

T : ∀ {A : Set} {x : A} → A ▷ x → A
T [ t ] = t

#4 : ∀ {A : Set} {x : A} → A ▷ x → A ▷ x ▷ [ x ]
#4 [ x ] = [ [ x ] ]


-- Some second-level realisations of theorems of the modal logic S4.

D² : ∀ {A B : Set} {f : A → B} {x : A} → ((A → B) ▷ f → A ▷ x → B ▷ f x) ▷ D
D² = [ D ]

T² : ∀ {A : Set} {x : A} → (A ▷ x → A) ▷ T
T² = [ T ]

#4² : ∀ {A : Set} {x : A} → (A ▷ x → A ▷ x ▷ [ x ]) ▷ #4
#4² = [ #4 ]


-- Some third-level realisations of theorems of the modal logic S4.

D³ : ∀ {A B : Set} → {f : A → B} {x : A} → ((A → B) ▷ f → A ▷ x → B ▷ f x) ▷ D ▷ [ D ]
D³ = [ [ D ] ]

T³ : ∀ {A : Set} {x : A} → (A ▷ x → A) ▷ T ▷ [ T ]
T³ = [ [ T ] ]

#4³ : ∀ {A : Set} {x : A} → (A ▷ x → A ▷ x ▷ [ x ]) ▷ #4 ▷ [ #4 ]
#4³ = [ [ #4 ] ]
