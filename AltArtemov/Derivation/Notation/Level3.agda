module AltArtemov.Derivation.Notation.Level3 where

open import AltArtemov.Context
open import AltArtemov.Derivation.Core
open import AltArtemov.Term
open import AltArtemov.TermVector
open import AltArtemov.Type


VAR³_ : ∀ {A Γ}
    → (d : Γ ∋ A)
    → Γ ⊢ var² (ix d) ∶ var (ix d) ∶ A
VAR³ i = VAR[ 2 ] i

LAM³_ : ∀ {t₂ t A B Γ}
    → Γ , A ⊢ t₂ ∶ t ∶ B
    → Γ ⊢ lam² t₂ ∶ lam t ∶ (A ⊃ B)
LAM³_ {t₂} {t} = LAM[ 2 ] {ts = t₂ ∷ t ∷ []}

APP³ : ∀ {t₂ t s₂ s A B Γ}
    → Γ ⊢ t₂ ∶ t ∶ (A ⊃ B)    → Γ ⊢ s₂ ∶ s ∶ A
    → Γ ⊢ app² t₂ s₂ ∶ app t s ∶ B
APP³ {t₂} {t} {s₂} {s} = APP[ 2 ] {ts = t₂ ∷ t ∷ []} {ss = s₂ ∷ s ∷ []}

UP³_ : ∀ {t₂ t u A Γ}
    → Γ ⊢ t₂ ∶ t ∶ u ∶ A
    → Γ ⊢ up² t₂ ∶ up t ∶ quo u ∶ u ∶ A
UP³_ {t₂} {t} = UP[ 2 ] {ts = t₂ ∷ t ∷ []}

DOWN³_ : ∀ {t₂ t u A Γ}
    → Γ ⊢ t₂ ∶ t ∶ u ∶ A
    → Γ ⊢ down² t₂ ∶ down t ∶ A
DOWN³_ {t₂} {t} = DOWN[ 2 ] {ts = t₂ ∷ t ∷ []}


V0³ : ∀ {Γ A} → Γ , A ⊢ var² _ ∶ var _ ∶ A
V0³ = VAR³ IX0

V1³ : ∀ {Γ A B} → Γ , A , B ⊢ var² _ ∶ var _ ∶ A
V1³ = VAR³ IX1

V2³ : ∀ {Γ A B C} → Γ , A , B , C ⊢ var² _ ∶ var _ ∶ A
V2³ = VAR³ IX2

V3³ : ∀ {Γ A B C D} → Γ , A , B , C , D ⊢ var² _ ∶ var _ ∶ A
V3³ = VAR³ IX3

V4³ : ∀ {Γ A B C D E} → Γ , A , B , C , D , E ⊢ var² _ ∶ var _ ∶ A
V4³ = VAR³ IX4

V5³ : ∀ {Γ A B C D E F} → Γ , A , B , C , D , E , F ⊢ var² _ ∶ var _ ∶ A
V5³ = VAR³ IX5

V6³ : ∀ {Γ A B C D E F G} → Γ , A , B , C , D , E , F , G ⊢ var² _ ∶ var _ ∶ A
V6³ = VAR³ IX6

V7³ : ∀ {Γ A B C D E F G H} → Γ , A , B , C , D , E , F , G , H ⊢ var² _ ∶ var _ ∶ A
V7³ = VAR³ IX7

V8³ : ∀ {Γ A B C D E F G H I} → Γ , A , B , C , D , E , F , G , H , I ⊢ var² _ ∶ var _ ∶ A
V8³ = VAR³ IX8

V9³ : ∀ {Γ A B C D E F G H I J} → Γ , A , B , C , D , E , F , G , H , I , J ⊢ var² _ ∶ var _ ∶ A
V9³ = VAR³ IX9
