module AltArtemov.Derivation.Notation.Level3 where

open import AltArtemov.Context
open import AltArtemov.Derivation.Core
open import AltArtemov.Term
open import AltArtemov.TermVector
open import AltArtemov.Type


VAR³ : ∀ {A Γ}
    → (d : Γ ∋ A)
    → Γ ⊢ var² (ix d) ∶ var (ix d) ∶ A
VAR³ i = VAR[ 2 ] i

LAM³ : ∀ {t₂ t A B Γ}
    → Γ , A ⊢ t₂ ∶ t ∶ B
    → Γ ⊢ lam² t₂ ∶ lam t ∶ (A ⊃ B)
LAM³ {t₂} {t} = LAM[ 2 ] {ts = t₂ ∷ t ∷ []}

APP³ : ∀ {t₂ t s₂ s A B Γ}
    → Γ ⊢ t₂ ∶ t ∶ (A ⊃ B)    → Γ ⊢ s₂ ∶ s ∶ A
    → Γ ⊢ app² t₂ s₂ ∶ app t s ∶ B
APP³ {t₂} {t} {s₂} {s} = APP[ 2 ] {ts = t₂ ∷ t ∷ []} {ss = s₂ ∷ s ∷ []}

UP³ : ∀ {t₂ t u A Γ}
    → Γ ⊢ t₂ ∶ t ∶ u ∶ A
    → Γ ⊢ up² t₂ ∶ up t ∶ quo u ∶ u ∶ A
UP³ {t₂} {t} = UP[ 2 ] {ts = t₂ ∷ t ∷ []}

DOWN³ : ∀ {t₂ t u A Γ}
    → Γ ⊢ t₂ ∶ t ∶ u ∶ A
    → Γ ⊢ down² t₂ ∶ down t ∶ A
DOWN³ {t₂} {t} = DOWN[ 2 ] {ts = t₂ ∷ t ∷ []}


V0³ : ∀ {Γ A} → Γ , A ⊢ v0² ∶ v0 ∶ A
V0³ = VAR³ IX0

V1³ : ∀ {Γ A B} → Γ , A , B ⊢ v1² ∶ v1 ∶ A
V1³ = VAR³ IX1

V2³ : ∀ {Γ A B C} → Γ , A , B , C ⊢ v2² ∶ v2 ∶ A
V2³ = VAR³ IX2

V3³ : ∀ {Γ A B C D} → Γ , A , B , C , D ⊢ v3² ∶ v3 ∶ A
V3³ = VAR³ IX3

V4³ : ∀ {Γ A B C D E} → Γ , A , B , C , D , E ⊢ v4² ∶ v4 ∶ A
V4³ = VAR³ IX4

V5³ : ∀ {Γ A B C D E F} → Γ , A , B , C , D , E , F ⊢ v5² ∶ v5 ∶ A
V5³ = VAR³ IX5

V6³ : ∀ {Γ A B C D E F G} → Γ , A , B , C , D , E , F , G ⊢ v6² ∶ v6 ∶ A
V6³ = VAR³ IX6

V7³ : ∀ {Γ A B C D E F G H} → Γ , A , B , C , D , E , F , G , H ⊢ v7² ∶ v7 ∶ A
V7³ = VAR³ IX7

V8³ : ∀ {Γ A B C D E F G H I} → Γ , A , B , C , D , E , F , G , H , I ⊢ v8² ∶ v8 ∶ A
V8³ = VAR³ IX8

V9³ : ∀ {Γ A B C D E F G H I J} → Γ , A , B , C , D , E , F , G , H , I , J ⊢ v9² ∶ v9 ∶ A
V9³ = VAR³ IX9
