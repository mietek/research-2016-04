module AltArtemov.Derivation.Notation.Level4 where

open import AltArtemov.Context
open import AltArtemov.Derivation.Core
open import AltArtemov.Term
open import AltArtemov.TermVector
open import AltArtemov.Type


VAR⁴ : ∀ {A Γ}
    → (d : Γ ∋ A)
    → Γ ⊢ var³ (ix d) ∶ var² (ix d) ∶ var (ix d) ∶ A
VAR⁴ i = VAR[ 3 ] i

LAM⁴ : ∀ {t₃ t₂ t A B Γ}
    → Γ , A ⊢ t₃ ∶ t₂ ∶ t ∶ B
    → Γ ⊢ lam³ t₃ ∶ lam² t₂ ∶ lam t ∶ (A ⊃ B)
LAM⁴ {t₃} {t₂} {t} = LAM[ 3 ] {ts = t₃ ∷ t₂ ∷ t ∷ []}

APP⁴ : ∀ {t₃ t₂ t s₃ s₂ s A B Γ}
    → Γ ⊢ t₃ ∶ t₂ ∶ t ∶ (A ⊃ B)    → Γ ⊢ s₃ ∶ s₂ ∶ s ∶ A
    → Γ ⊢ app³ t₃ s₃ ∶ app² t₂ s₂ ∶ app t s ∶ B
APP⁴ {t₃} {t₂} {t} {s₃} {s₂} {s} = APP[ 3 ] {ts = t₃ ∷ t₂ ∷ t ∷ []} {ss = s₃ ∷ s₂ ∷ s ∷ []}

UP⁴ : ∀ {t₃ t₂ t u A Γ}
    → Γ ⊢ t₃ ∶ t₂ ∶ t ∶ u ∶ A
    → Γ ⊢ up³ t₃ ∶ up² t₂ ∶ up t ∶ quo u ∶ u ∶ A
UP⁴ {t₃} {t₂} {t} = UP[ 3 ] {ts = t₃ ∷ t₂ ∷ t ∷ []}

DOWN⁴ : ∀ {t₃ t₂ t u A Γ}
    → Γ ⊢ t₃ ∶ t₂ ∶ t ∶ u ∶ A
    → Γ ⊢ down³ t₃ ∶ down² t₂ ∶ down t ∶ A
DOWN⁴ {t₃} {t₂} {t} = DOWN[ 3 ] {ts = t₃ ∷ t₂ ∷ t ∷ []}


V0⁴ : ∀ {Γ A} → Γ , A ⊢ v0³ ∶ v0² ∶ v0 ∶ A
V0⁴ = VAR⁴ IX0

V1⁴ : ∀ {Γ A B} → Γ , A , B ⊢ v1³ ∶ v1² ∶ v1 ∶ A
V1⁴ = VAR⁴ IX1

V2⁴ : ∀ {Γ A B C} → Γ , A , B , C ⊢ v2³ ∶ v2² ∶ v2 ∶ A
V2⁴ = VAR⁴ IX2

V3⁴ : ∀ {Γ A B C D} → Γ , A , B , C , D ⊢ v3³ ∶ v3² ∶ v3 ∶ A
V3⁴ = VAR⁴ IX3

V4⁴ : ∀ {Γ A B C D E} → Γ , A , B , C , D , E ⊢ v4³ ∶ v4² ∶ v4 ∶ A
V4⁴ = VAR⁴ IX4

V5⁴ : ∀ {Γ A B C D E F} → Γ , A , B , C , D , E , F ⊢ v5³ ∶ v5² ∶ v5 ∶ A
V5⁴ = VAR⁴ IX5

V6⁴ : ∀ {Γ A B C D E F G} → Γ , A , B , C , D , E , F , G ⊢ v6³ ∶ v6² ∶ v6 ∶ A
V6⁴ = VAR⁴ IX6

V7⁴ : ∀ {Γ A B C D E F G H} → Γ , A , B , C , D , E , F , G , H ⊢ v7³ ∶ v7² ∶ v7 ∶ A
V7⁴ = VAR⁴ IX7

V8⁴ : ∀ {Γ A B C D E F G H I} → Γ , A , B , C , D , E , F , G , H , I ⊢ v8³ ∶ v8² ∶ v8 ∶ A
V8⁴ = VAR⁴ IX8

V9⁴ : ∀ {Γ A B C D E F G H I J} → Γ , A , B , C , D , E , F , G , H , I , J ⊢ v9³ ∶ v9² ∶ v9 ∶ A
V9⁴ = VAR⁴ IX9
