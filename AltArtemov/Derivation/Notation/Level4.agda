module AltArtemov.Derivation.Notation.Level4 where

open import AltArtemov.Context
open import AltArtemov.Derivation.Core
open import AltArtemov.Term
open import AltArtemov.TermVector
open import AltArtemov.Type


var⁴ : ∀ {A Γ}
    → (i : Γ ∋ A)
    → Γ ⊢ VAR³ (ix i) ∶ VAR² (ix i) ∶ VAR (ix i) ∶ A
var⁴ i = var[ 3 ] i

lam⁴ : ∀ {t₃ t₂ t A B Γ}
    → Γ , A ⊢ t₃ ∶ t₂ ∶ t ∶ B
    → Γ ⊢ LAM³ t₃ ∶ LAM² t₂ ∶ LAM t ∶ (A ⊃ B)
lam⁴ {t₃} {t₂} {t} = lam[ 3 ] {ts = t₃ ∷ t₂ ∷ t ∷ []}

app⁴ : ∀ {t₃ t₂ t s₃ s₂ s A B Γ}
    → Γ ⊢ t₃ ∶ t₂ ∶ t ∶ (A ⊃ B)    → Γ ⊢ s₃ ∶ s₂ ∶ s ∶ A
    → Γ ⊢ APP³ t₃ s₃ ∶ APP² t₂ s₂ ∶ APP t s ∶ B
app⁴ {t₃} {t₂} {t} {s₃} {s₂} {s} = app[ 3 ] {ts = t₃ ∷ t₂ ∷ t ∷ []} {ss = s₃ ∷ s₂ ∷ s ∷ []}

up⁴ : ∀ {t₃ t₂ t u A Γ}
    → Γ ⊢ t₃ ∶ t₂ ∶ t ∶ u ∶ A
    → Γ ⊢ UP³ t₃ ∶ UP² t₂ ∶ UP t ∶ quo u ∶ u ∶ A
up⁴ {t₃} {t₂} {t} = up[ 3 ] {ts = t₃ ∷ t₂ ∷ t ∷ []}

down⁴ : ∀ {t₃ t₂ t u A Γ}
    → Γ ⊢ t₃ ∶ t₂ ∶ t ∶ u ∶ A
    → Γ ⊢ DOWN³ t₃ ∶ DOWN² t₂ ∶ DOWN t ∶ A
down⁴ {t₃} {t₂} {t} = down[ 3 ] {ts = t₃ ∷ t₂ ∷ t ∷ []}


v0⁴ : ∀ {Γ A} → Γ , A ⊢ V0³ ∶ V0² ∶ V0 ∶ A
v0⁴ = var⁴ ix0

v1⁴ : ∀ {Γ A B} → Γ , A , B ⊢ V1³ ∶ V1² ∶ V1 ∶ A
v1⁴ = var⁴ ix1

v2⁴ : ∀ {Γ A B C} → Γ , A , B , C ⊢ V2³ ∶ V2² ∶ V2 ∶ A
v2⁴ = var⁴ ix2

v3⁴ : ∀ {Γ A B C D} → Γ , A , B , C , D ⊢ V3³ ∶ V3² ∶ V3 ∶ A
v3⁴ = var⁴ ix3

v4⁴ : ∀ {Γ A B C D E} → Γ , A , B , C , D , E ⊢ V4³ ∶ V4² ∶ V4 ∶ A
v4⁴ = var⁴ ix4

v5⁴ : ∀ {Γ A B C D E F} → Γ , A , B , C , D , E , F ⊢ V5³ ∶ V5² ∶ V5 ∶ A
v5⁴ = var⁴ ix5

v6⁴ : ∀ {Γ A B C D E F G} → Γ , A , B , C , D , E , F , G ⊢ V6³ ∶ V6² ∶ V6 ∶ A
v6⁴ = var⁴ ix6

v7⁴ : ∀ {Γ A B C D E F G H} → Γ , A , B , C , D , E , F , G , H ⊢ V7³ ∶ V7² ∶ V7 ∶ A
v7⁴ = var⁴ ix7

v8⁴ : ∀ {Γ A B C D E F G H I} → Γ , A , B , C , D , E , F , G , H , I ⊢ V8³ ∶ V8² ∶ V8 ∶ A
v8⁴ = var⁴ ix8

v9⁴ : ∀ {Γ A B C D E F G H I J} → Γ , A , B , C , D , E , F , G , H , I , J ⊢ V9³ ∶ V9² ∶ V9 ∶ A
v9⁴ = var⁴ ix9
