module Try1.AltArtemov.Derivation.Notation.Level3 where

open import Try1.AltArtemov.Context
open import Try1.AltArtemov.Derivation.Core
open import Try1.AltArtemov.Term
open import Try1.AltArtemov.TermVector
open import Try1.AltArtemov.Type


var³ : ∀ {A Γ}
    → (i : Γ ∋ A)
    → Γ ⊢ VAR² (ix i) ∶ VAR (ix i) ∶ A
var³ i = var[ 2 ] i

lam³ : ∀ {t₂ t A B Γ}
    → Γ , A ⊢ t₂ ∶ t ∶ B
    → Γ ⊢ LAM² t₂ ∶ LAM t ∶ (A ⊃ B)
lam³ {t₂} {t} = lam[ 2 ] {ts = t₂ ∷ t ∷ []}

app³ : ∀ {t₂ t s₂ s A B Γ}
    → Γ ⊢ t₂ ∶ t ∶ (A ⊃ B)    → Γ ⊢ s₂ ∶ s ∶ A
    → Γ ⊢ APP² t₂ s₂ ∶ APP t s ∶ B
app³ {t₂} {t} {s₂} {s} = app[ 2 ] {ts = t₂ ∷ t ∷ []} {ss = s₂ ∷ s ∷ []}

pair³ : ∀ {t₂ t s₂ s A B Γ}
    → Γ ⊢ t₂ ∶ t ∶ A    → Γ ⊢ s₂ ∶ s ∶ B
    → Γ ⊢ PAIR² t₂ s₂ ∶ PAIR t s ∶ (A ∧ B)
pair³ {t₂} {t} {s₂} {s} = pair[ 2 ] {ts = t₂ ∷ t ∷ []} {ss = s₂ ∷ s ∷ []}

fst³ : ∀ {t₂ t A B Γ}
    → Γ ⊢ t₂ ∶ t ∶ (A ∧ B)
    → Γ ⊢ FST² t₂ ∶ FST t ∶ A
fst³ {t₂} {t} = fst[ 2 ] {ts = t₂ ∷ t ∷ []}

snd³ : ∀ {t₂ t A B Γ}
    → Γ ⊢ t₂ ∶ t ∶ (A ∧ B)
    → Γ ⊢ SND² t₂ ∶ SND t ∶ B
snd³ {t₂} {t} = snd[ 2 ] {ts = t₂ ∷ t ∷ []}

up³ : ∀ {t₂ t u A Γ}
    → Γ ⊢ t₂ ∶ t ∶ u ∶ A
    → Γ ⊢ UP² t₂ ∶ UP t ∶ quo u ∶ u ∶ A
up³ {t₂} {t} = up[ 2 ] {ts = t₂ ∷ t ∷ []}

down³ : ∀ {t₂ t u A Γ}
    → Γ ⊢ t₂ ∶ t ∶ u ∶ A
    → Γ ⊢ DOWN² t₂ ∶ DOWN t ∶ A
down³ {t₂} {t} = down[ 2 ] {ts = t₂ ∷ t ∷ []}

boom³ : ∀ {t₂ t A Γ}
    → Γ ⊢ t₂ ∶ t ∶ ⊥
    → Γ ⊢ BOOM² t₂ ∶ BOOM t ∶ A
boom³ {t₂} {t} = boom[ 2 ] {ts = t₂ ∷ t ∷ []}

eq³ : ∀ {t₂ t s₂ s u A B Γ}
    → Γ ⊢ t₂ ∶ t ∶ u ∶ A    → Γ ⊢ s₂ ∶ s ∶ u ∶ B
    → Γ ⊢ EQ² t₂ s₂ ∶ EQ t s ∶ (A ≑ B)
eq³ {t₂} {t} {s₂} {s} = eq[ 2 ] {ts = t₂ ∷ t ∷ []} {ss = s₂ ∷ s ∷ []}


v0³ : ∀ {Γ A} → Γ , A ⊢ V0² ∶ V0 ∶ A
v0³ = var³ ix0

v1³ : ∀ {Γ A B} → Γ , A , B ⊢ V1² ∶ V1 ∶ A
v1³ = var³ ix1

v2³ : ∀ {Γ A B C} → Γ , A , B , C ⊢ V2² ∶ V2 ∶ A
v2³ = var³ ix2

v3³ : ∀ {Γ A B C D} → Γ , A , B , C , D ⊢ V3² ∶ V3 ∶ A
v3³ = var³ ix3

v4³ : ∀ {Γ A B C D E} → Γ , A , B , C , D , E ⊢ V4² ∶ V4 ∶ A
v4³ = var³ ix4

v5³ : ∀ {Γ A B C D E F} → Γ , A , B , C , D , E , F ⊢ V5² ∶ V5 ∶ A
v5³ = var³ ix5

v6³ : ∀ {Γ A B C D E F G} → Γ , A , B , C , D , E , F , G ⊢ V6² ∶ V6 ∶ A
v6³ = var³ ix6

v7³ : ∀ {Γ A B C D E F G H} → Γ , A , B , C , D , E , F , G , H ⊢ V7² ∶ V7 ∶ A
v7³ = var³ ix7

v8³ : ∀ {Γ A B C D E F G H I} → Γ , A , B , C , D , E , F , G , H , I ⊢ V8² ∶ V8 ∶ A
v8³ = var³ ix8

v9³ : ∀ {Γ A B C D E F G H I J} → Γ , A , B , C , D , E , F , G , H , I , J ⊢ V9² ∶ V9 ∶ A
v9³ = var³ ix9
