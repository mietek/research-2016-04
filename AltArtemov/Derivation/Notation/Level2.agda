module AltArtemov.Derivation.Notation.Level2 where

open import AltArtemov.Context
open import AltArtemov.Derivation.Core
open import AltArtemov.Term
open import AltArtemov.TermVector
open import AltArtemov.Type


var² : ∀ {A Γ}
    → (i : Γ ∋ A)
    → Γ ⊢ VAR (ix i) ∶ A
var² i = var[ 1 ] i

lam² : ∀ {t A B Γ}
    → Γ , A ⊢ t ∶ B
    → Γ ⊢ LAM t ∶ (A ⊃ B)
lam² {t} = lam[ 1 ] {ts = t ∷ []}

app² : ∀ {t s A B Γ}
    → Γ ⊢ t ∶ (A ⊃ B)    → Γ ⊢ s ∶ A
    → Γ ⊢ APP t s ∶ B
app² {t} {s} =  app[ 1 ] {ts = t ∷ []} {ss = s ∷ []}

pair² : ∀ {t s A B Γ}
    → Γ ⊢ t ∶ A    → Γ ⊢ s ∶ B
    → Γ ⊢ PAIR t s ∶ (A ∧ B)
pair² {t} {s} =  pair[ 1 ] {ts = t ∷ []} {ss = s ∷ []}

fst² : ∀ {t A B Γ}
    → Γ ⊢ t ∶ (A ∧ B)
    → Γ ⊢ FST t ∶ A
fst² {t} =  fst[ 1 ] {ts = t ∷ []}

snd² : ∀ {t A B Γ}
    → Γ ⊢ t ∶ (A ∧ B)
    → Γ ⊢ SND t ∶ B
snd² {t} =  snd[ 1 ] {ts = t ∷ []}

up² : ∀ {t u A Γ}
    → Γ ⊢ t ∶ u ∶ A
    → Γ ⊢ UP t ∶ quo u ∶ u ∶ A
up² {t} = up[ 1 ] {ts = t ∷ []}

down² : ∀ {t u A Γ}
    → Γ ⊢ t ∶ u ∶ A
    → Γ ⊢ DOWN t ∶ A
down² {t} = down[ 1 ] {ts = t ∷ []}

boom² : ∀ {t A Γ}
    → Γ ⊢ t ∶ ⊥
    → Γ ⊢ BOOM t ∶ A
boom² {t} = boom[ 1 ] {ts = t ∷ []}


v0² : ∀ {Γ A} → Γ , A ⊢ V0 ∶ A
v0² = var² ix0

v1² : ∀ {Γ A B} → Γ , A , B ⊢ V1 ∶ A
v1² = var² ix1

v2² : ∀ {Γ A B C} → Γ , A , B , C ⊢ V2 ∶ A
v2² = var² ix2

v3² : ∀ {Γ A B C D} → Γ , A , B , C , D ⊢ V3 ∶ A
v3² = var² ix3

v4² : ∀ {Γ A B C D E} → Γ , A , B , C , D , E ⊢ V4 ∶ A
v4² = var² ix4

v5² : ∀ {Γ A B C D E F} → Γ , A , B , C , D , E , F ⊢ V5 ∶ A
v5² = var² ix5

v6² : ∀ {Γ A B C D E F G} → Γ , A , B , C , D , E , F , G ⊢ V6 ∶ A
v6² = var² ix6

v7² : ∀ {Γ A B C D E F G H} → Γ , A , B , C , D , E , F , G , H ⊢ V7 ∶ A
v7² = var² ix7

v8² : ∀ {Γ A B C D E F G H I} → Γ , A , B , C , D , E , F , G , H , I ⊢ V8 ∶ A
v8² = var² ix8

v9² : ∀ {Γ A B C D E F G H I J} → Γ , A , B , C , D , E , F , G , H , I , J ⊢ V9 ∶ A
v9² = var² ix9
