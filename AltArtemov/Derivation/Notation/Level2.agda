module AltArtemov.Derivation.Notation.Level2 where

open import AltArtemov.Context
open import AltArtemov.Derivation.Core
open import AltArtemov.Term
open import AltArtemov.TermVector
open import AltArtemov.Type


VAR² : ∀ {A Γ}
    → (d : Γ ∋ A)
    → Γ ⊢ var (ix d) ∶ A
VAR² i = VAR[ 1 ] i

LAM² : ∀ {t A B Γ}
    → Γ , A ⊢ t ∶ B
    → Γ ⊢ lam t ∶ (A ⊃ B)
LAM² {t} = LAM[ 1 ] {ts = t ∷ []}

APP² : ∀ {t s A B Γ}
    → Γ ⊢ t ∶ (A ⊃ B)    → Γ ⊢ s ∶ A
    → Γ ⊢ app t s ∶ B
APP² {t} {s} =  APP[ 1 ] {ts = t ∷ []} {ss = s ∷ []}

UP² : ∀ {t u A Γ}
    → Γ ⊢ t ∶ u ∶ A
    → Γ ⊢ up t ∶ quo u ∶ u ∶ A
UP² {t} = UP[ 1 ] {ts = t ∷ []}

DOWN² : ∀ {t u A Γ}
    → Γ ⊢ t ∶ u ∶ A
    → Γ ⊢ down t ∶ A
DOWN² {t} = DOWN[ 1 ] {ts = t ∷ []}


V0² : ∀ {Γ A} → Γ , A ⊢ v0 ∶ A
V0² = VAR² IX0

V1² : ∀ {Γ A B} → Γ , A , B ⊢ v1 ∶ A
V1² = VAR² IX1

V2² : ∀ {Γ A B C} → Γ , A , B , C ⊢ v2 ∶ A
V2² = VAR² IX2

V3² : ∀ {Γ A B C D} → Γ , A , B , C , D ⊢ v3 ∶ A
V3² = VAR² IX3

V4² : ∀ {Γ A B C D E} → Γ , A , B , C , D , E ⊢ v4 ∶ A
V4² = VAR² IX4

V5² : ∀ {Γ A B C D E F} → Γ , A , B , C , D , E , F ⊢ v5 ∶ A
V5² = VAR² IX5

V6² : ∀ {Γ A B C D E F G} → Γ , A , B , C , D , E , F , G ⊢ v6 ∶ A
V6² = VAR² IX6

V7² : ∀ {Γ A B C D E F G H} → Γ , A , B , C , D , E , F , G , H ⊢ v7 ∶ A
V7² = VAR² IX7

V8² : ∀ {Γ A B C D E F G H I} → Γ , A , B , C , D , E , F , G , H , I ⊢ v8 ∶ A
V8² = VAR² IX8

V9² : ∀ {Γ A B C D E F G H I J} → Γ , A , B , C , D , E , F , G , H , I , J ⊢ v9 ∶ A
V9² = VAR² IX9
