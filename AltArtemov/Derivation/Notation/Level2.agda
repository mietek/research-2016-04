module AltArtemov.Derivation.Notation.Level2 where

open import AltArtemov.Context
open import AltArtemov.Derivation.Core
open import AltArtemov.Term
open import AltArtemov.TermVector
open import AltArtemov.Type


VAR²_ : ∀ {A Γ}
    → (d : Γ ∋ A)
    → Γ ⊢ var (ix d) ∶ A
VAR² i = VAR[ 1 ] i

LAM²_ : ∀ {t A B Γ}
    → Γ , A ⊢ t ∶ B
    → Γ ⊢ lam t ∶ (A ⊃ B)
LAM²_ {t} = LAM[ 1 ] {ts = t ∷ []}

APP² : ∀ {t s A B Γ}
    → Γ ⊢ t ∶ (A ⊃ B)    → Γ ⊢ s ∶ A
    → Γ ⊢ app t s ∶ B
APP² {t} {s} =  APP[ 1 ] {ts = t ∷ []} {ss = s ∷ []}

UP²_ : ∀ {t u A Γ}
    → Γ ⊢ t ∶ u ∶ A
    → Γ ⊢ up t ∶ quo u ∶ u ∶ A
UP²_ {t} = UP[ 1 ] {ts = t ∷ []}

DOWN²_ : ∀ {t u A Γ}
    → Γ ⊢ t ∶ u ∶ A
    → Γ ⊢ down t ∶ A
DOWN²_ {t} = DOWN[ 1 ] {ts = t ∷ []}


V0² : ∀ {Γ A} → Γ , A ⊢ var _ ∶ A
V0² = VAR² IX0

V1² : ∀ {Γ A B} → Γ , A , B ⊢ var _ ∶ A
V1² = VAR² IX1

V2² : ∀ {Γ A B C} → Γ , A , B , C ⊢ var _ ∶ A
V2² = VAR² IX2

V3² : ∀ {Γ A B C D} → Γ , A , B , C , D ⊢ var _ ∶ A
V3² = VAR² IX3

V4² : ∀ {Γ A B C D E} → Γ , A , B , C , D , E ⊢ var _ ∶ A
V4² = VAR² IX4

V5² : ∀ {Γ A B C D E F} → Γ , A , B , C , D , E , F ⊢ var _ ∶ A
V5² = VAR² IX5

V6² : ∀ {Γ A B C D E F G} → Γ , A , B , C , D , E , F , G ⊢ var _ ∶ A
V6² = VAR² IX6

V7² : ∀ {Γ A B C D E F G H} → Γ , A , B , C , D , E , F , G , H ⊢ var _ ∶ A
V7² = VAR² IX7

V8² : ∀ {Γ A B C D E F G H I} → Γ , A , B , C , D , E , F , G , H , I ⊢ var _ ∶ A
V8² = VAR² IX8

V9² : ∀ {Γ A B C D E F G H I J} → Γ , A , B , C , D , E , F , G , H , I , J ⊢ var _ ∶ A
V9² = VAR² IX9
