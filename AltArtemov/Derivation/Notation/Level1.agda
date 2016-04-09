module AltArtemov.Derivation.Notation.Level1 where

open import AltArtemov.Context
open import AltArtemov.Derivation.Core
open import AltArtemov.TermVector
open import AltArtemov.Type


VAR_ : ∀ {A Γ}
    → Γ ∋ A
    → Γ ⊢ A
VAR i = VAR[ 0 ] i

LAM_ : ∀ {A B Γ}
    → Γ , A ⊢ B
    → Γ ⊢ A ⊃ B
LAM_ = LAM[ 0 ] {ts = []}

APP : ∀ {A B Γ}
    → Γ ⊢ A ⊃ B    → Γ ⊢ A
    → Γ ⊢ B
APP = APP[ 0 ] {ts = []} {ss = []}


V0 : ∀ {Γ A} → Γ , A ⊢ A
V0 = VAR IX0

V1 : ∀ {Γ A B} → Γ , A , B ⊢ A
V1 = VAR IX1

V2 : ∀ {Γ A B C} → Γ , A , B , C ⊢ A
V2 = VAR IX2

V3 : ∀ {Γ A B C D} → Γ , A , B , C , D ⊢ A
V3 = VAR IX3

V4 : ∀ {Γ A B C D E} → Γ , A , B , C , D , E ⊢ A
V4 = VAR IX4

V5 : ∀ {Γ A B C D E F} → Γ , A , B , C , D , E , F ⊢ A
V5 = VAR IX5

V6 : ∀ {Γ A B C D E F G} → Γ , A , B , C , D , E , F , G ⊢ A
V6 = VAR IX6

V7 : ∀ {Γ A B C D E F G H} → Γ , A , B , C , D , E , F , G , H ⊢ A
V7 = VAR IX7

V8 : ∀ {Γ A B C D E F G H I} → Γ , A , B , C , D , E , F , G , H , I ⊢ A
V8 = VAR IX8

V9 : ∀ {Γ A B C D E F G H I J} → Γ , A , B , C , D , E , F , G , H , I , J ⊢ A
V9 = VAR IX9
