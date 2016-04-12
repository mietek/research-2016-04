module S4.Derivation.Notation.Level2 where

open import S4.Derivation.Level2
open import S4.Context
open import S4.Term
open import S4.Type


infixr 0 ⊩_∶_

⊩_∶_ : ∀ (t : Tm) (A : Ty) → Set
⊩ t ∶ A = ∅ ∙ ∅ ⊢ t ∶ A


V0² : ∀ {Δ Γ A} → Δ ∙ Γ , A ⊢ v0 ∶ A
V0² = VAR² IX0

V1² : ∀ {Δ Γ A B} → Δ ∙ Γ , A , B ⊢ v1 ∶ A
V1² = VAR² IX1

V2² : ∀ {Δ Γ A B C} → Δ ∙ Γ , A , B , C ⊢ v2 ∶ A
V2² = VAR² IX2

V3² : ∀ {Δ Γ A B C D} → Δ ∙ Γ , A , B , C , D ⊢ v3 ∶ A
V3² = VAR² IX3

V4² : ∀ {Δ Γ A B C D E} → Δ ∙ Γ , A , B , C , D , E ⊢ v4 ∶ A
V4² = VAR² IX4

V5² : ∀ {Δ Γ A B C D E F} → Δ ∙ Γ , A , B , C , D , E , F ⊢ v5 ∶ A
V5² = VAR² IX5

V6² : ∀ {Δ Γ A B C D E F G} → Δ ∙ Γ , A , B , C , D , E , F , G ⊢ v6 ∶ A
V6² = VAR² IX6

V7² : ∀ {Δ Γ A B C D E F G H} → Δ ∙ Γ , A , B , C , D , E , F , G , H ⊢ v7 ∶ A
V7² = VAR² IX7

V8² : ∀ {Δ Γ A B C D E F G H I} → Δ ∙ Γ , A , B , C , D , E , F , G , H , I ⊢ v8 ∶ A
V8² = VAR² IX8

V9² : ∀ {Δ Γ A B C D E F G H I J} → Δ ∙ Γ , A , B , C , D , E , F , G , H , I , J ⊢ v9 ∶ A
V9² = VAR² IX9


V0*² : ∀ {Δ Γ A} → Δ , A ∙ Γ ⊢ v0* ∶ A
V0*² = VAR*² IX0

V1*² : ∀ {Δ Γ A B} → Δ , A , B ∙ Γ ⊢ v1* ∶ A
V1*² = VAR*² IX1

V2*² : ∀ {Δ Γ A B C} → Δ , A , B , C ∙ Γ ⊢ v2* ∶ A
V2*² = VAR*² IX2

V3*² : ∀ {Δ Γ A B C D} → Δ , A , B , C , D ∙ Γ ⊢ v3* ∶ A
V3*² = VAR*² IX3

V4*² : ∀ {Δ Γ A B C D E} → Δ , A , B , C , D , E ∙ Γ ⊢ v4* ∶ A
V4*² = VAR*² IX4

V5*² : ∀ {Δ Γ A B C D E F} → Δ , A , B , C , D , E , F ∙ Γ ⊢ v5* ∶ A
V5*² = VAR*² IX5

V6*² : ∀ {Δ Γ A B C D E F G} → Δ , A , B , C , D , E , F , G ∙ Γ ⊢ v6* ∶ A
V6*² = VAR*² IX6

V7*² : ∀ {Δ Γ A B C D E F G H} → Δ , A , B , C , D , E , F , G , H ∙ Γ ⊢ v7* ∶ A
V7*² = VAR*² IX7

V8*² : ∀ {Δ Γ A B C D E F G H I} → Δ , A , B , C , D , E , F , G , H , I ∙ Γ ⊢ v8* ∶ A
V8*² = VAR*² IX8

V9*² : ∀ {Δ Γ A B C D E F G H I J} → Δ , A , B , C , D , E , F , G , H , I , J ∙ Γ ⊢ v9* ∶ A
V9*² = VAR*² IX9
