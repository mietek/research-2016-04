module S4.Derivation.Notation.Level1 where

open import S4.Derivation.Level1
open import S4.Context
open import S4.Term
open import S4.Type


infixr 0 ⊩_

⊩_ : ∀ (A : Ty) → Set
⊩ A = ∀ {Δ Γ} → Δ ∙ Γ ⊢ A


V0 : ∀ {Δ Γ A} → Δ ∙ Γ , A ⊢ A
V0 = VAR IX0

V1 : ∀ {Δ Γ A B} → Δ ∙ Γ , A , B ⊢ A
V1 = VAR IX1

V2 : ∀ {Δ Γ A B C} → Δ ∙ Γ , A , B , C ⊢ A
V2 = VAR IX2

V3 : ∀ {Δ Γ A B C D} → Δ ∙ Γ , A , B , C , D ⊢ A
V3 = VAR IX3

V4 : ∀ {Δ Γ A B C D E} → Δ ∙ Γ , A , B , C , D , E ⊢ A
V4 = VAR IX4

V5 : ∀ {Δ Γ A B C D E F} → Δ ∙ Γ , A , B , C , D , E , F ⊢ A
V5 = VAR IX5

V6 : ∀ {Δ Γ A B C D E F G} → Δ ∙ Γ , A , B , C , D , E , F , G ⊢ A
V6 = VAR IX6

V7 : ∀ {Δ Γ A B C D E F G H} → Δ ∙ Γ , A , B , C , D , E , F , G , H ⊢ A
V7 = VAR IX7

V8 : ∀ {Δ Γ A B C D E F G H I} → Δ ∙ Γ , A , B , C , D , E , F , G , H , I ⊢ A
V8 = VAR IX8

V9 : ∀ {Δ Γ A B C D E F G H I J} → Δ ∙ Γ , A , B , C , D , E , F , G , H , I , J ⊢ A
V9 = VAR IX9


V0* : ∀ {Δ Γ A} → Δ , A ∙ Γ ⊢ A
V0* = VAR* IX0

V1* : ∀ {Δ Γ A B} → Δ , A , B ∙ Γ ⊢ A
V1* = VAR* IX1

V2* : ∀ {Δ Γ A B C} → Δ , A , B , C ∙ Γ ⊢ A
V2* = VAR* IX2

V3* : ∀ {Δ Γ A B C D} → Δ , A , B , C , D ∙ Γ ⊢ A
V3* = VAR* IX3

V4* : ∀ {Δ Γ A B C D E} → Δ , A , B , C , D , E ∙ Γ ⊢ A
V4* = VAR* IX4

V5* : ∀ {Δ Γ A B C D E F} → Δ , A , B , C , D , E , F ∙ Γ ⊢ A
V5* = VAR* IX5

V6* : ∀ {Δ Γ A B C D E F G} → Δ , A , B , C , D , E , F , G ∙ Γ ⊢ A
V6* = VAR* IX6

V7* : ∀ {Δ Γ A B C D E F G H} → Δ , A , B , C , D , E , F , G , H ∙ Γ ⊢ A
V7* = VAR* IX7

V8* : ∀ {Δ Γ A B C D E F G H I} → Δ , A , B , C , D , E , F , G , H , I ∙ Γ ⊢ A
V8* = VAR* IX8

V9* : ∀ {Δ Γ A B C D E F G H I J} → Δ , A , B , C , D , E , F , G , H , I , J ∙ Γ ⊢ A
V9* = VAR* IX9
