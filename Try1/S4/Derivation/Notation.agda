module Try1.S4.Derivation.Notation where

open import Try1.S4.Derivation.Core
open import Try1.S4.Context


v0 : ∀ {Δ Γ A} → Δ ∙ Γ , A ⊢ A
v0 = var ix0

v1 : ∀ {Δ Γ A B} → Δ ∙ Γ , A , B ⊢ A
v1 = var ix1

v2 : ∀ {Δ Γ A B C} → Δ ∙ Γ , A , B , C ⊢ A
v2 = var ix2

v3 : ∀ {Δ Γ A B C D} → Δ ∙ Γ , A , B , C , D ⊢ A
v3 = var ix3

v4 : ∀ {Δ Γ A B C D E} → Δ ∙ Γ , A , B , C , D , E ⊢ A
v4 = var ix4

v5 : ∀ {Δ Γ A B C D E F} → Δ ∙ Γ , A , B , C , D , E , F ⊢ A
v5 = var ix5

v6 : ∀ {Δ Γ A B C D E F G} → Δ ∙ Γ , A , B , C , D , E , F , G ⊢ A
v6 = var ix6

v7 : ∀ {Δ Γ A B C D E F G H} → Δ ∙ Γ , A , B , C , D , E , F , G , H ⊢ A
v7 = var ix7

v8 : ∀ {Δ Γ A B C D E F G H I} → Δ ∙ Γ , A , B , C , D , E , F , G , H , I ⊢ A
v8 = var ix8

v9 : ∀ {Δ Γ A B C D E F G H I J} → Δ ∙ Γ , A , B , C , D , E , F , G , H , I , J ⊢ A
v9 = var ix9


v0* : ∀ {Δ Γ A} → Δ , A ∙ Γ ⊢ A
v0* = var* ix0

v1* : ∀ {Δ Γ A B} → Δ , A , B ∙ Γ ⊢ A
v1* = var* ix1

v2* : ∀ {Δ Γ A B C} → Δ , A , B , C ∙ Γ ⊢ A
v2* = var* ix2

v3* : ∀ {Δ Γ A B C D} → Δ , A , B , C , D ∙ Γ ⊢ A
v3* = var* ix3

v4* : ∀ {Δ Γ A B C D E} → Δ , A , B , C , D , E ∙ Γ ⊢ A
v4* = var* ix4

v5* : ∀ {Δ Γ A B C D E F} → Δ , A , B , C , D , E , F ∙ Γ ⊢ A
v5* = var* ix5

v6* : ∀ {Δ Γ A B C D E F G} → Δ , A , B , C , D , E , F , G ∙ Γ ⊢ A
v6* = var* ix6

v7* : ∀ {Δ Γ A B C D E F G H} → Δ , A , B , C , D , E , F , G , H ∙ Γ ⊢ A
v7* = var* ix7

v8* : ∀ {Δ Γ A B C D E F G H I} → Δ , A , B , C , D , E , F , G , H , I ∙ Γ ⊢ A
v8* = var* ix8

v9* : ∀ {Δ Γ A B C D E F G H I J} → Δ , A , B , C , D , E , F , G , H , I , J ∙ Γ ⊢ A
v9* = var* ix9
