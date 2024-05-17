module Try1.AltArtemov.Context.Notation where

open import Try1.AltArtemov.Context.Core


ix0 : ∀ {Γ A} → Γ , A ∋ A
ix0 = top

ix1 : ∀ {Γ A B} → Γ , A , B ∋ A
ix1 = pop ix0

ix2 : ∀ {Γ A B C} → Γ , A , B , C ∋ A
ix2 = pop ix1

ix3 : ∀ {Γ A B C D} → Γ , A , B , C , D ∋ A
ix3 = pop ix2

ix4 : ∀ {Γ A B C D E} → Γ , A , B , C , D , E ∋ A
ix4 = pop ix3

ix5 : ∀ {Γ A B C D E F} → Γ , A , B , C , D , E , F ∋ A
ix5 = pop ix4

ix6 : ∀ {Γ A B C D E F G} → Γ , A , B , C , D , E , F , G ∋ A
ix6 = pop ix5

ix7 : ∀ {Γ A B C D E F G H} → Γ , A , B , C , D , E , F , G , H ∋ A
ix7 = pop ix6

ix8 : ∀ {Γ A B C D E F G H I} → Γ , A , B , C , D , E , F , G , H , I ∋ A
ix8 = pop ix7

ix9 : ∀ {Γ A B C D E F G H I J} → Γ , A , B , C , D , E , F , G , H , I , J ∋ A
ix9 = pop ix8
