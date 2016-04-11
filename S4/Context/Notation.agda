module S4.Context.Notation where

open import S4.Context.Core


IX0 : ∀ {Γ A} → Γ , A ∋ A
IX0 = top

IX1 : ∀ {Γ A B} → Γ , A , B ∋ A
IX1 = pop IX0

IX2 : ∀ {Γ A B C} → Γ , A , B , C ∋ A
IX2 = pop IX1

IX3 : ∀ {Γ A B C D} → Γ , A , B , C , D ∋ A
IX3 = pop IX2

IX4 : ∀ {Γ A B C D E} → Γ , A , B , C , D , E ∋ A
IX4 = pop IX3

IX5 : ∀ {Γ A B C D E F} → Γ , A , B , C , D , E , F ∋ A
IX5 = pop IX4

IX6 : ∀ {Γ A B C D E F G} → Γ , A , B , C , D , E , F , G ∋ A
IX6 = pop IX5

IX7 : ∀ {Γ A B C D E F G H} → Γ , A , B , C , D , E , F , G , H ∋ A
IX7 = pop IX6

IX8 : ∀ {Γ A B C D E F G H I} → Γ , A , B , C , D , E , F , G , H , I ∋ A
IX8 = pop IX7

IX9 : ∀ {Γ A B C D E F G H I J} → Γ , A , B , C , D , E , F , G , H , I , J ∋ A
IX9 = pop IX8
