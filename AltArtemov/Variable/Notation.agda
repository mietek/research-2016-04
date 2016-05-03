module AltArtemov.Variable.Notation where

open import AltArtemov.Context
open import AltArtemov.Variable.Core


0ˣ : ∀ {Γ A} → A ∈ (Γ , A)
1ˣ : ∀ {Γ A B} → A ∈ (Γ , A , B)
2ˣ : ∀ {Γ A B C} → A ∈ (Γ , A , B , C)
3ˣ : ∀ {Γ A B C D} → A ∈ (Γ , A , B , C , D)
4ˣ : ∀ {Γ A B C D E} → A ∈ (Γ , A , B , C , D , E)
5ˣ : ∀ {Γ A B C D E F} → A ∈ (Γ , A , B , C , D , E , F)
6ˣ : ∀ {Γ A B C D E F G} → A ∈ (Γ , A , B , C , D , E , F , G)
7ˣ : ∀ {Γ A B C D E F G H} → A ∈ (Γ , A , B , C , D , E , F , G , H)
8ˣ : ∀ {Γ A B C D E F G H I} → A ∈ (Γ , A , B , C , D , E , F , G , H , I)
9ˣ : ∀ {Γ A B C D E F G H I J} → A ∈ (Γ , A , B , C , D , E , F , G , H , I , J)
0ˣ = top
1ˣ = pop 0ˣ
2ˣ = pop 1ˣ
3ˣ = pop 2ˣ
4ˣ = pop 3ˣ
5ˣ = pop 4ˣ
6ˣ = pop 5ˣ
7ˣ = pop 6ˣ
8ˣ = pop 7ˣ
9ˣ = pop 8ˣ
