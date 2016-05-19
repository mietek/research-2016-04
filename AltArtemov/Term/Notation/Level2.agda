module AltArtemov.Term.Notation.Level2 where

open import Relation.Binary.PropositionalEquality using (_≡_)

open import AltArtemov.Context
open import AltArtemov.Term.Core
open import AltArtemov.Term.Representation
open import AltArtemov.Type
open import AltArtemov.Variable


var² : ∀ {Γ A Z}
    → (x : A ∈ Γ)
    → {{_ : VAR[ 0 ] ⌊ x ⌋ˣ ∶ wkᴬ* A ≡ Z}}
    → Γ ⊢ Z
var² = var[ 1 ]

lam² : ∀ {Γ A t B Z}
    → Γ , A ⊢ t ∶ wkᴬ* B
    → {{_ : LAM[ 0 ] t ∶ wkᴬ* (A ⊃ B) ≡ Z}}
    → Γ ⊢ Z
lam² {t = t} = lam[ 1 ] {ts = t ∷ []}

app² : ∀ {Γ t u A B Z}
    → Γ ⊢ t ∶ wkᴬ* (A ⊃ B)    → Γ ⊢ u ∶ wkᴬ* A
    → {{_ : APP[ 0 ] t u ∶ wkᴬ* B ≡ Z}}
    → Γ ⊢ Z
app² {t = t} {u} = app[ 1 ] {t ∷ []} {u ∷ []}

pair² : ∀ {Γ t u A B Z}
    → Γ ⊢ t ∶ wkᴬ* A    → Γ ⊢ u ∶ wkᴬ* B
    → {{_ : PAIR[ 0 ] t u ∶ wkᴬ* (A ∧ B) ≡ Z}}
    → Γ ⊢ Z
pair² {t = t} {u} = pair[ 1 ] {t ∷ []} {u ∷ []}

fst² : ∀ {Γ t A B Z}
    → Γ ⊢ t ∶ wkᴬ* (A ∧ B)
    → {{_ : FST[ 0 ] t ∶ wkᴬ* A ≡ Z}}
    → Γ ⊢ Z
fst² {t = t} = fst[ 1 ] {t ∷ []}

snd² : ∀ {Γ t A B Z}
    → Γ ⊢ t ∶ wkᴬ* (A ∧ B)
    → {{_ : SND[ 0 ] t ∶ wkᴬ* B ≡ Z}}
    → Γ ⊢ Z
snd² {t = t} = snd[ 1 ] {t ∷ []}

up² : ∀ {Γ t s A Z}
    → Γ ⊢ t ∶ wkᴬ* (s ∶ A)
    → {{_ : UP[ 0 ] t ∶ wkᴬ* (! s ∶ s ∶ A) ≡ Z}}
    → Γ ⊢ Z
up² {t = t} = up[ 1 ] {t ∷ []}

down² : ∀ {Γ t s A Z}
    → Γ ⊢ t ∶ wkᴬ* (s ∶ A)
    → {{_ : DOWN[ 0 ] t ∶ wkᴬ* A ≡ Z}}
    → Γ ⊢ Z
down² {t = t} = down[ 1 ] {t ∷ []}

boom² : ∀ {Γ t A Z}
    → Γ ⊢ t ∶ wkᴬ* ⊥
    → {{_ : BOOM[ 0 ] t ∶ wkᴬ* A ≡ Z}}
    → Γ ⊢ Z
boom² {t = t} = boom[ 1 ] {t ∷ []}


v0² : ∀ {Γ A} → Γ , A ⊢ V0 ∶ wkᴬ* A
v1² : ∀ {Γ A B} → Γ , A , B ⊢ V1 ∶ wkᴬ* A
v2² : ∀ {Γ A B C} → Γ , A , B , C ⊢ V2 ∶ wkᴬ* A
v3² : ∀ {Γ A B C D} → Γ , A , B , C , D ⊢ V3 ∶ wkᴬ* A
v4² : ∀ {Γ A B C D E} → Γ , A , B , C , D , E ⊢ V4 ∶ wkᴬ* A
v5² : ∀ {Γ A B C D E F} → Γ , A , B , C , D , E , F ⊢ V5 ∶ wkᴬ* A
v6² : ∀ {Γ A B C D E F G} → Γ , A , B , C , D , E , F , G ⊢ V6 ∶ wkᴬ* A
v7² : ∀ {Γ A B C D E F G H} → Γ , A , B , C , D , E , F , G , H ⊢ V7 ∶ wkᴬ* A
v8² : ∀ {Γ A B C D E F G H I} → Γ , A , B , C , D , E , F , G , H , I ⊢ V8 ∶ wkᴬ* A
v9² : ∀ {Γ A B C D E F G H I J} → Γ , A , B , C , D , E , F , G , H , I , J ⊢ V9 ∶ wkᴬ* A
v0² = var² 0ˣ
v1² = var² 1ˣ
v2² = var² 2ˣ
v3² = var² 3ˣ
v4² = var² 4ˣ
v5² = var² 5ˣ
v6² = var² 6ˣ
v7² = var² 7ˣ
v8² = var² 8ˣ
v9² = var² 9ˣ
