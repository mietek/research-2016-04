module AltArtemov.Term.Notation.Level2 where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import AltArtemov.Context
open import AltArtemov.Term.Core
open import AltArtemov.Term.Representation
open import AltArtemov.Type
open import AltArtemov.Variable


var² : ∀ {Γ A Z}
    → (x : A ∈ Γ)
    → VAR[ 0 ] ⌊ x ⌋ˣ ∶ wkᴬ* A ≡ Z
    → Γ ⊢ Z
var² x refl = var[ 1 ] x

lam² : ∀ {Γ A t B Z}
    → Γ , A ⊢ t ∶ wkᴬ* B
    → LAM[ 0 ] t ∶ wkᴬ* (A ⊃ B) ≡ Z
    → Γ ⊢ Z
lam² {t = t} t₂ refl = lam[ 1 ] {ts = t ∷ []} t₂

app² : ∀ {Γ t u A B Z}
    → Γ ⊢ t ∶ wkᴬ* (A ⊃ B)    → Γ ⊢ u ∶ wkᴬ* A
    → APP[ 0 ] t u ∶ wkᴬ* B ≡ Z
    → Γ ⊢ Z
app² {t = t} {u} t₂ u₂ refl = app[ 1 ] {t ∷ []} {u ∷ []} t₂ u₂

pair² : ∀ {Γ t u A B Z}
    → Γ ⊢ t ∶ wkᴬ* A    → Γ ⊢ u ∶ wkᴬ* B
    → PAIR[ 0 ] t u ∶ wkᴬ* (A ∧ B) ≡ Z
    → Γ ⊢ Z
pair² {t = t} {u} t₂ u₂ refl = pair[ 1 ] {t ∷ []} {u ∷ []} t₂ u₂

fst² : ∀ {Γ t A B Z}
    → Γ ⊢ t ∶ wkᴬ* (A ∧ B)
    → FST[ 0 ] t ∶ wkᴬ* A ≡ Z
    → Γ ⊢ Z
fst² {t = t} t₂ refl = fst[ 1 ] {t ∷ []} t₂

snd² : ∀ {Γ t A B Z}
    → Γ ⊢ t ∶ wkᴬ* (A ∧ B)
    → SND[ 0 ] t ∶ wkᴬ* B ≡ Z
    → Γ ⊢ Z
snd² {t = t} t₂ refl = snd[ 1 ] {t ∷ []} t₂

up² : ∀ {Γ t s A Z}
    → Γ ⊢ t ∶ wkᴬ* (s ∶ A)
    → UP[ 0 ] t ∶ wkᴬ* (! s ∶ s ∶ A) ≡ Z
    → Γ ⊢ Z
up² {t = t} t₂ refl = up[ 1 ] {t ∷ []} t₂

down² : ∀ {Γ t s A Z}
    → Γ ⊢ t ∶ wkᴬ* (s ∶ A)
    → DOWN[ 0 ] t ∶ wkᴬ* A ≡ Z
    → Γ ⊢ Z
down² {t = t} t₂ refl = down[ 1 ] {t ∷ []} t₂

boom² : ∀ {Γ t A Z}
    → Γ ⊢ t ∶ wkᴬ* ⊥
    → BOOM[ 0 ] t ∶ wkᴬ* A ≡ Z
    → Γ ⊢ Z
boom² {t = t} t₂ refl = boom[ 1 ] {t ∷ []} t₂


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
v0² = var² 0ˣ refl
v1² = var² 1ˣ refl
v2² = var² 2ˣ refl
v3² = var² 3ˣ refl
v4² = var² 4ˣ refl
v5² = var² 5ˣ refl
v6² = var² 6ˣ refl
v7² = var² 7ˣ refl
v8² = var² 8ˣ refl
v9² = var² 9ˣ refl
