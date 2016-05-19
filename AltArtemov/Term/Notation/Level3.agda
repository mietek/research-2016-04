module AltArtemov.Term.Notation.Level3 where

open import Relation.Binary.PropositionalEquality using (_≡_)

open import AltArtemov.Context
open import AltArtemov.Term.Core
open import AltArtemov.Term.Representation
open import AltArtemov.Type
open import AltArtemov.Variable


var³ : ∀ {Γ A Z}
    → (x : A ∈ Γ)
    → {{_ : VAR[ 1 ] ⌊ x ⌋ˣ ∶ VAR[ 0 ] ⌊ x ⌋ˣ ∶ wkᴬ* A ≡ Z}}
    → Γ ⊢ Z
var³ = var[ 2 ]

lam³ : ∀ {Γ A t₂ t B Z}
    → Γ , A ⊢ t₂ ∶ t ∶ wkᴬ* B
    → {{_ : LAM[ 1 ] t₂ ∶ LAM[ 0 ] t ∶ wkᴬ* (A ⊃ B) ≡ Z}}
    → Γ ⊢ Z
lam³ {t₂ = t₂} {t} = lam[ 2 ] {ts = t₂ ∷ t ∷ []}

app³ : ∀ {Γ t₂ t u₂ u A B Z}
    → Γ ⊢ t₂ ∶ t ∶ wkᴬ* (A ⊃ B)    → Γ ⊢ u₂ ∶ u ∶ wkᴬ* A
    → {{_ : APP[ 1 ] t₂ u₂ ∶ APP[ 0 ] t u ∶ wkᴬ* B ≡ Z}}
    → Γ ⊢ Z
app³ {t₂ = t₂} {t} {u₂} {u} = app[ 2 ] {t₂ ∷ t ∷ []} {u₂ ∷ u ∷ []}

pair³ : ∀ {Γ t₂ t u₂ u A B Z}
    → Γ ⊢ t₂ ∶ t ∶ wkᴬ* A    → Γ ⊢ u₂ ∶ u ∶ wkᴬ* B
    → {{_ : PAIR[ 1 ] t₂ u₂ ∶ PAIR[ 0 ] t u ∶ wkᴬ* (A ∧ B) ≡ Z}}
    → Γ ⊢ Z
pair³ {t₂ = t₂} {t} {u₂} {u} = pair[ 2 ] {t₂ ∷ t ∷ []} {u₂ ∷ u ∷ []}

fst³ : ∀ {Γ t₂ t A B Z}
    → Γ ⊢ t₂ ∶ t ∶ wkᴬ* (A ∧ B)
    → {{_ : FST[ 1 ] t₂ ∶ FST[ 0 ] t ∶ wkᴬ* A ≡ Z}}
    → Γ ⊢ Z
fst³ {t₂ = t₂} {t} = fst[ 2 ] {t₂ ∷ t ∷ []}

snd³ : ∀ {Γ t₂ t A B Z}
    → Γ ⊢ t₂ ∶ t ∶ wkᴬ* (A ∧ B)
    → {{_ : SND[ 1 ] t₂ ∶ SND[ 0 ] t ∶ wkᴬ* B ≡ Z}}
    → Γ ⊢ Z
snd³ {t₂ = t₂} {t} = snd[ 2 ] {t₂ ∷ t ∷ []}

up³ : ∀ {Γ t₂ t s A Z}
    → Γ ⊢ t₂ ∶ t ∶ wkᴬ* (s ∶ A)
    → {{_ : UP[ 1 ] t₂ ∶ UP[ 0 ] t ∶ wkᴬ* (! s ∶ s ∶ A) ≡ Z}}
    → Γ ⊢ Z
up³ {t₂ = t₂} {t} = up[ 2 ] {t₂ ∷ t ∷ []}

down³ : ∀ {Γ t₂ t s A Z}
    → Γ ⊢ t₂ ∶ t ∶ wkᴬ* (s ∶ A)
    → {{_ : DOWN[ 1 ] t₂ ∶ DOWN[ 0 ] t ∶ wkᴬ* A ≡ Z}}
    → Γ ⊢ Z
down³ {t₂ = t₂} {t} = down[ 2 ] {t₂ ∷ t ∷ []}

boom³ : ∀ {Γ t₂ t A Z}
    → Γ ⊢ t₂ ∶ t ∶ wkᴬ* ⊥
    → {{_ : BOOM[ 1 ] t₂ ∶ BOOM[ 0 ] t ∶ wkᴬ* A ≡ Z}}
    → Γ ⊢ Z
boom³ {t₂ = t₂} {t} = boom[ 2 ] {t₂ ∷ t ∷ []}


v0³ : ∀ {Γ A} → Γ , A ⊢ V0² ∶ V0 ∶ wkᴬ* A
v1³ : ∀ {Γ A B} → Γ , A , B ⊢ V1² ∶ V1 ∶ wkᴬ* A
v2³ : ∀ {Γ A B C} → Γ , A , B , C ⊢ V2² ∶ V2 ∶ wkᴬ* A
v3³ : ∀ {Γ A B C D} → Γ , A , B , C , D ⊢ V3² ∶ V3 ∶ wkᴬ* A
v4³ : ∀ {Γ A B C D E} → Γ , A , B , C , D , E ⊢ V4² ∶ V4 ∶ wkᴬ* A
v5³ : ∀ {Γ A B C D E F} → Γ , A , B , C , D , E , F ⊢ V5² ∶ V5 ∶ wkᴬ* A
v6³ : ∀ {Γ A B C D E F G} → Γ , A , B , C , D , E , F , G ⊢ V6² ∶ V6 ∶ wkᴬ* A
v7³ : ∀ {Γ A B C D E F G H} → Γ , A , B , C , D , E , F , G , H ⊢ V7² ∶ V7 ∶ wkᴬ* A
v8³ : ∀ {Γ A B C D E F G H I} → Γ , A , B , C , D , E , F , G , H , I ⊢ V8² ∶ V8 ∶ wkᴬ* A
v9³ : ∀ {Γ A B C D E F G H I J} → Γ , A , B , C , D , E , F , G , H , I , J ⊢ V9² ∶ V9 ∶ wkᴬ* A
v0³ = var³ 0ˣ
v1³ = var³ 1ˣ
v2³ = var³ 2ˣ
v3³ = var³ 3ˣ
v4³ = var³ 4ˣ
v5³ = var³ 5ˣ
v6³ = var³ 6ˣ
v7³ = var³ 7ˣ
v8³ = var³ 8ˣ
v9³ = var³ 9ˣ
