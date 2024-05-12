module AltArtemov.Term.Notation.Level1 where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import AltArtemov.Context
open import AltArtemov.Term.Core
open import AltArtemov.Term.Representation
open import AltArtemov.Type
open import AltArtemov.Variable


var : ∀ {Γ A Z}
    → A ∈ Γ
    → wkᴬ* A ≡ Z
    → Γ ⊢ Z
var x refl = var[ 0 ] x

lam : ∀ {Γ A B Z}
    → Γ , A ⊢ wkᴬ* B
    → wkᴬ* (A ⊃ B) ≡ Z
    → Γ ⊢ Z
lam t refl = lam[ 0 ] {ts = []} t

app : ∀ {Γ A B Z}
    → Γ ⊢ wkᴬ* (A ⊃ B)    → Γ ⊢ wkᴬ* A
    → wkᴬ* B ≡ Z
    → Γ ⊢ Z
app t u refl = app[ 0 ] {[]} {[]} t u

pair : ∀ {Γ A B Z}
    → Γ ⊢ wkᴬ* A    → Γ ⊢ wkᴬ* B
    → wkᴬ* (A ∧ B) ≡ Z
    → Γ ⊢ Z
pair t u refl = pair[ 0 ] {[]} {[]} t u

fst : ∀ {Γ A B Z}
    → Γ ⊢ wkᴬ* (A ∧ B)
    → wkᴬ* A ≡ Z
    → Γ ⊢ Z
fst t refl = fst[ 0 ] {[]} t

snd : ∀ {Γ A B Z}
    → Γ ⊢ wkᴬ* (A ∧ B)
    → wkᴬ* B ≡ Z
    → Γ ⊢ Z
snd t refl = snd[ 0 ] {[]} t

up : ∀ {Γ s A Z}
    → Γ ⊢ wkᴬ* (s ∶ A)
    → wkᴬ* (! s ∶ s ∶ A) ≡ Z
    → Γ ⊢ Z
up t refl = up[ 0 ] {[]} t

down : ∀ {Γ s A Z}
    → Γ ⊢ wkᴬ* (s ∶ A)
    → wkᴬ* A ≡ Z
    → Γ ⊢ Z
down t refl = down[ 0 ] {[]} t

boom : ∀ {Γ A Z}
    → Γ ⊢ wkᴬ* ⊥
    → wkᴬ* A ≡ Z
    → Γ ⊢ Z
boom t refl = boom[ 0 ] {[]} t


v0 : ∀ {Γ A} → Γ , A ⊢ wkᴬ* A
v1 : ∀ {Γ A B} → Γ , A , B ⊢ wkᴬ* A
v2 : ∀ {Γ A B C} → Γ , A , B , C ⊢ wkᴬ* A
v3 : ∀ {Γ A B C D} → Γ , A , B , C , D ⊢ wkᴬ* A
v4 : ∀ {Γ A B C D E} → Γ , A , B , C , D , E ⊢ wkᴬ* A
v5 : ∀ {Γ A B C D E F} → Γ , A , B , C , D , E , F ⊢ wkᴬ* A
v6 : ∀ {Γ A B C D E F G} → Γ , A , B , C , D , E , F , G ⊢ wkᴬ* A
v7 : ∀ {Γ A B C D E F G H} → Γ , A , B , C , D , E , F , G , H ⊢ wkᴬ* A
v8 : ∀ {Γ A B C D E F G H I} → Γ , A , B , C , D , E , F , G , H , I ⊢ wkᴬ* A
v9 : ∀ {Γ A B C D E F G H I J} → Γ , A , B , C , D , E , F , G , H , I , J ⊢ wkᴬ* A
v0 = var 0ˣ refl
v1 = var 1ˣ refl
v2 = var 2ˣ refl
v3 = var 3ˣ refl
v4 = var 4ˣ refl
v5 = var 5ˣ refl
v6 = var 6ˣ refl
v7 = var 7ˣ refl
v8 = var 8ˣ refl
v9 = var 9ˣ refl
