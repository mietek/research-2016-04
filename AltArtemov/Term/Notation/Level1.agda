module AltArtemov.Term.Notation.Level1 where

open import Relation.Binary.PropositionalEquality using (_≡_)

open import AltArtemov.Context
open import AltArtemov.Term.Core
open import AltArtemov.Term.Representation
open import AltArtemov.Type
open import AltArtemov.Variable

open import AltArtemov.WIP.TySubst#


var : ∀ {Γ A Z}
    → A ∈ Γ
    → {{_ : wkᴬ* A ≡ Z}}
    → Γ ⊢ Z
var = var[ 0 ]

lam : ∀ {Γ A B Z}
    → Γ , A ⊢ wkᴬ* B
    → {{_ : wkᴬ* (A ⊃ B) ≡ Z}}
    → Γ ⊢ Z
lam = lam[ 0 ] {ts = []}

app : ∀ {Γ A B Z}
    → Γ ⊢ wkᴬ* (A ⊃ B)    → Γ ⊢ wkᴬ* A
    → {{_ : wkᴬ* B ≡ Z}}
    → Γ ⊢ Z
app = app[ 0 ] {[]} {[]}

pair : ∀ {Γ A B Z}
    → Γ ⊢ wkᴬ* A    → Γ ⊢ wkᴬ* B
    → {{_ : wkᴬ* (A ∧ B) ≡ Z}}
    → Γ ⊢ Z
pair = pair[ 0 ] {[]} {[]}

fst : ∀ {Γ A B Z}
    → Γ ⊢ wkᴬ* (A ∧ B)
    → {{_ : wkᴬ* A ≡ Z}}
    → Γ ⊢ Z
fst = fst[ 0 ] {[]}

snd : ∀ {Γ A B Z}
    → Γ ⊢ wkᴬ* (A ∧ B)
    → {{_ : wkᴬ* B ≡ Z}}
    → Γ ⊢ Z
snd = snd[ 0 ] {[]}

up : ∀ {Γ s A Z}
    → Γ ⊢ wkᴬ* (s ∶ A)
    → {{_ : wkᴬ* (! s ∶ s ∶ A) ≡ Z}}
    → Γ ⊢ Z
up = up[ 0 ] {[]}

down : ∀ {Γ s A Z}
    → Γ ⊢ wkᴬ* (s ∶ A)
    → {{_ : wkᴬ* A ≡ Z}}
    → Γ ⊢ Z
down = down[ 0 ] {[]}

boom : ∀ {Γ A Z}
    → Γ ⊢ wkᴬ* ⊥
    → {{_ : wkᴬ* A ≡ Z}}
    → Γ ⊢ Z
boom = boom[ 0 ] {[]}


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
v0 = var 0ˣ
v1 = var 1ˣ
v2 = var 2ˣ
v3 = var 3ˣ
v4 = var 4ˣ
v5 = var 5ˣ
v6 = var 6ˣ
v7 = var 7ˣ
v8 = var 8ˣ
v9 = var 9ˣ
