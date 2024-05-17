module Try1.AltArtemov.Derivation.Notation.Level1 where

open import Try1.AltArtemov.Context
open import Try1.AltArtemov.Derivation.Core
open import Try1.AltArtemov.Term
open import Try1.AltArtemov.TermVector
open import Try1.AltArtemov.Type


var : ∀ {A Γ}
    → Γ ∋ A
    → Γ ⊢ A
var i = var[ 0 ] i

lam : ∀ {A B Γ}
    → Γ , A ⊢ B
    → Γ ⊢ A ⊃ B
lam = lam[ 0 ] {ts = []}

app : ∀ {A B Γ}
    → Γ ⊢ A ⊃ B    → Γ ⊢ A
    → Γ ⊢ B
app = app[ 0 ] {ts = []} {ss = []}

pair : ∀ {A B Γ}
    → Γ ⊢ A    → Γ ⊢ B
    → Γ ⊢ A ∧ B
pair = pair[ 0 ] {ts = []} {ss = []}

fst : ∀ {A B Γ}
    → Γ ⊢ A ∧ B
    → Γ ⊢ A
fst = fst[ 0 ] {ts = []}

snd : ∀ {A B Γ}
    → Γ ⊢ A ∧ B
    → Γ ⊢ B
snd = snd[ 0 ] {ts = []}

up : ∀ {u A Γ}
    → Γ ⊢ u ∶ A
    → Γ ⊢ quo u ∶ u ∶ A
up = up[ 0 ] {ts = []}

down : ∀ {u A Γ}
    → Γ ⊢ u ∶ A
    → Γ ⊢ A
down = down[ 0 ] {ts = []}

boom : ∀ {A Γ}
    → Γ ⊢ ⊥
    → Γ ⊢ A
boom = boom[ 0 ] {ts = []}

eq : ∀ {u A B Γ}
    → Γ ⊢ u ∶ A    → Γ ⊢ u ∶ B
    → Γ ⊢ A ≑ B
eq = eq[ 0 ] {ts = []} {ss = []}


v0 : ∀ {Γ A} → Γ , A ⊢ A
v0 = var ix0

v1 : ∀ {Γ A B} → Γ , A , B ⊢ A
v1 = var ix1

v2 : ∀ {Γ A B C} → Γ , A , B , C ⊢ A
v2 = var ix2

v3 : ∀ {Γ A B C D} → Γ , A , B , C , D ⊢ A
v3 = var ix3

v4 : ∀ {Γ A B C D E} → Γ , A , B , C , D , E ⊢ A
v4 = var ix4

v5 : ∀ {Γ A B C D E F} → Γ , A , B , C , D , E , F ⊢ A
v5 = var ix5

v6 : ∀ {Γ A B C D E F G} → Γ , A , B , C , D , E , F , G ⊢ A
v6 = var ix6

v7 : ∀ {Γ A B C D E F G H} → Γ , A , B , C , D , E , F , G , H ⊢ A
v7 = var ix7

v8 : ∀ {Γ A B C D E F G H I} → Γ , A , B , C , D , E , F , G , H , I ⊢ A
v8 = var ix8

v9 : ∀ {Γ A B C D E F G H I J} → Γ , A , B , C , D , E , F , G , H , I , J ⊢ A
v9 = var ix9
