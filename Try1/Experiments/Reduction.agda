module Experiments.Reduction where

open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import AltArtemov


Ren : Cx → Cx → Set
Ren Γ Δ = ∀ {a} {A : Ty a} → Γ ∋ A → Δ ∋ A

Sub : Cx → Cx → Set
Sub Γ Δ = ∀ {a} {A : Ty a} → Γ ∋ A → Δ ⊢ A

weaken-ren : ∀ {Γ Δ a} {A : Ty a} → Ren Γ Δ → Ren (Γ , A) (Δ , A)
weaken-ren f top     = top
weaken-ren f (pop i) = pop (f i)

baz : ∀ {Γ Δ} → Ren Γ Δ → Tm → Tm
baz f (VAR[ n ] i)   = {!!}
baz f (LAM[ n ] t)   = {!!}
baz f (APP[ n ] t s) = {!!}
baz f (UP[ n ] t)    = {!!}
baz f (DOWN[ n ] t)  = {!!}
baz f (BOOM[ n ] t)  = {!!}

bar : ∀ {Γ Δ a} → Ren Γ Δ → Ty a → Ty a
bar f ⊥      = ⊥
bar f (A ⊃ B) = A ⊃ B
bar f (t ∶ A) = baz f t ∶ bar f A

foo : ∀ {Γ Δ n a} {A : Ty a} {Z : Ty (n + a)} (i : Γ ∋ A) (f : Ren Γ Δ)
    → VARs[ n ] (ix i) ∶⋯∶ A ≡ Z
    → VARs[ n ] (ix (f i)) ∶⋯∶ A ≡ bar f Z
foo top f refl = {!refl!}
foo (pop i) f refl = {!!}

ren : ∀ {Γ Δ a} {A : Ty a} → Γ ⊢ A → Ren Γ Δ → Δ ⊢ A
ren (var[ n ] i {{p}})            f = {!!} -- var[ n ] (f i) {{foo i f p}}
ren (lam[ n ] {ts = ts} d)        f = lam[ n ] {ts = ts} (ren d (weaken-ren f))
ren (app[ n ] {ts = ts} {ss} d c) f = app[ n ] {ts = ts} {ss} (ren d f) (ren c f)
ren (up[ n ] {ts = ts} d)         f = up[ n ] {ts = ts} (ren d f)
ren (down[ n ] {ts = ts} d)       f = down[ n ] {ts = ts} (ren d f)
ren (boom[ n ] {ts = ts} {A} d)   f = boom[ n ] {ts = ts} {A} (ren d f)

weaken-sub : ∀ {Γ Δ a} {A : Ty a} → Sub Γ Δ → Sub (Γ , A) (Δ , A)
weaken-sub f top     = var top
weaken-sub f (pop i) = ren (f i) pop

sub : ∀ {Γ Δ a} {A : Ty a} → Γ ⊢ A → Sub Γ Δ → Δ ⊢ A
sub (var[ n ] i {{p}})            f = {!f i!}
sub (lam[ n ] {ts = ts} d)        f = lam[ n ] {ts = ts} (sub d (weaken-sub f))
sub (app[ n ] {ts = ts} {ss} d c) f = app[ n ] {ts = ts} {ss} (sub d f) (sub c f)
sub (up[ n ] {ts = ts} d)         f = up[ n ] {ts = ts} (sub d f)
sub (down[ n ] {ts = ts} d)       f = down[ n ] {ts = ts} (sub d f)
sub (boom[ n ] {ts = ts} {A} d)   f = boom[ n ] {ts = ts} {A} (sub d f)

strengthen : ∀ {Γ a} {A : Ty a} → Γ ⊢ A → Sub (Γ , A) Γ
strengthen t top     = t
strengthen t (pop i) = var i

-- redex : ∀ {Γ a} {A : Ty a} → Γ ⊢ A → Maybe (Γ ⊢ A)
-- redex (var[ n ] i)   = nothing
-- redex (lam[ n ] d)   with redex d
-- redex (lam[ n ] d)   | just d′ = just (lam[ n ] d′)
-- redex (lam[ n ] d)   | nothing = nothing
-- redex (app[ n ] d c) = {!!}
-- redex (up[ n ] d)    = {!!}
-- redex (down[ n ] d)  = {!!}
-- redex (boom[ n ] d)  = {!!}
