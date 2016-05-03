module AltArtemov.WIP.TmSubstLem where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; cong)

open import AltArtemov.Context
open import AltArtemov.Type
open import AltArtemov.Term.Core
open import AltArtemov.Term.Representation
open import AltArtemov.Variable

open import AltArtemov.Term.Substitution
open import AltArtemov.WIP.TySubst#


∖-dist : ∀ {Γ X} → (x : X ∈ Γ) → ⌊ Γ ∖ᴳ x ⌋ᴳ ≡ ⌊ Γ ⌋ᴳ ∖ᵍ ⌊ x ⌋ˣ
∖-dist top     = refl
∖-dist (pop x) = cong _,◌ (∖-dist x)


wkⁱ′ : ∀ {Γ X} → (x : X ∈ Γ) → ◌∈ ⌊ Γ ∖ᴳ x ⌋ᴳ → ◌∈ ⌊ Γ ⌋ᴳ
wkⁱ′ x rewrite ∖-dist x = wkⁱ ⌊ x ⌋ˣ


wkᵗ′ : ∀ {Γ X} → (x : X ∈ Γ) → ⌊ Γ ∖ᴳ x ⌋ᴳ ⊢◌ → ⌊ Γ ⌋ᴳ ⊢◌
wkᵗ′ x rewrite ∖-dist x = wkᵗ ⌊ x ⌋ˣ


wkᵛ′ : ∀ {Γ X n} → (x : X ∈ Γ) → Vec ⌊ Γ ∖ᴳ x ⌋ᴳ n → Vec ⌊ Γ ⌋ᴳ n
wkᵛ′ x rewrite ∖-dist x = wkᵛ ⌊ x ⌋ˣ


wkᴬ′ : ∀ {Γ X} → (x : X ∈ Γ) → Ty ⌊ Γ ∖ᴳ x ⌋ᴳ → Ty ⌊ Γ ⌋ᴳ
wkᴬ′ x rewrite ∖-dist x = wkᴬ ⌊ x ⌋ˣ


postulate
  oops  : ∀ {g} → (i : ◌∈ g) → (A : Ty ∅)
      → wkᴬ* {g} A ≡ wkᴬ {g} i (wkᴬ* {g ∖ᵍ i} A)


wk-dist-APP : ∀ {g n} → (i : ◌∈ g) → (ts us : Vec (g ∖ᵍ i) n) → (A : Ty ∅)
    → APPs[ n ] (wkᵛ i ts) (wkᵛ i us) ∴ A ≡ wkᴬ i (APPs[ n ] ts us ∴ A)
wk-dist-APP i []       []       A = oops i A
wk-dist-APP i (t ∷ ts) (u ∷ us) A = cong (APP[ _ ] (wkᵗ i t) (wkᵗ i u) ∶_) (wk-dist-APP i ts us A)

wk-dist-PAIR : ∀ {g n} → (i : ◌∈ g) → (ts us : Vec (g ∖ᵍ i) n) → (A : Ty ∅)
    → PAIRs[ n ] (wkᵛ i ts) (wkᵛ i us) ∴ A ≡ wkᴬ i (PAIRs[ n ] ts us ∴ A)
wk-dist-PAIR i []       []       A = oops i A
wk-dist-PAIR i (t ∷ ts) (u ∷ us) A = cong (PAIR[ _ ] (wkᵗ i t) (wkᵗ i u) ∶_) (wk-dist-PAIR i ts us A)

wk-dist-FST : ∀ {g n} → (i : ◌∈ g) → (ts : Vec (g ∖ᵍ i) n) → (A : Ty ∅)
    → FSTs[ n ] (wkᵛ i ts) ∴ A ≡ wkᴬ i (FSTs[ n ] ts ∴ A)
wk-dist-FST i []       A = oops i A
wk-dist-FST i (t ∷ ts) A = cong (FST[ _ ] (wkᵗ i t) ∶_) (wk-dist-FST i ts A)

wk-dist-SND : ∀ {g n} → (i : ◌∈ g) → (ts : Vec (g ∖ᵍ i) n) → (A : Ty ∅)
    → SNDs[ n ] (wkᵛ i ts) ∴ A ≡ wkᴬ i (SNDs[ n ] ts ∴ A)
wk-dist-SND i []       A = oops i A
wk-dist-SND i (t ∷ ts) A = cong (SND[ _ ] (wkᵗ i t) ∶_) (wk-dist-SND i ts A)

wk-dist-UP : ∀ {g n} → (i : ◌∈ g) → (ts : Vec (g ∖ᵍ i) n) → (A : Ty ∅)
    → UPs[ n ] (wkᵛ i ts) ∴ A ≡ wkᴬ i (UPs[ n ] ts ∴ A)
wk-dist-UP i []       A = oops i A
wk-dist-UP i (t ∷ ts) A = cong (UP[ _ ] (wkᵗ i t) ∶_) (wk-dist-UP i ts A)

wk-dist-DOWN : ∀ {g n} → (i : ◌∈ g) → (ts : Vec (g ∖ᵍ i) n) → (A : Ty ∅)
    → DOWNs[ n ] (wkᵛ i ts) ∴ A ≡ wkᴬ i (DOWNs[ n ] ts ∴ A)
wk-dist-DOWN i []       A = oops i A
wk-dist-DOWN i (t ∷ ts) A = cong (DOWN[ _ ] (wkᵗ i t) ∶_) (wk-dist-DOWN i ts A)

wk-dist-BOOM : ∀ {g n} → (i : ◌∈ g) → (ts : Vec (g ∖ᵍ i) n) → (A : Ty ∅)
    → BOOMs[ n ] (wkᵛ i ts) ∴ A ≡ wkᴬ i (BOOMs[ n ] ts ∴ A)
wk-dist-BOOM i []       A = oops i A
wk-dist-BOOM i (t ∷ ts) A = cong (BOOM[ _ ] (wkᵗ i t) ∶_) (wk-dist-BOOM i ts A)


wk-dist-APP′ : ∀ {Γ X n} → (x : X ∈ Γ) → (ts us : Vec ⌊ Γ ∖ᴳ x ⌋ᴳ n) → (A : Ty ∅)
    → APPs[ n ] (wkᵛ′ x ts) (wkᵛ′ x us) ∴ A ≡ wkᴬ′ x (APPs[ n ] ts us ∴ A)
wk-dist-APP′ x rewrite ∖-dist x = wk-dist-APP ⌊ x ⌋ˣ

wk-dist-PAIR′ : ∀ {Γ X n} → (x : X ∈ Γ) → (ts us : Vec ⌊ Γ ∖ᴳ x ⌋ᴳ n) → (A : Ty ∅)
    → PAIRs[ n ] (wkᵛ′ x ts) (wkᵛ′ x us) ∴ A ≡ wkᴬ′ x (PAIRs[ n ] ts us ∴ A)
wk-dist-PAIR′ x rewrite ∖-dist x = wk-dist-PAIR ⌊ x ⌋ˣ

wk-dist-FST′ : ∀ {Γ X n} → (x : X ∈ Γ) → (ts : Vec ⌊ Γ ∖ᴳ x ⌋ᴳ n) → (A : Ty ∅)
    → FSTs[ n ] (wkᵛ′ x ts) ∴ A ≡ wkᴬ′ x (FSTs[ n ] ts ∴ A)
wk-dist-FST′ x rewrite ∖-dist x = wk-dist-FST ⌊ x ⌋ˣ

wk-dist-SND′ : ∀ {Γ X n} → (x : X ∈ Γ) → (ts : Vec ⌊ Γ ∖ᴳ x ⌋ᴳ n) → (A : Ty ∅)
    → SNDs[ n ] (wkᵛ′ x ts) ∴ A ≡ wkᴬ′ x (SNDs[ n ] ts ∴ A)
wk-dist-SND′ x rewrite ∖-dist x = wk-dist-SND ⌊ x ⌋ˣ

wk-dist-UP′ : ∀ {Γ X n} → (x : X ∈ Γ) → (ts : Vec ⌊ Γ ∖ᴳ x ⌋ᴳ n) → (A : Ty ∅)
    → UPs[ n ] (wkᵛ′ x ts) ∴ A ≡ wkᴬ′ x (UPs[ n ] ts ∴ A)
wk-dist-UP′ x rewrite ∖-dist x = wk-dist-UP ⌊ x ⌋ˣ

wk-dist-DOWN′ : ∀ {Γ X n} → (x : X ∈ Γ) → (ts : Vec ⌊ Γ ∖ᴳ x ⌋ᴳ n) → (A : Ty ∅)
    → DOWNs[ n ] (wkᵛ′ x ts) ∴ A ≡ wkᴬ′ x (DOWNs[ n ] ts ∴ A)
wk-dist-DOWN′ x rewrite ∖-dist x = wk-dist-DOWN ⌊ x ⌋ˣ

wk-dist-BOOM′ : ∀ {Γ X n} → (x : X ∈ Γ) → (ts : Vec ⌊ Γ ∖ᴳ x ⌋ᴳ n) → (A : Ty ∅)
    → BOOMs[ n ] (wkᵛ′ x ts) ∴ A ≡ wkᴬ′ x (BOOMs[ n ] ts ∴ A)
wk-dist-BOOM′ x rewrite ∖-dist x = wk-dist-BOOM ⌊ x ⌋ˣ



wk-dist-vec : ∀ {g n} → (i : ◌∈ g) → (ts : Vec (g ∖ᵍ i) n) → (A : Ty ∅)
    → wkᴬ i (ts ∴ A) ≡ wkᵛ i ts ∴ A
wk-dist-vec i []       A = sym (oops i A)
wk-dist-vec i (t ∷ ts) A = cong (wkᵗ i t ∶_) (wk-dist-vec i ts A)


wk-dist-vec′ : ∀ {Γ X n} → (x : X ∈ Γ) → (ts : Vec ⌊ Γ ∖ᴳ x ⌋ᴳ n) → (A : Ty ∅)
    → wkᴬ′ x (ts ∴ A) ≡ wkᵛ′ x ts ∴ A
wk-dist-vec′ x rewrite ∖-dist x = wk-dist-vec ⌊ x ⌋ˣ


wkᵈ : ∀ {Γ X} → (x : X ∈ Γ) → {A : Ty ⌊ Γ ∖ᴳ x ⌋ᴳ} → {A′ : Ty ⌊ Γ ⌋ᴳ}
    → (Γ ∖ᴳ x) ⊢ A
    → {{_ : wkᴬ′ x A ≡ A′}}
    → Γ ⊢ A′

wkᵈ x (var[ n ] {A} y {{refl}}) {{refl}} = {!!}

wkᵈ x (lam[ n ] {ts} {A} {B} d {{refl}}) {{refl}} = {!!}

wkᵈ x (app[ n ] {ts} {us} {A} {B} d e {{refl}}) {{refl}} =
    app[ n ] (wkᵈ x d {{wk-dist-vec′ x ts (A ⊃ B)}}) (wkᵈ x e {{wk-dist-vec′ x us A}}) {{wk-dist-APP′ x ts us B}}

wkᵈ x (pair[ n ] {ts} {us} {A} {B} d e {{refl}}) {{refl}} =
    pair[ n ] (wkᵈ x d {{wk-dist-vec′ x ts A}}) (wkᵈ x e {{wk-dist-vec′ x us B}}) {{wk-dist-PAIR′ x ts us (A ∧ B)}}

wkᵈ x (fst[ n ] {ts} {A} {B} d {{refl}}) {{refl}} =
    fst[ n ] (wkᵈ x d {{wk-dist-vec′ x ts (A ∧ B)}}) {{wk-dist-FST′ x ts A}}

wkᵈ x (snd[ n ] {ts} {A} {B} d {{refl}}) {{refl}} =
    snd[ n ] (wkᵈ x d {{wk-dist-vec′ x ts (A ∧ B)}}) {{wk-dist-SND′ x ts B}}

wkᵈ x (up[ n ] {ts} {s} {A} d {{refl}}) {{refl}} =
    up[ n ] (wkᵈ x d {{wk-dist-vec′ x ts (s ∶ A)}}) {{wk-dist-UP′ x ts (! s ∶ s ∶ A)}}

wkᵈ x (down[ n ] {ts} {s} {A} d {{refl}}) {{refl}} =
    down[ n ] (wkᵈ x d {{wk-dist-vec′ x ts (s ∶ A)}}) {{wk-dist-DOWN′ x ts A}}

wkᵈ x (boom[ n ] {ts} {A} d {{refl}}) {{refl}} =
    boom[ n ] (wkᵈ x d {{wk-dist-vec′ x ts ⊥}}) {{wk-dist-BOOM′ x ts A}}


-- substˣ : ∀ {Γ X A} → ℕ → A ∈ Γ → (x : X ∈ Γ) → (Γ ∖ᴳ x) ⊢ {!!} → (Γ ∖ᴳ x) ⊢ {!!}
-- substˣ = {!!}


-- substᵈ : ∀ {Γ X A} → Γ ⊢ A → (x : X ∈ Γ) → (Γ ∖ᴳ x) ⊢ {!!} → (Γ ∖ᴳ x) ⊢ {!!}
-- substᵈ = {!!}
