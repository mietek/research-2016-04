module AltArtemov.WIP.TmSubstLem where

open import Data.Nat using (zero ; suc)
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
  oops : ∀ {g A} → (i : ◌∈ g) → wkᴬ* {g} A ≡ wkᴬ {g} i (wkᴬ* {g ∖ᵍ i} A)


wk-dist-VAR : ∀ {g n A} → (i : ◌∈ g) → (j : ◌∈ (g ∖ᵍ i))
    → VARs[ n ] (wkⁱ i j) ∴ A ≡ wkᴬ i (VARs[ n ] j ∴ A)
wk-dist-VAR {n = zero}  i j = oops i
wk-dist-VAR {n = suc n} i j = cong (VAR[ n ] (wkⁱ i j) ∶_) (wk-dist-VAR {n = n} i j)

wk-dist-LAM : ∀ {g n A} → (i : ◌∈ g) → (ts : Vec ((g ∖ᵍ i) ,◌) n)
    → LAMs[ n ] (wkᵛ (pop i) ts) ∴ A ≡ wkᴬ i (LAMs[ n ] ts ∴ A)
wk-dist-LAM i []       = oops i
wk-dist-LAM i (t ∷ ts) = cong (LAM[ _ ] (wkᵗ (pop i) t) ∶_) (wk-dist-LAM i ts)

wk-dist-APP : ∀ {g n A} → (i : ◌∈ g) → (ts us : Vec (g ∖ᵍ i) n)
    → APPs[ n ] (wkᵛ i ts) (wkᵛ i us) ∴ A ≡ wkᴬ i (APPs[ n ] ts us ∴ A)
wk-dist-APP i []       []       = oops i
wk-dist-APP i (t ∷ ts) (u ∷ us) = cong (APP[ _ ] (wkᵗ i t) (wkᵗ i u) ∶_) (wk-dist-APP i ts us)

wk-dist-PAIR : ∀ {g n A} → (i : ◌∈ g) → (ts us : Vec (g ∖ᵍ i) n)
    → PAIRs[ n ] (wkᵛ i ts) (wkᵛ i us) ∴ A ≡ wkᴬ i (PAIRs[ n ] ts us ∴ A)
wk-dist-PAIR i []       []       = oops i
wk-dist-PAIR i (t ∷ ts) (u ∷ us) = cong (PAIR[ _ ] (wkᵗ i t) (wkᵗ i u) ∶_) (wk-dist-PAIR i ts us)

wk-dist-FST : ∀ {g n A} → (i : ◌∈ g) → (ts : Vec (g ∖ᵍ i) n)
    → FSTs[ n ] (wkᵛ i ts) ∴ A ≡ wkᴬ i (FSTs[ n ] ts ∴ A)
wk-dist-FST i []       = oops i
wk-dist-FST i (t ∷ ts) = cong (FST[ _ ] (wkᵗ i t) ∶_) (wk-dist-FST i ts)

wk-dist-SND : ∀ {g n A} → (i : ◌∈ g) → (ts : Vec (g ∖ᵍ i) n)
    → SNDs[ n ] (wkᵛ i ts) ∴ A ≡ wkᴬ i (SNDs[ n ] ts ∴ A)
wk-dist-SND i []       = oops i
wk-dist-SND i (t ∷ ts) = cong (SND[ _ ] (wkᵗ i t) ∶_) (wk-dist-SND i ts)

wk-dist-UP : ∀ {g n A} → (i : ◌∈ g) → (ts : Vec (g ∖ᵍ i) n)
    → UPs[ n ] (wkᵛ i ts) ∴ A ≡ wkᴬ i (UPs[ n ] ts ∴ A)
wk-dist-UP i []       = oops i
wk-dist-UP i (t ∷ ts) = cong (UP[ _ ] (wkᵗ i t) ∶_) (wk-dist-UP i ts)

wk-dist-DOWN : ∀ {g n A} → (i : ◌∈ g) → (ts : Vec (g ∖ᵍ i) n)
    → DOWNs[ n ] (wkᵛ i ts) ∴ A ≡ wkᴬ i (DOWNs[ n ] ts ∴ A)
wk-dist-DOWN i []       = oops i
wk-dist-DOWN i (t ∷ ts) = cong (DOWN[ _ ] (wkᵗ i t) ∶_) (wk-dist-DOWN i ts)

wk-dist-BOOM : ∀ {g n A} → (i : ◌∈ g) → (ts : Vec (g ∖ᵍ i) n)
    → BOOMs[ n ] (wkᵛ i ts) ∴ A ≡ wkᴬ i (BOOMs[ n ] ts ∴ A)
wk-dist-BOOM i []       = oops i
wk-dist-BOOM i (t ∷ ts) = cong (BOOM[ _ ] (wkᵗ i t) ∶_) (wk-dist-BOOM i ts)


wk-dist-VAR′ : ∀ {Γ X n A} → (x : X ∈ Γ) → (j : ◌∈ ⌊ Γ ∖ᴳ x ⌋ᴳ)
    → VARs[ n ] (wkⁱ′ x j) ∴ A ≡ wkᴬ′ x (VARs[ n ] j ∴ A)
wk-dist-VAR′ {n = n} x rewrite ∖-dist x = wk-dist-VAR {n = n} ⌊ x ⌋ˣ

wk-dist-LAM′ : ∀ {Γ X n A B} → (x : X ∈ Γ) → (ts : Vec ⌊ Γ ∖ᴳ x , B ⌋ᴳ n)
    → LAMs[ n ] (wkᵛ′ (pop {B = B} x) ts) ∴ A ≡ wkᴬ′ x (LAMs[ n ] ts ∴ A)
wk-dist-LAM′ x rewrite ∖-dist x = wk-dist-LAM ⌊ x ⌋ˣ

wk-dist-APP′ : ∀ {Γ X n A} → (x : X ∈ Γ) → (ts us : Vec ⌊ Γ ∖ᴳ x ⌋ᴳ n)
    → APPs[ n ] (wkᵛ′ x ts) (wkᵛ′ x us) ∴ A ≡ wkᴬ′ x (APPs[ n ] ts us ∴ A)
wk-dist-APP′ x rewrite ∖-dist x = wk-dist-APP ⌊ x ⌋ˣ

wk-dist-PAIR′ : ∀ {Γ X n A} → (x : X ∈ Γ) → (ts us : Vec ⌊ Γ ∖ᴳ x ⌋ᴳ n)
    → PAIRs[ n ] (wkᵛ′ x ts) (wkᵛ′ x us) ∴ A ≡ wkᴬ′ x (PAIRs[ n ] ts us ∴ A)
wk-dist-PAIR′ x rewrite ∖-dist x = wk-dist-PAIR ⌊ x ⌋ˣ

wk-dist-FST′ : ∀ {Γ X n A} → (x : X ∈ Γ) → (ts : Vec ⌊ Γ ∖ᴳ x ⌋ᴳ n)
    → FSTs[ n ] (wkᵛ′ x ts) ∴ A ≡ wkᴬ′ x (FSTs[ n ] ts ∴ A)
wk-dist-FST′ x rewrite ∖-dist x = wk-dist-FST ⌊ x ⌋ˣ

wk-dist-SND′ : ∀ {Γ X n A} → (x : X ∈ Γ) → (ts : Vec ⌊ Γ ∖ᴳ x ⌋ᴳ n)
    → SNDs[ n ] (wkᵛ′ x ts) ∴ A ≡ wkᴬ′ x (SNDs[ n ] ts ∴ A)
wk-dist-SND′ x rewrite ∖-dist x = wk-dist-SND ⌊ x ⌋ˣ

wk-dist-UP′ : ∀ {Γ X n A} → (x : X ∈ Γ) → (ts : Vec ⌊ Γ ∖ᴳ x ⌋ᴳ n)
    → UPs[ n ] (wkᵛ′ x ts) ∴ A ≡ wkᴬ′ x (UPs[ n ] ts ∴ A)
wk-dist-UP′ x rewrite ∖-dist x = wk-dist-UP ⌊ x ⌋ˣ

wk-dist-DOWN′ : ∀ {Γ X n A} → (x : X ∈ Γ) → (ts : Vec ⌊ Γ ∖ᴳ x ⌋ᴳ n)
    → DOWNs[ n ] (wkᵛ′ x ts) ∴ A ≡ wkᴬ′ x (DOWNs[ n ] ts ∴ A)
wk-dist-DOWN′ x rewrite ∖-dist x = wk-dist-DOWN ⌊ x ⌋ˣ

wk-dist-BOOM′ : ∀ {Γ X n A} → (x : X ∈ Γ) → (ts : Vec ⌊ Γ ∖ᴳ x ⌋ᴳ n)
    → BOOMs[ n ] (wkᵛ′ x ts) ∴ A ≡ wkᴬ′ x (BOOMs[ n ] ts ∴ A)
wk-dist-BOOM′ x rewrite ∖-dist x = wk-dist-BOOM ⌊ x ⌋ˣ


postulate
  oops2 : ∀ {Γ X A} → (x : X ∈ Γ) → (y : A ∈ (Γ ∖ᴳ x)) → ⌊ wkˣ x y ⌋ˣ ≡ wkⁱ′ x ⌊ y ⌋ˣ


wk-dist-VAR″ : ∀ {Γ n X A} → (x : X ∈ Γ) → (y : A ∈ (Γ ∖ᴳ x))
    → VARs[ n ] ⌊ wkˣ x y ⌋ˣ ∴ A ≡ wkᴬ′ x (VARs[ n ] ⌊ y ⌋ˣ ∴ A)
wk-dist-VAR″ {n = n} x y rewrite oops2 x y = wk-dist-VAR′ {n = n} x ⌊ y ⌋ˣ


wk-dist-vec : ∀ {g n A} → (i : ◌∈ g) → (ts : Vec (g ∖ᵍ i) n)
    → wkᴬ i (ts ∴ A) ≡ wkᵛ i ts ∴ A
wk-dist-vec i []       = sym (oops i)
wk-dist-vec i (t ∷ ts) = cong (wkᵗ i t ∶_) (wk-dist-vec i ts)


wk-dist-vec′ : ∀ {Γ X n A} → (x : X ∈ Γ) → (ts : Vec ⌊ Γ ∖ᴳ x ⌋ᴳ n)
    → wkᴬ′ x (ts ∴ A) ≡ wkᵛ′ x ts ∴ A
wk-dist-vec′ x rewrite ∖-dist x = wk-dist-vec ⌊ x ⌋ˣ


wkᵈ : ∀ {Γ X} → (x : X ∈ Γ) → {A : Ty ⌊ Γ ∖ᴳ x ⌋ᴳ} → {A′ : Ty ⌊ Γ ⌋ᴳ}
    → (Γ ∖ᴳ x) ⊢ A
    → {{_ : wkᴬ′ x A ≡ A′}}
    → Γ ⊢ A′

wkᵈ x (var[ n ] {A} y {{refl}}) {{refl}} rewrite oops2 x y =
    var[ n ] (wkˣ x y) {{wk-dist-VAR″ {n = n} x y}}

wkᵈ x (lam[ n ] {A} {ts} {B} d {{refl}}) {{refl}} =
    lam[ n ] (wkᵈ (pop x) d {{wk-dist-vec′ (pop x) ts}}) {{wk-dist-LAM′ x ts}}

wkᵈ x (app[ n ] {ts} {us} {A} {B} d e {{refl}}) {{refl}} =
    app[ n ] (wkᵈ x d {{wk-dist-vec′ x ts}}) (wkᵈ x e {{wk-dist-vec′ x us}}) {{wk-dist-APP′ x ts us}}

wkᵈ x (pair[ n ] {ts} {us} {A} {B} d e {{refl}}) {{refl}} =
    pair[ n ] (wkᵈ x d {{wk-dist-vec′ x ts}}) (wkᵈ x e {{wk-dist-vec′ x us}}) {{wk-dist-PAIR′ x ts us}}

wkᵈ x (fst[ n ] {ts} {A} {B} d {{refl}}) {{refl}} =
    fst[ n ] (wkᵈ x d {{wk-dist-vec′ x ts}}) {{wk-dist-FST′ x ts}}

wkᵈ x (snd[ n ] {ts} {A} {B} d {{refl}}) {{refl}} =
    snd[ n ] (wkᵈ x d {{wk-dist-vec′ x ts}}) {{wk-dist-SND′ x ts}}

wkᵈ x (up[ n ] {ts} {s} {A} d {{refl}}) {{refl}} =
    up[ n ] (wkᵈ x d {{wk-dist-vec′ x ts}}) {{wk-dist-UP′ x ts}}

wkᵈ x (down[ n ] {ts} {s} {A} d {{refl}}) {{refl}} =
    down[ n ] (wkᵈ x d {{wk-dist-vec′ x ts}}) {{wk-dist-DOWN′ x ts}}

wkᵈ x (boom[ n ] {ts} {A} d {{refl}}) {{refl}} =
    boom[ n ] (wkᵈ x d {{wk-dist-vec′ x ts}}) {{wk-dist-BOOM′ x ts}}


-- substˣ : ∀ {Γ X A} → ℕ → A ∈ Γ → (x : X ∈ Γ) → (Γ ∖ᴳ x) ⊢ {!!} → (Γ ∖ᴳ x) ⊢ {!!}
-- substˣ = {!!}


-- substᵈ : ∀ {Γ X A} → Γ ⊢ A → (x : X ∈ Γ) → (Γ ∖ᴳ x) ⊢ {!!} → (Γ ∖ᴳ x) ⊢ {!!}
-- substᵈ = {!!}
