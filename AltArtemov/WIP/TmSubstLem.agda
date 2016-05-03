module AltArtemov.WIP.TmSubstLem where

open import Data.Nat using (zero ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; cong₂)

open import AltArtemov.Context
open import AltArtemov.Term
open import AltArtemov.Type
open import AltArtemov.Variable

open import AltArtemov.WIP.TySubst#
open import AltArtemov.WIP.TmSubst




wkᵗ-dist-VAR  : ∀ {g n} → (i : ◌∈ g) → (j : ◌∈ (g ∖ᵍ i)) → VAR[ n ] (wkⁱ i j) ≡ wkᵗ i (VAR[ n ] j)
wkᵗ-dist-VAR i j = refl

wkᵗ-dist-LAM  : ∀ {g n} → (i : ◌∈ g) → (t : ((g ∖ᵍ i) ,◌) ⊢◌) → LAM[ n ] (wkᵗ (pop i) t) ≡ wkᵗ i (LAM[ n ] t)
wkᵗ-dist-LAM i t = refl

wkᵗ-dist-APP  : ∀ {g n} → (i : ◌∈ g) → (t u : (g ∖ᵍ i) ⊢◌) → APP[ n ] (wkᵗ i t) (wkᵗ i u) ≡ wkᵗ i (APP[ n ] t u)
wkᵗ-dist-APP i t u = refl

wkᵗ-dist-PAIR : ∀ {g n} → (i : ◌∈ g) → (t u : (g ∖ᵍ i) ⊢◌) → PAIR[ n ] (wkᵗ i t) (wkᵗ i u) ≡ wkᵗ i (PAIR[ n ] t u)
wkᵗ-dist-PAIR i t u = refl

wkᵗ-dist-FST : ∀ {g n} → (i : ◌∈ g) → (t : (g ∖ᵍ i) ⊢◌) → FST[ n ] (wkᵗ i t) ≡ wkᵗ i (FST[ n ] t)
wkᵗ-dist-FST i t = refl

wkᵗ-dist-SND : ∀ {g n} → (i : ◌∈ g) → (t : (g ∖ᵍ i) ⊢◌) → SND[ n ] (wkᵗ i t) ≡ wkᵗ i (SND[ n ] t)
wkᵗ-dist-SND i t = refl

wkᵗ-dist-UP : ∀ {g n} → (i : ◌∈ g) → (t : (g ∖ᵍ i) ⊢◌) → UP[ n ] (wkᵗ i t) ≡ wkᵗ i (UP[ n ] t)
wkᵗ-dist-UP i t = refl

wkᵗ-dist-DOWN : ∀ {g n} → (i : ◌∈ g) → (t : (g ∖ᵍ i) ⊢◌) → DOWN[ n ] (wkᵗ i t) ≡ wkᵗ i (DOWN[ n ] t)
wkᵗ-dist-DOWN i t = refl

wkᵗ-dist-BOOM : ∀ {g n} → (i : ◌∈ g) → (t : (g ∖ᵍ i) ⊢◌) → BOOM[ n ] (wkᵗ i t) ≡ wkᵗ i (BOOM[ n ] t)
wkᵗ-dist-BOOM i t = refl

wkᵗ-dist-! : ∀ {g} → (i : ◌∈ g) → (t : (g ∖ᵍ i) ⊢◌) → ! wkᵗ i t ≡ wkᵗ i (! t)
wkᵗ-dist-! i t = refl




wkᵗ′-dist-VAR : ∀ {Γ X n} → (x : X ∈ Γ) → (y : ◌∈ ⌊ Γ ∖ᴳ x ⌋ᴳ) → VAR[ n ] (wkⁱ′ x y) ≡ wkᵗ′ x (VAR[ n ] y)
wkᵗ′-dist-VAR x y rewrite ∖-dist x = refl

wkᵗ′-dist-LAM : ∀ {Γ X n B} → (x : X ∈ Γ) → (t : ⌊ Γ ∖ᴳ x , B ⌋ᴳ ⊢◌) → LAM[ n ] (wkᵗ′ (pop {B = B} x) t) ≡ wkᵗ′ x (LAM[ n ] t)
wkᵗ′-dist-LAM x t rewrite ∖-dist x = refl

wkᵗ′-dist-APP : ∀ {Γ X n} → (x : X ∈ Γ) → (t u : ⌊ Γ ∖ᴳ x ⌋ᴳ ⊢◌) → APP[ n ] (wkᵗ′ x t) (wkᵗ′ x u) ≡ wkᵗ′ x (APP[ n ] t u)
wkᵗ′-dist-APP x t u rewrite ∖-dist x = refl

wkᵗ′-dist-PAIR : ∀ {Γ X n} → (x : X ∈ Γ) → (t u : ⌊ Γ ∖ᴳ x ⌋ᴳ ⊢◌) → PAIR[ n ] (wkᵗ′ x t) (wkᵗ′ x u) ≡ wkᵗ′ x (PAIR[ n ] t u)
wkᵗ′-dist-PAIR x t u rewrite ∖-dist x = refl

wkᵗ′-dist-FST : ∀ {Γ X n} → (x : X ∈ Γ) → (t : ⌊ Γ ∖ᴳ x ⌋ᴳ ⊢◌) → FST[ n ] (wkᵗ′ x t) ≡ wkᵗ′ x (FST[ n ] t)
wkᵗ′-dist-FST x t rewrite ∖-dist x = refl

wkᵗ′-dist-SND : ∀ {Γ X n} → (x : X ∈ Γ) → (t : ⌊ Γ ∖ᴳ x ⌋ᴳ ⊢◌) → SND[ n ] (wkᵗ′ x t) ≡ wkᵗ′ x (SND[ n ] t)
wkᵗ′-dist-SND x t rewrite ∖-dist x = refl

wkᵗ′-dist-UP : ∀ {Γ X n} → (x : X ∈ Γ) → (t : ⌊ Γ ∖ᴳ x ⌋ᴳ ⊢◌) → UP[ n ] (wkᵗ′ x t) ≡ wkᵗ′ x (UP[ n ] t)
wkᵗ′-dist-UP x t rewrite ∖-dist x = refl

wkᵗ′-dist-DOWN : ∀ {Γ X n} → (x : X ∈ Γ) → (t : ⌊ Γ ∖ᴳ x ⌋ᴳ ⊢◌) → DOWN[ n ] (wkᵗ′ x t) ≡ wkᵗ′ x (DOWN[ n ] t)
wkᵗ′-dist-DOWN x t rewrite ∖-dist x = refl

wkᵗ′-dist-BOOM : ∀ {Γ X n} → (x : X ∈ Γ) → (t : ⌊ Γ ∖ᴳ x ⌋ᴳ ⊢◌) → BOOM[ n ] (wkᵗ′ x t) ≡ wkᵗ′ x (BOOM[ n ] t)
wkᵗ′-dist-BOOM x t rewrite ∖-dist x = refl

wkᵗ′-dist-! : ∀ {Γ X} → (x : X ∈ Γ) → (t : ⌊ Γ ∖ᴳ x ⌋ᴳ ⊢◌) → ! wkᵗ′ x t ≡ wkᵗ′ x (! t)
wkᵗ′-dist-! x t rewrite ∖-dist x = refl




wkᵛ-dist-VAR : ∀ {g n} → (i : ◌∈ g) → (j : ◌∈ (g ∖ᵍ i)) → VARs[ n ] (wkⁱ i j) ≡ wkᵛ i (VARs[ n ] j)
wkᵛ-dist-VAR {n = zero}  i j = refl
wkᵛ-dist-VAR {n = suc n} i j = cong₂ _∷_ refl (wkᵛ-dist-VAR i j)

wkᵛ-dist-LAM : ∀ {g n} → (i : ◌∈ g) → (ts : Vec ((g ∖ᵍ i) ,◌) n) → LAMs[ n ] (wkᵛ (pop i) ts) ≡ wkᵛ i (LAMs[ n ] ts)
wkᵛ-dist-LAM i []       = refl
wkᵛ-dist-LAM i (t ∷ ts) = cong₂ _∷_ refl (wkᵛ-dist-LAM i ts)

wkᵛ-dist-APP : ∀ {g n} → (i : ◌∈ g) → (ts us : Vec (g ∖ᵍ i) n) → APPs[ n ] (wkᵛ i ts) (wkᵛ i us) ≡ wkᵛ i (APPs[ n ] ts us)
wkᵛ-dist-APP i []       []       = refl
wkᵛ-dist-APP i (t ∷ ts) (u ∷ us) = cong₂ _∷_ refl (wkᵛ-dist-APP i ts us)

wkᵛ-dist-PAIR : ∀ {g n} → (i : ◌∈ g) → (ts us : Vec (g ∖ᵍ i) n) → PAIRs[ n ] (wkᵛ i ts) (wkᵛ i us) ≡ wkᵛ i (PAIRs[ n ] ts us)
wkᵛ-dist-PAIR i []       []       = refl
wkᵛ-dist-PAIR i (t ∷ ts) (u ∷ us) = cong₂ _∷_ refl (wkᵛ-dist-PAIR i ts us)

wkᵛ-dist-FST : ∀ {g n} → (i : ◌∈ g) → (ts : Vec (g ∖ᵍ i) n) → FSTs[ n ] (wkᵛ i ts) ≡ wkᵛ i (FSTs[ n ] ts)
wkᵛ-dist-FST i []       = refl
wkᵛ-dist-FST i (t ∷ ts) = cong₂ _∷_ refl (wkᵛ-dist-FST i ts)

wkᵛ-dist-SND : ∀ {g n} → (i : ◌∈ g) → (ts : Vec (g ∖ᵍ i) n) → SNDs[ n ] (wkᵛ i ts) ≡ wkᵛ i (SNDs[ n ] ts)
wkᵛ-dist-SND i []       = refl
wkᵛ-dist-SND i (t ∷ ts) = cong₂ _∷_ refl (wkᵛ-dist-SND i ts)

wkᵛ-dist-UP : ∀ {g n} → (i : ◌∈ g) → (ts : Vec (g ∖ᵍ i) n) → UPs[ n ] (wkᵛ i ts) ≡ wkᵛ i (UPs[ n ] ts)
wkᵛ-dist-UP i []       = refl
wkᵛ-dist-UP i (t ∷ ts) = cong₂ _∷_ refl (wkᵛ-dist-UP i ts)

wkᵛ-dist-DOWN : ∀ {g n} → (i : ◌∈ g) → (ts : Vec (g ∖ᵍ i) n) → DOWNs[ n ] (wkᵛ i ts) ≡ wkᵛ i (DOWNs[ n ] ts)
wkᵛ-dist-DOWN i []       = refl
wkᵛ-dist-DOWN i (t ∷ ts) = cong₂ _∷_ refl (wkᵛ-dist-DOWN i ts)

wkᵛ-dist-BOOM : ∀ {g n} → (i : ◌∈ g) → (ts : Vec (g ∖ᵍ i) n) → BOOMs[ n ] (wkᵛ i ts) ≡ wkᵛ i (BOOMs[ n ] ts)
wkᵛ-dist-BOOM i []       = refl
wkᵛ-dist-BOOM i (t ∷ ts) = cong₂ _∷_ refl (wkᵛ-dist-BOOM i ts)




wkᵛ′-dist-VAR : ∀ {Γ X n} → (x : X ∈ Γ) → (y : ◌∈ ⌊ Γ ∖ᴳ x ⌋ᴳ) → VARs[ n ] (wkⁱ′ x y) ≡ wkᵛ′ x (VARs[ n ] y)
wkᵛ′-dist-VAR x rewrite ∖-dist x = wkᵛ-dist-VAR ⌊ x ⌋ˣ

wkᵛ′-dist-LAM : ∀ {Γ X n B} → (x : X ∈ Γ) → (ts : Vec ⌊ Γ ∖ᴳ x , B ⌋ᴳ n) → LAMs[ n ] (wkᵛ′ (pop {B = B} x) ts) ≡ wkᵛ′ x (LAMs[ n ] ts)
wkᵛ′-dist-LAM x rewrite ∖-dist x = wkᵛ-dist-LAM ⌊ x ⌋ˣ

wkᵛ′-dist-APP : ∀ {Γ X n} → (x : X ∈ Γ) → (ts us : Vec ⌊ Γ ∖ᴳ x ⌋ᴳ n) → APPs[ n ] (wkᵛ′ x ts) (wkᵛ′ x us) ≡ wkᵛ′ x (APPs[ n ] ts us)
wkᵛ′-dist-APP x rewrite ∖-dist x = wkᵛ-dist-APP ⌊ x ⌋ˣ

wkᵛ′-dist-PAIR : ∀ {Γ X n} → (x : X ∈ Γ) → (ts us : Vec ⌊ Γ ∖ᴳ x ⌋ᴳ n) → PAIRs[ n ] (wkᵛ′ x ts) (wkᵛ′ x us) ≡ wkᵛ′ x (PAIRs[ n ] ts us)
wkᵛ′-dist-PAIR x rewrite ∖-dist x = wkᵛ-dist-PAIR ⌊ x ⌋ˣ

wkᵛ′-dist-FST : ∀ {Γ X n} → (x : X ∈ Γ) → (ts : Vec ⌊ Γ ∖ᴳ x ⌋ᴳ n)
    → FSTs[ n ] (wkᵛ′ x ts) ≡ wkᵛ′ x (FSTs[ n ] ts)
wkᵛ′-dist-FST x rewrite ∖-dist x = wkᵛ-dist-FST ⌊ x ⌋ˣ

wkᵛ′-dist-SND : ∀ {Γ X n} → (x : X ∈ Γ) → (ts : Vec ⌊ Γ ∖ᴳ x ⌋ᴳ n) → SNDs[ n ] (wkᵛ′ x ts) ≡ wkᵛ′ x (SNDs[ n ] ts)
wkᵛ′-dist-SND x rewrite ∖-dist x = wkᵛ-dist-SND ⌊ x ⌋ˣ

wkᵛ′-dist-UP : ∀ {Γ X n} → (x : X ∈ Γ) → (ts : Vec ⌊ Γ ∖ᴳ x ⌋ᴳ n) → UPs[ n ] (wkᵛ′ x ts) ≡ wkᵛ′ x (UPs[ n ] ts)
wkᵛ′-dist-UP x rewrite ∖-dist x = wkᵛ-dist-UP ⌊ x ⌋ˣ

wkᵛ′-dist-DOWN : ∀ {Γ X n} → (x : X ∈ Γ) → (ts : Vec ⌊ Γ ∖ᴳ x ⌋ᴳ n) → DOWNs[ n ] (wkᵛ′ x ts) ≡ wkᵛ′ x (DOWNs[ n ] ts)
wkᵛ′-dist-DOWN x rewrite ∖-dist x = wkᵛ-dist-DOWN ⌊ x ⌋ˣ

wkᵛ′-dist-BOOM : ∀ {Γ X n} → (x : X ∈ Γ) → (ts : Vec ⌊ Γ ∖ᴳ x ⌋ᴳ n)
    → BOOMs[ n ] (wkᵛ′ x ts) ≡ wkᵛ′ x (BOOMs[ n ] ts)
wkᵛ′-dist-BOOM x rewrite ∖-dist x = wkᵛ-dist-BOOM ⌊ x ⌋ˣ






postulate
  oops′ : ∀ {g} → (i : ◌∈ g) → (A : Ty ∅)
      → wkᴬ i (wkᴬ* A) ≡ wkᴬ* A

  oops  : ∀ {g} → (i : ◌∈ g) → (A : Ty ∅)
      → wkᴬ {g} i (wkᴬ* {g ∖ᵍ i} A) ≡ wkᴬ* {g} A





wkᴬ-lem1 : ∀ {g n} → (i : ◌∈ g) → (ts : Vec (g ∖ᵍ i) n) → (A : Ty ∅)
    → wkᴬ i (ts ∴ A) ≡ wkᵛ i ts ∴ A
wkᴬ-lem1 i []       A = oops i A
wkᴬ-lem1 i (t ∷ ts) A = cong (wkᵗ i t ∶_) (wkᴬ-lem1 i ts A)


wkᴬ′-lem1 : ∀ {Γ X n} → (x : X ∈ Γ) → (ts : Vec ⌊ Γ ∖ᴳ x ⌋ᴳ n) → (A : Ty ∅)
    → wkᴬ′ x (ts ∴ A) ≡ wkᵛ′ x ts ∴ A
wkᴬ′-lem1 x ts rewrite ∖-dist x = wkᴬ-lem1 ⌊ x ⌋ˣ ts



wkᴬ-dist-FST : ∀ {g n} → (i : ◌∈ g) → (ts : Vec (g ∖ᵍ i) n) → (A : Ty ∅)
    → wkᴬ i (FSTs[ n ] ts ∴ A) ≡ FSTs[ n ] (wkᵛ i ts) ∴ A
wkᴬ-dist-FST i []       A = oops i A
wkᴬ-dist-FST i (t ∷ ts) A = cong (FST[ _ ] (wkᵗ i t) ∶_) (wkᴬ-dist-FST i ts A)



-- wkᵈ : ∀ {Γ X} → (x : X ∈ Γ) → {A : Ty ⌊ Γ ∖ᴳ x ⌋ᴳ} → {A′ : Ty ⌊ Γ ⌋ᴳ}
--     → (Γ ∖ᴳ x) ⊢ A
--     → {{_ : wkᴬ′ x A ≡ A′}}
--     → Γ ⊢ A′
-- wkᵈ x (var[ n ] {A} y {{refl}})                  {{refl}} = {!!}
-- wkᵈ x (lam[ n ] {ts} {A} {B} d {{refl}})         {{refl}} = {!!}
-- wkᵈ x (app[ n ] {ts} {us} {A} {B} d e {{refl}})  {{refl}} = {!!}
-- wkᵈ x (pair[ n ] {ts} {us} {A} {B} d e {{refl}}) {{refl}} = {!!}
-- wkᵈ x (fst[ n ] {ts} {A} {B} d {{refl}})         {{refl}} =
--   fst[ n ] {wkᵛ′ x ts} {A} {B} (wkᵈ x d {{{!!}}}) {{{!refl!}}}
-- wkᵈ x (snd[ n ] {ts} {A} {B} d {{refl}})         {{refl}} = {!!}
-- wkᵈ x (up[ n ] {ts} {s} {A} d {{refl}})          {{refl}} = {!!}
-- wkᵈ x (down[ n ] {ts} {s} {A} d {{refl}})        {{refl}} = {!!}
-- wkᵈ x (boom[ n ] {ts} {A} d {{refl}})            {{refl}} = {!!}


-- -- substˣ : ∀ {Γ X A} → ℕ → A ∈ Γ → (x : X ∈ Γ) → (Γ ∖ᴳ x) ⊢ {!!} → (Γ ∖ᴳ x) ⊢ {!!}
-- -- substˣ = {!!}


-- -- substᵈ : ∀ {Γ X A} → Γ ⊢ A → (x : X ∈ Γ) → (Γ ∖ᴳ x) ⊢ {!!} → (Γ ∖ᴳ x) ⊢ {!!}
-- -- substᵈ = {!!}
