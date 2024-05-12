{-# OPTIONS --allow-unsolved-metas #-}

module Try2.AltArtemov.Term.Substitution2 where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Try2.AltArtemov.Context
open import Try2.AltArtemov.Type
open import Try2.AltArtemov.Term.Core
open import Try2.AltArtemov.Term.Representation
open import Try2.AltArtemov.Variable

open import Try2.AltArtemov.WIP.TySubst#


-- weak : ∀ {Γ A} → (Γ , A) ≳ᴳ Γ
-- weak = skip ≳ᴳ-refl

mapˣ : ∀ {Γ Γ′ A} → Γ ≳ᴳ Γ′ → A ∈ Γ′ → A ∈ Γ
mapˣ done     x       = x
mapˣ (skip p) x       = pop (mapˣ p x)
mapˣ (keep p) top     = top
mapˣ (keep p) (pop x) = pop (mapˣ p x)

mapᵗ : ∀ {Γ Γ′ A} → (p : Γ ≳ᴳ Γ′) → Γ′ ⊢ A → Γ ⊢ {!mapᴬ (≳ᴳ⇒≳ᵍ p) A!}
--mapᵗ : ∀ {Γ Γ′ A A′} → (p : Γ ≳ᴳ Γ′) → Γ′ ⊢ A → {{_ : mapᴬ (≳ᴳ-proj p) A ≡ A′}} → Γ ⊢ A′
mapᵗ p (var[ n ] v)    = var[ n ] (mapˣ p v)
mapᵗ p (lam[ n ] t)    = lam[ n ] (mapᵗ (keep p) t)
mapᵗ p (app[ n ] t u)  = app[ n ] (mapᵗ p t) (mapᵗ p u)
mapᵗ p (pair[ n ] t u) = pair[ n ] (mapᵗ p t) (mapᵗ p u)
mapᵗ p (fst[ n ] t)    = fst[ n ] (mapᵗ p t)
mapᵗ p (snd[ n ] t)    = snd[ n ] (mapᵗ p t)
mapᵗ p (up[ n ] t)     = up[ n ] (mapᵗ p t)
mapᵗ p (down[ n ] t)   = down[ n ] (mapᵗ p t)
mapᵗ p (boom[ n ] t)   = boom[ n ] (mapᵗ p t)



_∖ᴳ_ : ∀ {X} → (Γ : Cx) → X ∈ Γ → Cx
∅       ∖ᴳ ()
(Γ , A) ∖ᴳ top   = Γ
(Γ , B) ∖ᴳ pop x = Γ ∖ᴳ x , B


wkˣ : ∀ {Γ X A} → (x : X ∈ Γ) → A ∈ (Γ ∖ᴳ x) → A ∈ Γ
wkˣ top     y       = pop y
wkˣ (pop x) top     = top
wkˣ (pop x) (pop y) = pop (wkˣ x y)


data _≈ˣ_ {Γ : Cx} {A : Ty ∅} : A ∈ Γ → A ∈ Γ → Set where
  same : {x : A ∈ Γ} → x ≈ˣ x
  diff : (x : A ∈ Γ) → (y : A ∈ (Γ ∖ᴳ x)) → x ≈ˣ wkˣ x y


_≈?ˣ_ : ∀ {Γ A} → (x y : A ∈ Γ) → x ≈ˣ y
top   ≈?ˣ top            = same
top   ≈?ˣ pop y          = diff top y
pop x ≈?ˣ top            = diff (pop x) top
pop x ≈?ˣ pop y          with x ≈?ˣ y
pop y ≈?ˣ pop .y         | same = same
pop x ≈?ˣ pop .(wkˣ x y) | diff .x y = diff (pop x) (pop y)


data _≈ˣ′_ {Γ : Cx} : ∀ {A B} → A ∈ Γ → B ∈ Γ → Set where
  same : ∀ {A} {x : A ∈ Γ} → x ≈ˣ′ x
  diff : ∀ {A B} (x : A ∈ Γ) → (y : B ∈ (Γ ∖ᴳ x)) → x ≈ˣ′ wkˣ x y

_≈?ˣ′_ : ∀ {Γ A A′} → (x : A ∈ Γ) → (y : A′ ∈ Γ) → x ≈ˣ′ y
top   ≈?ˣ′ top            = same
top   ≈?ˣ′ pop y          = diff top y
pop x ≈?ˣ′ top            = diff (pop x) top
pop x ≈?ˣ′ pop y          with x ≈?ˣ′ y
pop y ≈?ˣ′ pop .y         | same = same
pop x ≈?ˣ′ pop .(wkˣ x y) | diff .x y = diff (pop x) (pop y)


-- TODO
