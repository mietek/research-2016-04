module AltArtemov.Term.Substitution where

open import AltArtemov.Context
open import AltArtemov.Type
open import AltArtemov.Variable


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
