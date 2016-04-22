module Experiments.FishAndChips where

open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; subst)

open import AltArtemov


-- Type of simultaneous renamings.

Ren : Cx → Cx → Set
Ren Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A


-- Type of simultaneous substitutions.

Sub : Cx → Cx → Set
Sub Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A


-- Context extension.

_⊂+_ : Cx → List Ty → Cx
Γ ⊂+ []       = Γ
Γ ⊂+ (A ∷ As) = (Γ , A) ⊂+ As


-- Type of shiftable simultaneous substitutions.

Shub : Cx → Cx → Set
Shub Γ Δ = ∀ As → Sub (Γ ⊂+ As) (Δ ⊂+ As)


-- Substitution.

postulate
  [_/_] : ∀ {Γ Δ} (θ : Shub Γ Δ) {A} → Γ ⊢ A → Δ ⊢ A

-- TODO
{-[ θ / var[ n ] i ]   = {!θ [] i!}
[ θ / lam[ n ] t ]   = lam[ n ] [ θ ∘ {!!} / t ]
[ θ / app[ n ] t s ] = app[ n ] [ θ / t ] [ θ / s ]
[ θ / up[ n ] t ]    = up[ n ] [ θ / t ]
[ θ / down[ n ] t ]  = down[ n ] [ θ / t ]-}


-- Any simultaneous renaming can be shiftable.

wkr : ∀ {Γ Δ A} → Ren Γ Δ → Ren (Γ , A) (Δ , A)
wkr ρ top      = top
wkr ρ (pop i)  = pop (ρ i)

ren : ∀ {Γ Δ} → Ren Γ Δ → Shub Γ Δ
ren ρ []       = var ∘ ρ
ren ρ (_ ∷ As) = ren (wkr ρ) As


-- Any simultaneous substitution can be shiftable.

wks : ∀ {Γ Δ A} → Sub Γ Δ → Sub (Γ , A) (Δ , A)
wks σ top      = var top
wks σ (pop i)  = [ ren pop / σ i ]

sub : ∀ {Γ Δ} → Sub Γ Δ → Shub Γ Δ
sub σ []       = σ
sub σ (_ ∷ As) = sub (wks σ) As


-- Renaming that shifts past any context extension.

weak : ∀ {Γ} (As : List Ty) → Ren Γ (Γ ⊂+ As)
weak []       i = i
weak (_ ∷ As) i = weak As (pop i)

wix : ∀ {Γ A} (As : List Ty) → Γ ∋ A → ℕ
wix As i = ix (weak As i)


-- Reverse context extension.

_+⊐_ : Cx → List Ty → List Ty
∅       +⊐ As = As
(Γ , A) +⊐ As = Γ +⊐ (A ∷ As)


-- TODO

THIS_IS_PLUS : Cx → Cx → List Ty → Set
THIS_IS_PLUS Δ Γ As = Δ +⊐ [] ≡ Γ +⊐ As

this_is_plus : ∀ Δ Γ (As : List Ty) {{q : THIS Δ IS Γ PLUS As}} → Γ ⊂+ As ≡ Δ
this_is_plus Δ (Γ , A) As         {{q}}    = this Δ is Γ plus (A ∷ As) {{q}}
this_is_plus Δ ∅       .(Δ +⊐ []) {{refl}} = aux Δ []
  where
    aux : ∀ Δ (As : List Ty) → ∅ ⊂+ (Δ +⊐ As) ≡ Δ ⊂+ As
    aux ∅       As = refl
    aux (Δ , A) As = aux Δ (A ∷ As)


lam*[_] : ∀ n {ts : Tms n} {A B Γ}
    → ((∀ {Δ} {As} {{q : THIS Δ IS Γ PLUS (A ∷ As)}}
            → Δ ⊢ VARs[ n ] (wix As top) ∶⋯∶ A)
        → Γ , A ⊢ ts ∶⋯∶ B)
    → Γ ⊢ LAMs[ n ] ts ∶⋯∶ (A ⊃ B)
lam*[ n ] {A = A} {Γ = Γ} f =
    lam[ n ] (f (λ {Δ} {As} {{q}}
        → subst (λ Γ → Γ ⊢ VARs[ n ] (wix As top) ∶⋯∶ A)
                 (this Δ is Γ plus (A ∷ As))
                 (var[ n ] (weak As top))))


lam* : ∀ {A B Γ}
    → ((∀ {Δ} {As} {{q : THIS Δ IS Γ PLUS (A ∷ As)}} → Δ ⊢ A) → Γ , A ⊢ B)
    → Γ ⊢ A ⊃ B
lam* = lam*[ 0 ] {[]}

syntax lam* (λ x → y) = fun x ⇒ y


lam*² : ∀ {t A B Γ}
    → ((∀ {Δ} {As} {{q : THIS Δ IS Γ PLUS (A ∷ As)}}
            → Δ ⊢ VAR (wix As top) ∶ A)
        → Γ , A ⊢ t ∶ B)
    → Γ ⊢ LAM t ∶ (A ⊃ B)
lam*² {t} = lam*[ 1 ] {t ∷ []}

syntax lam*² (λ x → y) = fun² x ⇒ y


lam*³ : ∀ {t₂ t A B Γ}
    → ((∀ {Δ} {As} {{q : THIS Δ IS Γ PLUS (A ∷ As)}}
            → Δ ⊢ VAR² (wix As top) ∶ VAR (wix As top) ∶ A)
        → Γ , A ⊢ t₂ ∶ t ∶ B)
    → Γ ⊢ LAM² t₂ ∶ LAM t ∶ (A ⊃ B)
lam*³ {t₂} {t} = lam*[ 2 ] {t₂ ∷ t ∷ []}

syntax lam*³ (λ x → y) = fun³ x ⇒ y


lam*⁴ : ∀ {t₃ t₂ t A B Γ}
    → ((∀ {Δ} {As} {{q : THIS Δ IS Γ PLUS (A ∷ As)}}
            → Δ ⊢ VAR³ (wix As top) ∶ VAR² (wix As top) ∶ VAR (wix As top) ∶ A)
        → Γ , A ⊢ t₃ ∶ t₂ ∶ t ∶ B)
    → Γ ⊢ LAM³ t₃ ∶ LAM² t₂ ∶ LAM t ∶ (A ⊃ B)
lam*⁴ {t₃} {t₂} {t} = lam*[ 3 ] {t₃ ∷ t₂ ∷ t ∷ []}

syntax lam*⁴ (λ x → y) = fun⁴ x ⇒ y
