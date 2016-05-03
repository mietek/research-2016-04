module AltArtemov.WIP.TmSubst# where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ ; suc)
open import Data.Fin using (Fin ; zero ; suc)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; sym ; subst)
open import Relation.Nullary using (yes ; no)

open import AltArtemov.Context
open import AltArtemov.Term.Core
open import AltArtemov.Term.Representation
open import AltArtemov.Type
open import AltArtemov.Variable
open import Data.Fin.Missing

open import AltArtemov.Term.Substitution
open import AltArtemov.WIP.TmRSubst#
open import AltArtemov.WIP.TmSubst
open import AltArtemov.WIP.TySubst#


_∖ᴳ#_ : (Γ : Cx) → Fin (suc ⌊ Γ ⌋ᴳ′) → Cx
Γ       ∖ᴳ# zero   = Γ
∅       ∖ᴳ# suc ()
(Γ , A) ∖ᴳ# suc k  = ((Γ , A) ∖ᴳ top) ∖ᴳ# k


_↦∅ᴳ : (Γ : Cx) → ∅ ≡ Γ ∖ᴳ# sup ⌊ Γ ⌋ᴳ′
∅       ↦∅ᴳ = refl
(Γ , _) ↦∅ᴳ = Γ ↦∅ᴳ


wkˣ# : ∀ {Γ A} → (k : Fin (suc ⌊ Γ ⌋ᴳ′)) → A ∈ (Γ ∖ᴳ# k) → A ∈ Γ
wkˣ# {Γ}     {A}  zero     x = x
wkˣ# {∅}     {A}  (suc ()) x
wkˣ# {Γ , B} {A}  (suc k)  x with A ≟ᴬ B
wkˣ# {Γ , A} {.A} (suc k)  x | yes refl = top
wkˣ# {Γ , B} {A}  (suc k)  x | no  A≢B  = pop (wkˣ# k x)


wkˣ* : ∀ {Γ A} → A ∈ ∅ → A ∈ Γ
wkˣ* ()


∖#-dist : ∀ {Γ} → (k : Fin (suc ⌊ Γ ⌋ᴳ′)) → ⌊ Γ ∖ᴳ# k ⌋ᴳ ≡ ⌊ Γ ⌋ᴳ ∖ᵍ# k
∖#-dist zero             = refl
∖#-dist {∅}     (suc ())
∖#-dist {Γ , _} (suc k)  = ∖#-dist k


wkⁱ#′ : ∀ {Γ} → (k : Fin (suc ⌊ Γ ⌋ᴳ′)) → ◌∈ ⌊ Γ ∖ᴳ# k ⌋ᴳ → ◌∈ ⌊ Γ ⌋ᴳ
wkⁱ#′ k rewrite ∖#-dist k = wkⁱ# k


wkᵗ#′ : ∀ {Γ} → (k : Fin (suc ⌊ Γ ⌋ᴳ′)) → ⌊ Γ ∖ᴳ# k ⌋ᴳ ⊢◌ → ⌊ Γ ⌋ᴳ ⊢◌
wkᵗ#′ k rewrite ∖#-dist k = wkᵗ# k


wkᴬ#′ : ∀ {Γ} → (k : Fin (suc ⌊ Γ ⌋ᴳ′)) → Ty ⌊ Γ ∖ᴳ# k ⌋ᴳ → Ty ⌊ Γ ⌋ᴳ
wkᴬ#′ k rewrite ∖#-dist k = wkᴬ# k
