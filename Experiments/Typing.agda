module Experiments.Typing where

open import Data.Empty using () renaming (⊥ to Empty ; ⊥-elim to boom)
open import Data.Maybe using (Maybe ; just ; nothing ; map)
open import Data.Nat using (ℕ ; zero ; suc)
open import Function using (const)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Nullary using (yes ; no)

open import AltArtemov
open import Data.Maybe.Missing


lookup : ∀ (Γ : Cx) (i : ℕ) → Maybe Ty
lookup ∅       i       = nothing
lookup (Γ , A) zero    = just A
lookup (Γ , B) (suc i) = lookup Γ i


locate : ∀ (Γ : Cx) (i : ℕ) (A : Ty) → Maybe (Γ ∋ A)
locate ∅       i       A  = nothing
locate (Γ , A) zero    ?A with A Ty≟ ?A
locate (Γ , A) zero    .A | yes refl = just top
...                       | no _     = nothing
locate (Γ , B) (suc i) A  = map pop (locate Γ i A)


mutual
  infer : ∀ (Γ : Cx) (t : Tm) → Maybe Ty    -- TODO: Perhaps return inferred derivation; Σ Ty (λ A → Γ ⊢ A).
  infer Γ (VAR[ 0 ] i)   = lookup Γ i
  infer Γ (LAM[ 0 ] t)   = nothing    -- TODO: Can we do better here?
  infer Γ (APP[ 0 ] t s) with infer Γ t
  ...                    | just (A ⊃ B) = map (const B) (check Γ s A)
  ...                    | _            = nothing
  infer Γ (UP[ 0 ] t)    with infer Γ t
  ...                    | just (u ∶ A) = just (quo u ∶ u ∶ A)
  ...                    | _            = nothing
  infer Γ (DOWN[ 0 ] t)  with infer Γ t
  ...                    | just (u ∶ A) = just A
  ...                    | _            = nothing
  infer Γ _              = nothing

  check : ∀ (Γ : Cx) (t : Tm) (A : Ty) → Maybe (Γ ⊢ A)
  check Γ (VAR[ 0 ] i)   A                  = map var (locate Γ i A)    -- TODO: Use infer here.
  check Γ (LAM[ 0 ] t)   (A ⊃ B)            = map lam (check (Γ , A) t B)
  check Γ (LAM[ 0 ] t)   _                  = nothing
  check Γ (APP[ 0 ] t s) B                  with infer Γ t    -- TODO: Avoid rechecking t.
  ...                                       | just (A ⊃ B′) with B Ty≟ B′
  check Γ (APP[ 0 ] t s) B                  | just (A ⊃ .B) | yes refl = map₂ app (check Γ t (A ⊃ B)) (check Γ s A)
  ...                                                       | no _     = nothing
  check Γ (APP[ 0 ] t s) B                  | _             = nothing
  check Γ (UP[ 0 ] t)    (q ∶ u ∶ A)        with (quo u) Tm≟ q
  check Γ (UP[ 0 ] t)    (.(quo u) ∶ u ∶ A) | yes refl = map up (check Γ t (u ∶ A))
  ...                                       | no _     = nothing
  check Γ (UP[ 0 ] t)    _                  = nothing
  check Γ (DOWN[ 0 ] t)  A                  with infer Γ t    -- TODO: Avoid rechecking t.
  ...                                       | just (u ∶ A′) with A Ty≟ A′
  check Γ (DOWN[ 0 ] t)  A                  | just (u ∶ .A) | yes refl = map down (check Γ t (u ∶ A))
  ...                                                       | no _     = nothing
  check Γ (DOWN[ 0 ] t)  A                  | _             = nothing
  check Γ _              _                  = nothing


-- TODO: Perhaps do this instead:
-- check : (Γ : Ctx) (t : Tm) (A : Ty) -> Maybe (Γ ⊢ t ∶ A)
-- infer : (Γ : Ctx) (t : Tm) -> Maybe (Σ Ty (λ A → Γ ⊢ t ∶ A))


module Example where
  open import Examples.AltArtemov

  pI : ∀ {A} → rep (I {A}) ≡ LAM V0
  pI = refl

  tI : ∀ {A} → ty (I {A}) ≡ (A ⊃ A)
  tI = refl


  false_rec : (A : Set) → Empty → A
  false_rec A ()

  postulate
    ugh : ∀ Γ A → locate (Γ , A) zero A ≡ just top    -- TODO: Remove this.

  zI : ∀ {A} → check ∅ (rep (I {A})) (ty (I {A})) ≡ just (I {A})
  zI {A} rewrite ugh ∅ A = refl
