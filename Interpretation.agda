module Interpretation where

open import Data.Empty using () renaming (⊥ to Empty ; ⊥-elim to expl)
open import Data.Nat using (ℕ ; zero ; suc ; _≤′_ ; _<′_ ; _⊓_)
open import Data.Product using (_,_ ; _×_)
open import Data.Unit using () renaming (⊤ to Unit ; tt to unit)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import AltArtemov
open import AltArtemov.Type.Properties using () renaming (z<′lev-t∶A to z<′ty-lev-t∶A)
open import Data.Nat.Missing


⟦_⟧ty : ∀ (A : Ty) → Set
⟦ ⊥ ⟧ty    = Empty
⟦ A ⊃ B ⟧ty = ⟦ A ⟧ty → ⟦ B ⟧ty
⟦ t ∶ A ⟧ty = ∅ ⊢ A


⟦_⟧cx : ∀ (Γ : Cx) → Set
⟦ ∅ ⟧cx     = Unit
⟦ Γ , A ⟧cx = ⟦ Γ ⟧cx × ⟦ A ⟧ty


⟦_⟧ix : ∀ {Γ A} (i : Γ ∋ A) (γ : ⟦ Γ ⟧cx) → ⟦ A ⟧ty
⟦ top ⟧ix   (γ , a) = a
⟦ pop i ⟧ix (γ , b) = ⟦ i ⟧ix γ


postulate
  lam-lm : ∀ {Γ} n (ts : TmV n) {A B} (d : Γ , A ⊢ ts ∶ⁿ B) → n ≤′ dn-lev d
  app-lm : ∀ {Γ} n (ts ss : TmV n) {A B} (d : Γ ⊢ ts ∶ⁿ (A ⊃ B)) (c : Γ ⊢ ss ∶ⁿ A) → n ≤′ dn-lev d ⊓ dn-lev c
  up-down-lm : ∀ {Γ} n (ts : TmV n) {u A} (d : Γ ⊢ ts ∶ⁿ u ∶ A) → n ≤′ dn-lev d
  ⊓-lm₁ : ∀ {n} m → suc n ≤′ m → zero <′ suc n ⊓ m
  ⊓-lm₂ : ∀ {n} m o → suc n ≤′ m ⊓ o → zero <′ suc n ⊓ m ⊓ o


⟦_⟧dn : ∀ {Γ A} (d : Γ ⊢ A) (γ : ⟦ Γ ⟧cx) → ⟦ A ⟧ty

⟦ VAR[ zero ] i ⟧dn               γ = ⟦ i ⟧ix γ
⟦ LAM[ zero ] {[]} d ⟧dn          γ = λ a → ⟦ d ⟧dn (γ , a)
⟦ APP[ zero ] {[]} {[]} d c ⟧dn   γ = (⟦ d ⟧dn γ) (⟦ c ⟧dn γ)
⟦_⟧dn {∅}     (UP[_] zero {[]} d) γ = d
⟦_⟧dn {Γ , _} (UP[_] zero {[]} d) γ = {!!}
⟦ DOWN[ zero ] {[]} d ⟧dn         γ = {!⟦ ⟦ d ⟧dn γ ⟧dn unit!} -- TODO: Termination

⟦_⟧dn {∅} (VAR[_] (suc n) i) γ =
    unnec (VAR[ suc n ] i) z<′sn z<′sn
⟦_⟧dn {∅} (LAM[_] (suc n) {t ∷ ts} {A} {B} d) γ =
    unnec (LAM[ suc n ] {t ∷ ts} d)
      (⊓-lm₁ (dn-lev d) (lam-lm (suc n) (t ∷ ts) d))
      (z<′ty-lev-t∶A t (lamⁿ[ n ] ts ∶ⁿ (A ⊃ B)))
⟦_⟧dn {∅} (APP[_] (suc n) {t ∷ ts} {s ∷ ss} {A} {B} d c) γ =
    unnec (APP[ suc n ] {t ∷ ts} {s ∷ ss} d c)
      (⊓-lm₂ (dn-lev d) (dn-lev c) (app-lm (suc n) (t ∷ ts) (s ∷ ss) d c))
      (z<′ty-lev-t∶A t (appⁿ[ n ] ts ss ∶ⁿ B))
⟦_⟧dn {∅} (UP[_] (suc n) {t ∷ ts} {u} {A} d) γ =
    unnec (UP[ suc n ] {t ∷ ts} d)
      (⊓-lm₁ (dn-lev d) (up-down-lm (suc n) (t ∷ ts) d))
      (z<′ty-lev-t∶A t (upⁿ[ n ] ts ∶ⁿ quo u ∶ u ∶ A))
⟦_⟧dn {∅} (DOWN[_] (suc n) {t ∷ ts} {u} {A} d) γ =
    unnec (DOWN[ suc n ] {t ∷ ts} d)
      (⊓-lm₁ (dn-lev d) (up-down-lm (suc n) (t ∷ ts) d))
      (z<′ty-lev-t∶A t (downⁿ[ n ] ts ∶ⁿ A))

⟦_⟧dn {Γ , _} (VAR[_] (suc n) i)                     γ = {!!}
⟦_⟧dn {Γ , _} (LAM[_] (suc n) {t ∷ ts} d)            γ = {!!}
⟦_⟧dn {Γ , _} (APP[_] (suc n) {t ∷ ts} {s ∷ ss} d c) γ = {!!}
⟦_⟧dn {Γ , _} (UP[_] (suc n) {t ∷ ts} d)             γ = {!!}
⟦_⟧dn {Γ , _} (DOWN[_] (suc n) {t ∷ ts} d)           γ = {!!}


module ⟦PL⟧ where
  -- ⟦ A ⊃ A ⟧
  I : ∀ {A} → ⟦ A ⟧ty → ⟦ A ⟧ty
  I = λ x → x

  -- ⟦ A ⊃ B ⊃ A ⟧
  K : ∀ {A B} → ⟦ A ⟧ty → ⟦ B ⟧ty → ⟦ A ⟧ty
  K = λ x y → x

  -- ⟦ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C ⟧
  S : ∀ {A B C} → ⟦ A ⊃ B ⊃ C ⟧ty → ⟦ A ⊃ B ⟧ty → ⟦ A ⟧ty → ⟦ C ⟧ty
  S = λ f g x → (f x) (g x)


module ⟦PL²⟧ where
  -- ⟦ □ (A ⊃ A) ⟧
  I : ∀ {A} → ∅ ⊢ A ⊃ A
  I = ⟦ LAM² V0² ⟧dn unit

  -- ⟦ □ (A ⊃ B ⊃ A) ⟧
  K : ∀ {A B} → ∅ ⊢ A ⊃ B ⊃ A
  K = ⟦ LAM² LAM² V1² ⟧dn unit

  -- ⟦ □ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C) ⟧
  S : ∀ {A B C} → ∅ ⊢ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
  S = ⟦ LAM² LAM² LAM² APP² (APP² V2² V0²) (APP² V1² V0²) ⟧dn unit


postulate
  wat : ∀ {A} (d : ⟦ A ⟧ty) → ∅ ⊢ A


module ⟦S4⟧ where
  -- ⟦ □ (A ⊃ B) ⊃ □ A ⊃ □ B ⟧
  K : ∀ {A B} → (f : ∅ ⊢ A ⊃ B) → (x : ∅ ⊢ A) → ∅ ⊢ B
  K = λ f x → wat ((⟦ f ⟧dn unit) (⟦ x ⟧dn unit))

  -- ⟦ □ A ⊃ A ⟧
  T : ∀ {A} → (x : ∅ ⊢ A) → ⟦ A ⟧ty
  T = λ x → ⟦ x ⟧dn unit

  -- ⟦ □ A ⊃ □ □ A ⟧
  #4 : ∀ {A} → (x : ∅ ⊢ A) → ∅ ⊢ repr x ∶ A
  #4 = λ x → nec x


module ⟦S4²⟧ where
  -- ⟦ □ (□ (A ⊃ B) ⊃ □ A ⊃ □ B) ⟧
  K : ∀ {f x A B} → ∅ ⊢ f ∶ (A ⊃ B) ⊃ x ∶ A ⊃ app f x ∶ B
  K = ⟦ LAM² LAM² APP³ V1² V0² ⟧dn unit

  -- ⟦ □ (□ A ⊃ A) ⟧
  T : ∀ {x A} → ∅ ⊢ x ∶ A ⊃ A
  T = ⟦ LAM² DOWN² V0² ⟧dn unit

  -- ⟦ □ (□ A ⊃ □ □ A) ⟧
  #4 : ∀ {x A} → ∅ ⊢ x ∶ A ⊃ quo x ∶ x ∶ A
  #4 = ⟦ LAM² UP² V0² ⟧dn unit
