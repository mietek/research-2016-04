module Interpretation where

open import Data.Empty using () renaming (⊥ to Empty ; ⊥-elim to expl)
open import Data.Nat using (ℕ ; zero ; suc ; _≤′_ ; _<′_ ; _⊓_)
open import Data.Product using (_,_ ; _×_)
open import Data.Unit using () renaming (⊤ to Unit ; tt to unit)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import AltArtemov
open import AltArtemov.Type.Properties using () renaming (z<′lev-t∶A to z<′ty-lev-t∶A)
open import Data.Nat.Missing
open import README using (module PL ; module PL² ; module S4 ; module S4²)


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


module AgPL where
  I : ∀ {A} → ⟦ A ⟧ty → ⟦ A ⟧ty
  I = λ x → x

  K : ∀ {A B} → ⟦ A ⟧ty → ⟦ B ⟧ty → ⟦ A ⟧ty
  K = λ x y → x

  S : ∀ {A B C} → (⟦ A ⟧ty → ⟦ B ⟧ty → ⟦ C ⟧ty) → (⟦ A ⟧ty → ⟦ B ⟧ty) → ⟦ A ⟧ty → ⟦ C ⟧ty
  S = λ f g x → (f x) (g x)


module PLDemo where
  -- ⟦ A ⟧ty → ⟦ A ⟧ty
  ⟦I⟧≡AgI : ∀ {A} → ⟦ PL.I {A} ⟧dn unit ≡ AgPL.I
  ⟦I⟧≡AgI = refl

  -- ⟦ A ⟧ty → ⟦ B ⟧ty → ⟦ A ⟧ty
  ⟦K⟧≡AgK : ∀ {A B} → ⟦ PL.K {A} {B} ⟧dn unit ≡ AgPL.K
  ⟦K⟧≡AgK = refl

  -- (⟦ A ⟧ty → ⟦ B ⟧ty → ⟦ C ⟧ty) → (⟦ A ⟧ty → ⟦ B ⟧ty) → ⟦ A ⟧ty → ⟦ C ⟧ty
  ⟦S⟧≡AgS : ∀ {A B C} → ⟦ PL.S {A} {B} {C} ⟧dn unit ≡ AgPL.S
  ⟦S⟧≡AgS = refl

  -- ∅ ⊢ A ⊃ A
  ⟦I²⟧≡I : ∀ {A} → ⟦ PL².I {A} ⟧dn unit ≡ PL.I
  ⟦I²⟧≡I = refl

  -- ∅ ⊢ A ⊃ B ⊃ A
  ⟦K²⟧≡I : ∀ {A B} → ⟦ PL².K {A} {B} ⟧dn unit ≡ PL.K
  ⟦K²⟧≡I = refl

  -- ∅ ⊢ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
  ⟦S²⟧≡I : ∀ {A B C} → ⟦ PL².S {A} {B} {C} ⟧dn unit ≡ PL.S
  ⟦S²⟧≡I = refl


postulate
  wat : ∀ {A} (d : ⟦ A ⟧ty) → ∅ ⊢ A


module AgS4 where
  K : ∀ {A B} → (f : ∅ ⊢ A ⊃ B) → (x : ∅ ⊢ A) → ∅ ⊢ B
  K = λ f x → wat ((⟦ f ⟧dn unit) (⟦ x ⟧dn unit))

  T : ∀ {A} → (x : ∅ ⊢ A) → ⟦ A ⟧ty
  T = λ x → ⟦ x ⟧dn unit

  #4 : ∀ {A} → (x : ∅ ⊢ A) → ∅ ⊢ repr x ∶ A
  #4 = λ x → nec x


module S4Demo where
  -- ∅ ⊢ A ⊃ B → ∅ ⊢ A → ∅ ⊢ B
  ⟦K⟧≡AgK : ∀ {f x A B} → ⟦ S4.K {f} {x} {A} {B} ⟧dn unit ≡ AgS4.K
  ⟦K⟧≡AgK = refl

  -- ∅ ⊢ A → ⟦ A ⟧ty
  ⟦T⟧≡AgT : ∀ {x A} → ⟦ S4.T {x} {A} ⟧dn unit ≡ AgS4.T
  ⟦T⟧≡AgT = refl

  -- ∅ ⊢ A → ∅ ⊢ x ∶ A
  ⟦#4⟧≡Ag#4 : ∀ {x A} → ⟦ S4.#4 {x} {A} ⟧dn unit ≡ {!AgS4.#4!}
  ⟦#4⟧≡Ag#4 = refl

  -- ∅ ⊢ f ∶ (A ⊃ B) ⊃ x ∶ A ⊃ app f x ∶ B
  ⟦K²⟧≡K : ∀ {f x A B} → ⟦ S4².K {f} {x} {A} {B} ⟧dn unit ≡ S4.K
  ⟦K²⟧≡K = refl

  -- ∅ ⊢ x ∶ A ⊃ A
  ⟦T²⟧≡T : ∀ {x A} → ⟦ S4².T {x} {A} ⟧dn unit ≡ S4.T
  ⟦T²⟧≡T = refl

  -- ∅ ⊢ x ∶ A ⊃ quo x ∶ x ∶ A
  ⟦#4²⟧≡#4 : ∀ {x A} → ⟦ S4².#4 {x} {A} ⟧dn unit ≡ S4.#4
  ⟦#4²⟧≡#4 = refl
