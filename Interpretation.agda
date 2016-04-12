module Interpretation where

open import Data.Empty using () renaming (⊥ to Empty ; ⊥-elim to expl)
open import Data.Nat using (ℕ ; zero ; suc ; _≤′_ ; _<′_ ; _⊓_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using () renaming (⊤ to Unit ; tt to unit)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import AltArtemov
open import Data.Nat.Missing
open import README using (module PL ; module PL² ; module S4 ; module S4²)


⟦_⟧ty : ∀ (A : Ty) (Γ : Cx) → Set
⟦ ⊥ ⟧ty    Γ = Empty
⟦ A ⊃ B ⟧ty Γ = ⟦ A ⟧ty Γ → ⟦ B ⟧ty Γ
⟦ t ∶ A ⟧ty Γ = Γ ⊢ A


⟦_⟧cx : ∀ (Γ : Cx) → Set
⟦ ∅ ⟧cx     = Unit
⟦ Γ , A ⟧cx = ⟦ Γ ⟧cx × ⟦ A ⟧ty Γ


drop : ∀ Γ {A} (i : Γ ∋ A) → Cx
drop ∅       ()
drop (Γ , A) top     = Γ
drop (Γ , A) (pop i) = drop Γ i


⟦_⟧ix : ∀ {Γ A} (i : Γ ∋ A) (γ : ⟦ Γ ⟧cx) → ⟦ A ⟧ty (drop Γ i)
⟦ top ⟧ix   ⟨ γ , a ⟩ = a
⟦ pop i ⟧ix ⟨ γ , b ⟩ = ⟦ i ⟧ix γ


postulate
  lam-lm : ∀ {Γ} n (ts : TmV (suc n)) {A B} (d : Γ , A ⊢ ts ∶ⁿ B) → suc n ≤′ dn-lev d
  app-lm : ∀ {Γ} n (ts ss : TmV (suc n)) {A B} (d : Γ ⊢ ts ∶ⁿ (A ⊃ B)) (c : Γ ⊢ ss ∶ⁿ A) → suc n ≤′ dn-lev d ⊓ dn-lev c
  up-down-lm : ∀ {Γ} n (ts : TmV (suc n)) {u A} (d : Γ ⊢ ts ∶ⁿ u ∶ A) → suc n ≤′ dn-lev d
  weak : ∀ {Γ A} {i : Γ ∋ A} → ⟦ A ⟧ty (drop Γ i) → ⟦ A ⟧ty Γ


⟦_⟧dn : ∀ {Γ A} (d : Γ ⊢ A) → ⟦ Γ ⟧cx → ⟦ A ⟧ty Γ
⟦ VAR[ zero ] i ⟧dn             γ = weak (⟦ i ⟧ix γ)
⟦ LAM[ zero ] {[]} d ⟧dn        γ = λ a → {!⟦ d ⟧dn (γ , a)!}
⟦ APP[ zero ] {[]} {[]} d c ⟧dn γ = (⟦ d ⟧dn γ) (⟦ c ⟧dn γ)
⟦ UP[ zero ] {[]} d ⟧dn         γ = d
⟦ DOWN[ zero ] {[]} d ⟧dn       γ = {!⟦ ⟦ d ⟧dn γ ⟧dn γ!} -- TODO: Termination
⟦ VAR[ suc n ] i ⟧dn γ =
    unint (VAR[ suc n ] i)
      z<′sn
      z<′sn
⟦ LAM[ suc n ] {t ∷ ts} d ⟧dn γ =
    unint (LAM[ suc n ] {t ∷ ts} d)
      (m<′n⇒z<′sm⊓n (lam-lm n (t ∷ ts) d))
      z<′sn
⟦ APP[ suc n ] {t ∷ ts} {s ∷ ss} d c ⟧dn γ =
    unint (APP[ suc n ] {t ∷ ts} {s ∷ ss} d c)
      (n<′m⇒z<′sn⊓m⊓o (dn-lev d) (dn-lev c) (app-lm n (t ∷ ts) (s ∷ ss) d c))
      z<′sn
⟦ UP[ suc n ] {t ∷ ts} d ⟧dn γ =
    unint (UP[ suc n ] {t ∷ ts} d)
      (m<′n⇒z<′sm⊓n (up-down-lm n (t ∷ ts) d))
      z<′sn
⟦ DOWN[ suc n ] {t ∷ ts} d ⟧dn γ =
    unint (DOWN[ suc n ] {t ∷ ts} d)
      (m<′n⇒z<′sm⊓n (up-down-lm n (t ∷ ts) d))
      z<′sn


module AgPL where
  AgI : ∀ {A} → ⟦ A ⟧ty ∅ → ⟦ A ⟧ty ∅
  AgI = λ x → x

  AgK : ∀ {A B} → ⟦ A ⟧ty ∅ → ⟦ B ⟧ty ∅ → ⟦ A ⟧ty ∅
  AgK = λ x y → x

  AgS : ∀ {A B C} → (⟦ A ⟧ty ∅ → ⟦ B ⟧ty ∅ → ⟦ C ⟧ty ∅) → (⟦ A ⟧ty ∅ → ⟦ B ⟧ty ∅) → ⟦ A ⟧ty ∅ → ⟦ C ⟧ty ∅
  AgS = λ f g x → (f x) (g x)


module PLDemo where
  open AgPL
  open PL
  open PL²

  -- ⟦ A ⟧ty → ⟦ A ⟧ty
  ⟦I⟧≡AgI : ∀ {A} → ⟦ I {A} ⟧dn unit ≡ AgI
  ⟦I⟧≡AgI = refl

  -- ⟦ A ⟧ty → ⟦ B ⟧ty → ⟦ A ⟧ty
  ⟦K⟧≡AgK : ∀ {A B} → ⟦ K {A} {B} ⟧dn unit ≡ AgK
  ⟦K⟧≡AgK = refl

  -- (⟦ A ⟧ty → ⟦ B ⟧ty → ⟦ C ⟧ty) → (⟦ A ⟧ty → ⟦ B ⟧ty) → ⟦ A ⟧ty → ⟦ C ⟧ty
  ⟦S⟧≡AgS : ∀ {A B C} → ⟦ S {A} {B} {C} ⟧dn unit ≡ AgS
  ⟦S⟧≡AgS = refl

  -- ∅ ⊢ A ⊃ A
  ⟦I²⟧≡I : ∀ {A} → ⟦ I² {A} ⟧dn unit ≡ I
  ⟦I²⟧≡I = refl

  -- ∅ ⊢ A ⊃ B ⊃ A
  ⟦K²⟧≡I : ∀ {A B} → ⟦ K² {A} {B} ⟧dn unit ≡ K
  ⟦K²⟧≡I = refl

  -- ∅ ⊢ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
  ⟦S²⟧≡I : ∀ {A B C} → ⟦ S² {A} {B} {C} ⟧dn unit ≡ S
  ⟦S²⟧≡I = refl


postulate
  wat : ∀ {A} (d : ⟦ A ⟧ty ∅) → ∅ ⊢ A


module AgS4 where
  AgK : ∀ {A B} → (f : ∅ ⊢ A ⊃ B) → (x : ∅ ⊢ A) → ∅ ⊢ B
  AgK = λ f x → wat ((⟦ f ⟧dn unit) (⟦ x ⟧dn unit))

  AgT : ∀ {A} → (x : ∅ ⊢ A) → ⟦ A ⟧ty ∅
  AgT = λ x → ⟦ x ⟧dn unit

  Ag#4 : ∀ {A} → (x : ∅ ⊢ A) → ∅ ⊢ repr x ∶ A
  Ag#4 = λ x → nec x


module S4Demo where
  open AgS4
  open S4
  open S4²

  -- ∅ ⊢ A ⊃ B → ∅ ⊢ A → ∅ ⊢ B
  ⟦K⟧≡AgK : ∀ {f x A B} → ⟦ K {f} {x} {A} {B} ⟧dn unit ≡ AgK
  ⟦K⟧≡AgK = refl

  -- ∅ ⊢ A → ⟦ A ⟧ty
  ⟦T⟧≡AgT : ∀ {x A} → ⟦ T {x} {A} ⟧dn unit ≡ AgT
  ⟦T⟧≡AgT = refl

  -- ∅ ⊢ A → ∅ ⊢ x ∶ A
  ⟦#4⟧≡Ag#4 : ∀ {x A} → ⟦ #4 {x} {A} ⟧dn unit ≡ {!Ag#4!}
  ⟦#4⟧≡Ag#4 = refl

  -- ∅ ⊢ f ∶ (A ⊃ B) ⊃ x ∶ A ⊃ app f x ∶ B
  ⟦K²⟧≡K : ∀ {f x A B} → ⟦ K² {f} {x} {A} {B} ⟧dn unit ≡ K
  ⟦K²⟧≡K = refl

  -- ∅ ⊢ x ∶ A ⊃ A
  ⟦T²⟧≡T : ∀ {x A} → ⟦ T² {x} {A} ⟧dn unit ≡ T
  ⟦T²⟧≡T = refl

  -- ∅ ⊢ x ∶ A ⊃ quo x ∶ x ∶ A
  ⟦#4²⟧≡#4 : ∀ {x A} → ⟦ #4² {x} {A} ⟧dn unit ≡ #4
  ⟦#4²⟧≡#4 = refl
