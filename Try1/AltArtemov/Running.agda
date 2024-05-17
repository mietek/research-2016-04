module AltArtemov.Running where


module Maybe where
  open import Data.Maybe using (Maybe ; just ; nothing ; map)
  open import Relation.Nullary using (Dec ; yes ; no)
  open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

  map-∨ : ∀ {A B C : Set} → (A → B → C) → A → B → Maybe A → Maybe B → Maybe C
  map-∨ f a₀ b₀ (just a) (just b) = just (f a b)
  map-∨ f a₀ b₀ (just a) nothing  = just (f a b₀)
  map-∨ f a₀ b₀ nothing (just b)  = just (f a₀ b)
  map-∨ f a₀ b₀ nothing nothing   = nothing

  when : ∀ {A B : Set} {a a′ : A} → Dec (a ≡ a′) → B → Maybe B
  when (yes refl) b = just b
  when (no _) b     = nothing


open import Data.Fin using (Fin ; zero ; suc)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Nat using (ℕ ; zero ; suc ; _+_) renaming (_≟_ to _≟ℕ_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; cong ; cong₂ ; subst)
open import Relation.Nullary using (Dec ; yes ; no)
import Data.Maybe as Maybe


_+ᴿ_ : ℕ → ℕ → ℕ
m +ᴿ zero  = m
m +ᴿ suc n = suc (m +ᴿ n)

raiseᴿ : ∀ {m} (n : ℕ) → Fin m → Fin (m +ᴿ n)
raiseᴿ zero i    = i
raiseᴿ (suc n) i = suc (raiseᴿ n i)


-- Terms.

data Tm : Set where
  !_      : Tm → Tm
  VAR[_]  : ℕ → ℕ → Tm
  LAM[_]  : ℕ → Tm → Tm
  APP[_]  : ℕ → Tm → Tm → Tm
  UP[_]   : ℕ → Tm → Tm
  DOWN[_] : ℕ → Tm → Tm
  PAIR[_] : ℕ → Tm → Tm → Tm
  FST[_]  : ℕ → Tm → Tm
  SND[_]  : ℕ → Tm → Tm
  BOOM[_] : ℕ → Tm → Tm

module Term where
  Ren : Set
  Ren = ℕ → ℕ

  weaken-ren : Ren → Ren
  weaken-ren f i = i

  ren : Ren → Tm → Tm
  ren f (! t)           = ! (ren f t)
  ren f (VAR[ n ] i)    = VAR[ n ] (f i)
  ren f (LAM[ n ] t)    = LAM[ n ] (ren (weaken-ren f) t)
  ren f (APP[ n ] t u)  = APP[ n ] (ren f t) (ren f u)
  ren f (UP[ n ] t)     = UP[ n ] (ren f t)
  ren f (DOWN[ n ] t)   = DOWN[ n ] (ren f t)
  ren f (PAIR[ n ] t u) = PAIR[ n ] (ren f t) (ren f u)
  ren f (FST[ n ] t)    = FST[ n ] (ren f t)
  ren f (SND[ n ] t)    = SND[ n ] (ren f t)
  ren f (BOOM[ n ] t)   = BOOM[ n ] (ren f t)

  Sub : Set
  Sub = ℕ → Tm

  weaken-sub : Sub → ℕ → Sub
  weaken-sub f n zero    = VAR[ n ] zero
  weaken-sub f n (suc i) = ren suc (f i)

  sub : Sub → Tm → Tm
  sub f (! t)           = ! (sub f t)
  sub f (VAR[ n ] i)    = f i
  sub f (LAM[ n ] t)    = LAM[ n ] (sub (weaken-sub f n) t)
  sub f (APP[ n ] t u)  = APP[ n ] (sub f t) (sub f u)
  sub f (UP[ n ] t)     = UP[ n ] (sub f t)
  sub f (DOWN[ n ] t)   = DOWN[ n ] (sub f t)
  sub f (PAIR[ n ] t u) = PAIR[ n ] (sub f t) (sub f u)
  sub f (FST[ n ] t)    = FST[ n ] (sub f t)
  sub f (SND[ n ] t)    = SND[ n ] (sub f t)
  sub f (BOOM[ n ] t)   = BOOM[ n ] (sub f t)

  strengthen : Tm → ℕ → Sub
  strengthen t n zero    = t
  strengthen t n (suc i) = VAR[ n ] i

  redex : Tm → Maybe Tm
  redex (! t)                       = nothing  -- TODO: Are you sure?
  redex (VAR[ n ] i)                = nothing
  redex (LAM[ n ] t)                = Maybe.map LAM[ n ] (redex t)
  redex (APP[ n ] (LAM[ n′ ] t) u)  = Maybe.when (n ≟ℕ n′) (sub (strengthen u n) t)
  redex (APP[ n ] t u)              = Maybe.map-∨ APP[ n ] t u (redex t) (redex u)
  redex (UP[ n ] t)                 = Maybe.map UP[ n ] (redex t)
  redex (DOWN[ n ] (UP[ n′ ] t))    = Maybe.when (n ≟ℕ n′) t
  redex (DOWN[ n ] t)               = Maybe.map DOWN[ n ] (redex t)
  redex (PAIR[ n ] t u)             = Maybe.map-∨ PAIR[ n ] t u (redex t) (redex u)
  redex (FST[ n ] (PAIR[ n′ ] t u)) = Maybe.when (n ≟ℕ n′) t
  redex (FST[ n ] t)                = Maybe.map FST[ n ] (redex t)
  redex (SND[ n ] (PAIR[ n′ ] t u)) = Maybe.when (n ≟ℕ n′) u
  redex (SND[ n ] t)                = Maybe.map SND[ n ] (redex t)
  redex (BOOM[ n ] t)               = Maybe.map BOOM[ n ] (redex t)


-- Types.

infixr 2 _⊃_
infixr 5 _∶_

data Ty : Set where
  _∶_ : Tm → Ty → Ty
  _⊃_ : Ty → Ty → Ty
  _∧_ : Ty → Ty → Ty
  ⊥  : Ty

⊤ : Ty
⊤ = ⊥ ⊃ ⊥

¬_ : Ty → Ty
¬ A = A ⊃ ⊥

_⫗_ : Ty → Ty → Ty
A ⫗ B = (A ⊃ B) ∧ (B ⊃ A)

module Type where
  ren : Term.Ren → Ty → Ty
  ren f (t ∶ A) = Term.ren f t ∶ ren f A
  ren f (A ⊃ B) = A ⊃ B
  ren f (A ∧ B) = A ∧ B
  ren f ⊥      = ⊥

  sub : Term.Sub → Ty → Ty
  sub f (t ∶ A) = Term.sub f t ∶ sub f A
  sub f (A ⊃ B) = A ⊃ B
  sub f (A ∧ B) = A ∧ B
  sub f ⊥      = ⊥


-- A vector of terms is indexed by the number of terms it contains.

infixr 5 _∷_
infixr 5 _∴_

data Tms : ℕ → Set where
  []  : Tms zero
  _∷_ : ∀ {n} → Tm → Tms n → Tms (suc n)

_∴_ : ∀ {n} → Tms n → Ty → Ty
[] ∴ A       = A
(t ∷ ts) ∴ A = t ∶ ts ∴ A

module Terms where
  map : (F : ℕ → Tm → Tm) (n : ℕ) → Tms n → Tms n
  map F zero []          = []
  map F (suc n) (t ∷ ts) = F (suc n) t ∷ map F n ts

  map₂ : (F : ℕ → Tm → Tm → Tm) (n : ℕ) → Tms n → Tms n → Tms n
  map₂ F zero [] []                = []
  map₂ F (suc n) (t ∷ ts) (u ∷ us) = F (suc n) t u ∷ map₂ F n ts us

  ren : ∀ {n} → Term.Ren → Tms n → Tms n
  ren f []       = []
  ren f (t ∷ ts) = Term.ren f t ∷ ren f ts

  sub : ∀ {n} → Term.Sub → Tms n → Tms n
  sub f []       = []
  sub f (t ∷ ts) = Term.sub f t ∷ sub f ts

  ren-dist-∴ : ∀ {n} (f : Term.Ren) (ts : Tms n) {A}
      → Type.ren f (ts ∴ A) ≡ ren f ts ∴ Type.ren f A
  ren-dist-∴ f []       = refl
  ren-dist-∴ f (t ∷ ts) = cong (λ ts′ → Term.ren f t ∶ ts′) (ren-dist-∴ f ts)

  sub-dist-∴ : ∀ {n} (f : Term.Sub) (ts : Tms n) {A}
      → Type.sub f (ts ∴ A) ≡ sub f ts ∴ Type.sub f A
  sub-dist-∴ f []       = refl
  sub-dist-∴ f (t ∷ ts) = cong (λ ts′ → Term.sub f t ∶ ts′) (sub-dist-∴ f ts)


VARs[_] : (n : ℕ) → ℕ → Tms n
VARs[ zero ] i  = []
VARs[ suc n ] i = VAR[ n ] i ∷ VARs[ n ] i

LAMs[_] : (n : ℕ) → Tms n → Tms n
LAMs[_] = Terms.map LAM[_]

APPs[_] : (n : ℕ) → Tms n → Tms n → Tms n
APPs[_] = Terms.map₂ APP[_]

UPs[_] : (n : ℕ) → Tms n → Tms n
UPs[_] = Terms.map UP[_]

DOWNs[_] : (n : ℕ) → Tms n → Tms n
DOWNs[_] = Terms.map DOWN[_]

PAIRs[_] : (n : ℕ) → Tms n → Tms n → Tms n
PAIRs[_] = Terms.map₂ PAIR[_]

FSTs[_] : (n : ℕ) → Tms n → Tms n
FSTs[_] = Terms.map FST[_]

SNDs[_] : (n : ℕ) → Tms n → Tms n
SNDs[_] = Terms.map SND[_]

BOOMs[_] : (n : ℕ) → Tms n → Tms n
BOOMs[_] = Terms.map BOOM[_]


-- A context can be projected as a natural number.

infixl 2 _,_
infixr 1 _∈_

data Cx : Set where
  ∅   : Cx
  _,_ : Cx → Ty → Cx

⌊_⌋C : Cx → ℕ
⌊ ∅ ⌋C     = zero
⌊ Γ , A ⌋C = suc ⌊ Γ ⌋C


-- A well-typed de Bruijn index can be projected as a natural number.

data _∈_ (A : Ty) : Cx → Set where
  zero : ∀ {Γ} → A ∈ Γ , A
  suc  : ∀ {Γ B} → A ∈ Γ → A ∈ Γ , B

⌊_⌋∈ : ∀ {Γ A} → A ∈ Γ → ℕ
⌊ zero ⌋∈  = zero
⌊ suc i ⌋∈ = suc ⌊ i ⌋∈


-- A well-typed derivation is indexed by the context it requires, and by its conclusion.

infix 0 _⊢_

data _⊢_ (Γ : Cx) : Ty → Set where
  var[_] : ∀ (n : ℕ) {A Z}
      → (i : A ∈ Γ)
      → VARs[ n ] ⌊ i ⌋∈ ∴ A ≡ Z
      → Γ ⊢ Z

  lam[_] : ∀ (n : ℕ) {ts : Tms n} {A B Z}
      → Γ , A ⊢ ts ∴ B
      → LAMs[ n ] ts ∴ (A ⊃ B) ≡ Z
      → Γ ⊢ Z

  app[_] : ∀ (n : ℕ) {ts us : Tms n} {A B Z}
      → Γ ⊢ ts ∴ (A ⊃ B)    → Γ ⊢ us ∴ A
      → APPs[ n ] ts us ∴ B ≡ Z
      → Γ ⊢ Z

  up[_] : ∀ (n : ℕ) {ts : Tms n} {u A Z}
      → Γ ⊢ ts ∴ u ∶ A
      → UPs[ n ] ts ∴ ! u ∶ u ∶ A ≡ Z
      → Γ ⊢ Z

  down[_] : ∀ (n : ℕ) {ts : Tms n} {u A Z}
      → Γ ⊢ ts ∴ u ∶ A
      → DOWNs[ n ] ts ∴ A ≡ Z
      → Γ ⊢ Z

  pair[_] : ∀ (n : ℕ) {ts us : Tms n} {A B Z}
      → Γ ⊢ ts ∴ A    → Γ ⊢ us ∴ B
      → PAIRs[ n ] ts us ∴ (A ∧ B) ≡ Z
      → Γ ⊢ Z

  fst[_] : ∀ (n : ℕ) {ts : Tms n} {A B Z}
      → Γ ⊢ ts ∴ (A ∧ B)
      → FSTs[ n ] ts ∴ A ≡ Z
      → Γ ⊢ Z

  snd[_] : ∀ (n : ℕ) {ts : Tms n} {A B Z}
      → Γ ⊢ ts ∴ (A ∧ B)
      → SNDs[ n ] ts ∴ B ≡ Z
      → Γ ⊢ Z

  boom[_] : ∀ (n : ℕ) {ts : Tms n} {A Z}
      → Γ ⊢ ts ∴ ⊥
      → BOOMs[ n ] ts ∴ A ≡ Z
      → Γ ⊢ Z


redex : ∀ {Γ Z} → Γ ⊢ Z → Maybe (Γ ⊢ Z)
redex (var[ n ] i refl)    = nothing
redex (lam[ n ] d refl)    = Maybe.map (λ d′ → lam[ n ] d′ refl) (redex d)
redex (app[ n ] d c refl)  = {!!}
redex (up[ n ] d refl)     = Maybe.map (λ d′ → up[ n ] d′ refl) (redex d)
redex (down[ n ] d refl)   = {!!}
redex (pair[ n ] d c refl) = {!!}
redex (fst[ n ] (pair[ n′ ] d e p) refl) with n ≟ℕ n′
redex (fst[ n ] (pair[ .n ] d e p) refl) | yes refl = {!just d!}
redex (fst[ n ] (pair[ n′ ] d e p) refl) | no ¬p = {!!}
redex (fst[ n ] d refl) = {!!}
redex (snd[ n ] d refl)    = {!!}
redex (boom[ n ] d refl)   = Maybe.map (λ d′ → boom[ n ] d′ refl) (redex d)


-- ren-dist-map : ∀ {n a} (F : ℕ → Tm → Tm) (f : Term.Ren) (ts : Tms n) (A : Ty a)
--     → {{_ : (n : ℕ) (t : Tm) → Term.ren f (F n t) ≡ F n (Term.ren f t)}}
--     → Terms.map F n (Terms.ren f ts) ∴ Type.ren f A ≡ Type.ren f (Terms.map F n ts ∴ A)
-- ren-dist-map {zero} F f [] A = refl
-- ren-dist-map {suc n} F f (t ∷ ts) A {{p}} rewrite p (suc n) t
--     = cong (λ A′ → F (suc n) (Term.ren f t) ∶ A′) (ren-dist-map F f ts A {{p}})

-- ren-dist-UP : ∀ {n a} (f : Term.Ren) (ts : Tms n) (A : Ty a)
--     → UPs[ n ] (Terms.ren f ts) ∴ Type.ren f A ≡ Type.ren f (UPs[ n ] ts ∴ A)
-- ren-dist-UP f ts A = ren-dist-map UP[_] f ts A

-- ren-cong-UP : ∀ {n a} (f : Term.Ren) (ts : Tms n) (u : Tm) (A : Ty a) (Z Z′ : Ty (n + suc (suc a)))
--     → {{_ : UPs[ n ] ts ∴ (! u ∶ u ∶ A) ≡ Z}} {{_ : Z′ ≡ Type.ren f Z}}
--     → UPs[ n ] (Terms.ren f ts) ∴ Type.ren f (! u ∶ u ∶ A) ≡ Z′
-- ren-cong-UP f ts u A Z Z′ {{p}} {{r}} rewrite ren-dist-UP f ts (! u ∶ u ∶ A) | r = cong (Type.ren f) p


-- Ren : Cx → Cx → Set
-- Ren Γ Γ′ = ∀ {z} {Z : Ty z} → Z ∈ Γ → Z ∈ Γ′

-- Link : ∀ {Γ Γ′} → Ren Γ Γ′ → Term.Ren → Set
-- Link {Γ} φ f = ∀ {z} {Z : Ty z} {d : Z ∈ Γ} → ⌊ φ d ⌋∈ ≡ f ⌊ d ⌋∈

-- weaken-ren : ∀ {Γ Γ′ a} {A : Ty a} → Ren Γ Γ′ → Ren (Γ , A) (Γ′ , A)
-- weaken-ren f zero    = zero
-- weaken-ren f (suc i) = suc (f i)

-- weaken-link : ∀ {Γ Γ′} {φ : Ren Γ Γ′} {f : Term.Ren} → Link φ f → Link (weaken-ren φ) (Term.weaken-ren f)
-- weaken-link p = {!!}

-- ren : ∀ {Γ Γ′ z} {Z Z′ : Ty z} (φ : Ren Γ Γ′) (f : Term.Ren)
--     → {{_ : Link φ f}} {{_ : Z′ ≡ Type.ren f Z}}
--     → Γ ⊢ Z
--     → Γ′ ⊢ Z′

-- ren φ f (var[ n ] i)    = {!!}

-- ren {Γ′ = Γ′} {Z = Z} {Z′ = Z′} φ f (lam[ n ] {ts} {A} {B} d)
--     = let d′ = ren (weaken-ren φ) (Term.weaken-ren f) {{{!!}}} d
--       in lam[ n ] {!!}

-- ren φ f (app[ n ] d e)  = {!!}

-- ren {Γ′ = Γ′} {Z = Z} {Z′ = Z′} φ f (up[ n ] {ts} {u} {A} d)
--     = let d′ = subst (λ C → Γ′ ⊢ C) (Terms.ren-dist-∴ f ts (u ∶ A)) (ren φ f d)
--           instance p′ = ren-cong-UP f ts u A Z Z′
--       in up[ n ] {Terms.ren f ts} {Term.ren f u} {Type.ren f A} d′

-- ren φ f (down[ n ] d)   = {!!}
-- ren φ f (pair[ n ] d e) = {!!}
-- ren φ f (fst[ n ] d)    = {!!}
-- ren φ f (snd[ n ] d)    = {!!}
-- ren φ f (boom[ n ] d)   = {!!}

-- -- module Derivation where
-- --   Ren : Cx → Cx → Set
-- --   Ren Γ Γ′ = ∀ {z} {Z : Ty z} → Z ∈ Γ → Z ∈ Γ′

-- --   foo : ∀ {Γ Γ′ n a b} (φ : Ren Γ Γ′) (f : Term.Ren) (ts : Tms n) (A : Ty a) (B : Ty b)
-- --       → Γ , A ⊢ ts ∴ B
-- --       → Γ′ , Type.ren f A ⊢ Type.ren f (ts ∴ B)
-- --   foo φ f ts A B p = {!!}

-- --   weaken-ren : ∀ {Γ Γ′ z} {Z : Ty z} (φ : Ren Γ Γ′) (f : Term.Ren) → Ren (Γ , Z) (Γ′ , Type.ren f Z)
-- --   weaken-ren φ f zero    = {!!}
-- --   weaken-ren φ f (suc i) = {!!}

-- --   ren : ∀ {Γ Γ′ z} {Z : Ty z} (φ : Ren Γ Γ′) (f : Term.Ren)
-- --       → Γ ⊢ Z
-- --       → Γ′ ⊢ Type.ren f Z

-- --   ren {Γ′ = Γ′} {Z = Z} φ f (var[ n ] {A} i {{p}})
-- --       = var[ n ] (φ i) {{{!!}}}

-- --   ren {Γ′ = Γ′} {Z = Z} φ f (lam[ n ] {ts} {A} {B} d {{p}})
-- --       = let d₀ = {!!} -- ren (weaken-ren φ) f d
-- --             d₁ = {!!}
-- --             d′ = subst (λ C → Γ′ , Type.ren f A ⊢ C) (Terms.ren-dist-∴ f ts B) (foo φ f ts A B d)
-- --         in lam[ n ] {Terms.ren f ts} {Type.ren f A} {Type.ren f B} d′ {{ren-cong-LAM f ts A B Z p}}

-- --   ren {Γ′ = Γ′} {Z = Z} φ f (app[ n ] {ts} {us} {A} {B} d e {{p}})
-- --       = let d′ = subst (λ C → Γ′ ⊢ C) (Terms.ren-dist-∴ f ts (A ⊃ B)) (ren φ f d)
-- --             e′ = subst (λ C → Γ′ ⊢ C) (Terms.ren-dist-∴ f us A) (ren φ f e)
-- --         in app[ n ] d′ e′ {{ren-cong-APP f ts us A B Z p}}

-- --   ren {Γ′ = Γ′} {Z = Z} φ f (up[ n ] {ts} {u} {A} d {{p}})
-- --       = let d′ = subst (λ C → Γ′ ⊢ C) (Terms.ren-dist-∴ f ts (u ∶ A)) (ren φ f d)
-- --         in up[ n ] d′ {{ren-cong-UP f ts u A Z p}}

-- --   ren {Γ′ = Γ′} {Z = Z} φ f (down[ n ] {ts} {u} {A} d {{p}})
-- --       = let d′ = subst (λ C → Γ′ ⊢ C) (Terms.ren-dist-∴ f ts (u ∶ A)) (ren φ f d)
-- --         in down[ n ] d′ {{ren-cong-DOWN f ts A Z p}}

-- --   ren {Γ′ = Γ′} {Z = Z} φ f (pair[ n ] {ts} {us} {A} {B} d e {{p}})
-- --       = let d′ = subst (λ C → Γ′ ⊢ C) (Terms.ren-dist-∴ f ts A) (ren φ f d)
-- --             e′ = subst (λ C → Γ′ ⊢ C) (Terms.ren-dist-∴ f us B) (ren φ f e)
-- --         in pair[ n ] d′ e′ {{ren-cong-PAIR f ts us A B Z p}}

-- --   ren {Γ′ = Γ′} {Z = Z} φ f (fst[ n ] {ts} {A} {B} d {{p}})
-- --       = let d′ = subst (λ C → Γ′ ⊢ C) (Terms.ren-dist-∴ f ts (A ∧ B)) (ren φ f d)
-- --         in fst[ n ] d′ {{ren-cong-FST f ts A Z p}}

-- --   ren {Γ′ = Γ′} {Z = Z} φ f (snd[ n ] {ts} {A} {B} d {{p}})
-- --       = let d′ = subst (λ C → Γ′ ⊢ C) (Terms.ren-dist-∴ f ts (A ∧ B)) (ren φ f d)
-- --         in snd[ n ] d′ {{ren-cong-SND f ts B Z p}}

-- --   ren {Γ′ = Γ′} {Z = Z} φ f (boom[ n ] {ts} {A} d {{p}})
-- --       = let d′ = subst (λ C → Γ′ ⊢ C) (Terms.ren-dist-∴ f ts ⊥) (ren φ f d)
-- --         in boom[ n ] d′ {{ren-cong-BOOM f ts A Z p}}
