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
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
import Data.Maybe as Maybe


_+ᴿ_ : ℕ → ℕ → ℕ
m +ᴿ zero  = m
m +ᴿ suc n = suc (m +ᴿ n)

raiseᴿ : ∀ {m} (n : ℕ) → Fin m → Fin (m +ᴿ n)
raiseᴿ zero i    = i
raiseᴿ (suc n) i = suc (raiseᴿ n i)


-- A well-scoped term is indexed by the size of the context it requires.

data Tm (g : ℕ) : Set where
  VAR[_]  : ℕ → Fin g → Tm g
  LAM[_]  : ℕ → Tm (suc g) → Tm g
  APP[_]  : ℕ → Tm g → Tm g → Tm g
  UP[_]   : ℕ → Tm g → Tm g
  DOWN[_] : ℕ → Tm g → Tm g
  PAIR[_] : ℕ → Tm g → Tm g → Tm g
  FST[_]  : ℕ → Tm g → Tm g
  SND[_]  : ℕ → Tm g → Tm g
  BOOM[_] : ℕ → Tm g → Tm g

! : ∀ {g} → Tm g → Tm g
! (VAR[ n ] i)    = VAR[ suc n ] i
! (LAM[ n ] t)    = LAM[ suc n ] (! t)
! (APP[ n ] t u)  = APP[ suc n ] (! t) (! u)
! (UP[ n ] t)     = UP[ suc n ] (! t)
! (DOWN[ n ] t)   = DOWN[ suc n ] (! t)
! (PAIR[ n ] t u) = PAIR[ suc n ] (! t) (! u)
! (FST[ n ] t)    = FST[ suc n ] (! t)
! (SND[ n ] t)    = SND[ suc n ] (! t)
! (BOOM[ n ] t)   = BOOM[ suc n ] (! t)

module Term where
  Ren : ℕ → ℕ → Set
  Ren g g′ = Fin g → Fin g′

  weaken-ren : ∀ {g g′} → Ren g g′ → Ren (suc g) (suc g′)
  weaken-ren f zero    = zero
  weaken-ren f (suc i) = suc (f i)

  ren : ∀ {g g′} → Ren g g′ → Tm g → Tm g′
  ren f (VAR[ n ] i)    = VAR[ n ] (f i)
  ren f (LAM[ n ] t)    = LAM[ n ] (ren (weaken-ren f) t)
  ren f (APP[ n ] t u)  = APP[ n ] (ren f t) (ren f u)
  ren f (UP[ n ] t)     = UP[ n ] (ren f t)
  ren f (DOWN[ n ] t)   = DOWN[ n ] (ren f t)
  ren f (PAIR[ n ] t u) = PAIR[ n ] (ren f t) (ren f u)
  ren f (FST[ n ] t)    = FST[ n ] (ren f t)
  ren f (SND[ n ] t)    = SND[ n ] (ren f t)
  ren f (BOOM[ n ] t)   = BOOM[ n ] (ren f t)

  Sub : ℕ → ℕ → Set
  Sub g g′ = Fin g → Tm g′

  weaken-sub : ∀ {g g′} → Sub g g′ → ℕ → Sub (suc g) (suc g′)
  weaken-sub f n zero    = VAR[ n ] zero
  weaken-sub f n (suc i) = ren suc (f i)

  sub : ∀ {g g′} → Sub g g′ → Tm g → Tm g′
  sub f (VAR[ n ] i)    = f i
  sub f (LAM[ n ] t)    = LAM[ n ] (sub (weaken-sub f n) t)
  sub f (APP[ n ] t u)  = APP[ n ] (sub f t) (sub f u)
  sub f (UP[ n ] t)     = UP[ n ] (sub f t)
  sub f (DOWN[ n ] t)   = DOWN[ n ] (sub f t)
  sub f (PAIR[ n ] t u) = PAIR[ n ] (sub f t) (sub f u)
  sub f (FST[ n ] t)    = FST[ n ] (sub f t)
  sub f (SND[ n ] t)    = SND[ n ] (sub f t)
  sub f (BOOM[ n ] t)   = BOOM[ n ] (sub f t)

  strengthen : ∀ {g} → Tm g → ℕ → Sub (suc g) g
  strengthen t n zero    = t
  strengthen t n (suc i) = VAR[ n ] i

  redex : ∀ {g} → Tm g → Maybe (Tm g)
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


-- A type is indexed by the size of the context each type assertion requires, and by the number of type assertions it contains at the top level.

infixr 2 _⊃_
infixr 5 _∶_

data Ty (g : ℕ) : ℕ → Set where
  _∶_ : ∀ {a} → Tm g → Ty g a → Ty g (suc a)
  _⊃_ : ∀ {a b} → Ty g a → Ty (suc g) b → Ty g zero
  _∧_ : ∀ {a b} → Ty g a → Ty g b → Ty g zero
  ⊥  : Ty g zero

⊤ : ∀ {g} → Ty g zero
⊤ = ⊥ ⊃ ⊥

¬_ : ∀ {g a} → Ty g a → Ty g zero
¬ A = A ⊃ ⊥

_⫗_ : ∀ {g a b} → Ty g a → Ty (suc g) b → Ty g zero
A ⫗ B = (A ⊃ B) ∧ (B ⊃ A)

module Type where
  ren : ∀ {g g′ a} → Term.Ren g g′ → Ty a → Ty a
  ren f ⊥      = ⊥
  ren f (A ⊃ B) = ren f A ⊃ ren f B
  ren f (x ∶ A) = {!Term.ren f x ∶ ren f A!}
  ren f (A ∧ B) = {!!}


-- A vector of terms is indexed by the size of the context each term requires, and by the number of terms it contains.

-- infixr 5 _∷_
-- infixr 5 _∴_

-- data Tms (g : ℕ) : ℕ → Set where
--   []  : Tms g zero
--   _∷_ : ∀ {n} → Tm g → Tms g n → Tms g (suc n)

-- _∴_ : ∀ {g n a} → Tms g n → Ty a → Ty (n + a)
-- [] ∴ A       = A
-- (t ∷ ts) ∴ A = t ∶ ts ∴ A

-- module Terms where
--   map : ∀ {g} → (ℕ → Tm g → Tm g) → (n : ℕ) → Tms g n → Tms g n
--   map f zero []          = []
--   map f (suc n) (t ∷ ts) = f (suc n) t ∷ map f n ts

--   map₂ : ∀ {g} → (ℕ → Tm g → Tm g → Tm g) → (n : ℕ) → Tms g n → Tms g n → Tms g n
--   map₂ f zero [] []                = []
--   map₂ f (suc n) (t ∷ ts) (u ∷ us) = f (suc n) t u ∷ map₂ f n ts us

--   ren : ∀ {g g′ n} → Term.Ren g g′ → Tms g n → Tms g′ n
--   ren f []       = []
--   ren f (t ∷ ts) = Term.ren f t ∷ ren f ts

--   sub : ∀ {g g′ n} → Term.Sub g g′ → Tms g n → Tms g′ n
--   sub f []       = []
--   sub f (t ∷ ts) = Term.sub f t ∷ sub f ts

-- VARs[_] : ∀ {g} (n : ℕ) → Fin g → Tms g n
-- VARs[ zero ] i  = []
-- VARs[ suc n ] i = VAR[ n ] i ∷ VARs[ n ] i

-- LAMs[_] : ∀ {g} (n : ℕ) → Tms (suc g) n → Tms g n
-- LAMs[ zero ] []        = []
-- LAMs[ suc n ] (t ∷ ts) = LAM[ n ] t ∷ LAMs[ n ] ts

-- APPs[_] : ∀ {g} (n : ℕ) → Tms g n → Tms g n → Tms g n
-- APPs[_] = Terms.map₂ APP[_]

-- UPs[_] : ∀ {g} (n : ℕ) → Tms g n → Tms g n
-- UPs[_] = Terms.map UP[_]

-- DOWNs[_] : ∀ {g} (n : ℕ) → Tms g n → Tms g n
-- DOWNs[_] = Terms.map DOWN[_]

-- PAIRs[_] : ∀ {g} (n : ℕ) → Tms g n → Tms g n → Tms g n
-- PAIRs[_] = Terms.map₂ PAIR[_]

-- FSTs[_] : ∀ {g} (n : ℕ) → Tms g n → Tms g n
-- FSTs[_] = Terms.map FST[_]

-- SNDs[_] : ∀ {g} (n : ℕ) → Tms g n → Tms g n
-- SNDs[_] = Terms.map SND[_]

-- BOOMs[_] : ∀ {g} (n : ℕ) → Tms g n → Tms g n
-- BOOMs[_] = Terms.map BOOM[_]


-- -- A context can be projected as a natural number.

-- infixl 2 _,_
-- infixr 1 _∈_

-- data Cx : Set where
--   ∅   : Cx
--   _,_ : ∀ {a} → Cx → Ty a → Cx

-- ⌊_⌋C : Cx → ℕ
-- ⌊ ∅ ⌋C     = zero
-- ⌊ Γ , A ⌋C = suc ⌊ Γ ⌋C


-- -- A well-typed de Bruijn index can be projected as a finite natural number.

-- data _∈_ {a} (A : Ty a) : Cx → Set where
--   zero : ∀ {Γ} → A ∈ Γ , A
--   suc  : ∀ {Γ b} {B : Ty b} → A ∈ Γ → A ∈ Γ , B

-- ⌊_⌋∈ : ∀ {Γ a} {A : Ty a} → A ∈ Γ → Fin ⌊ Γ ⌋C
-- ⌊ zero ⌋∈  = zero
-- ⌊ suc i ⌋∈ = suc ⌊ i ⌋∈


-- -- A well-typed derivation is indexed by the context it requires, and by its conclusion.

-- infix 0 _⊢_

-- data _⊢_ (Γ : Cx) : ∀ {z} → Ty z → Set where
--   var[_] : ∀ n {a} {A : Ty a} {Z : Ty (n + a)}
--       → (i : A ∈ Γ)
--       → {{_ : VARs[ n ] ⌊ i ⌋∈ ∴ A ≡ Z}}
--       → Γ ⊢ Z
--   lam[_] : ∀ n {ts : Tms (suc ⌊ Γ ⌋C) n} {a b} {A : Ty a} {B : Ty b} {Z : Ty (n + zero)}
--       → Γ , A ⊢ ts ∴ B
--       → {{_ : LAMs[ n ] ts ∴ (A ⊃ B) ≡ Z}}
--       → Γ ⊢ Z
--   app[_] : ∀ n {ts us : Tms ⌊ Γ ⌋C n} {a b} {A : Ty a} {B : Ty b} {Z : Ty (n + b)}
--       → Γ ⊢ ts ∴ (A ⊃ B)    → Γ ⊢ us ∴ A
--       → {{_ : APPs[ n ] ts us ∴ B ≡ Z}}
--       → Γ ⊢ Z
--   up[_] : ∀ n {ts : Tms ⌊ Γ ⌋C n} {u : Tm ⌊ Γ ⌋C} {a} {A : Ty a} {Z : Ty (n + suc (suc a))}
--       → Γ ⊢ ts ∴ u ∶ A
--       → {{_ : UPs[ n ] ts ∴ ! u ∶ u ∶ A ≡ Z}}
--       → Γ ⊢ Z
--   down[_] : ∀ n {ts : Tms ⌊ Γ ⌋C n} {u : Tm ⌊ Γ ⌋C} {a} {A : Ty a} {Z : Ty (n + a)}
--       → Γ ⊢ ts ∴ u ∶ A
--       → {{_ : DOWNs[ n ] ts ∴ A ≡ Z}}
--       → Γ ⊢ Z
--   pair[_] : ∀ n {ts us : Tms ⌊ Γ ⌋C n} {a b} {A : Ty a} {B : Ty b} {Z : Ty (n + zero)}
--       → Γ ⊢ ts ∴ A    → Γ ⊢ us ∴ B
--       → {{_ : PAIRs[ n ] ts us ∴ (A ∧ B) ≡ Z}}
--       → Γ ⊢ Z
--   fst[_] : ∀ n {ts : Tms ⌊ Γ ⌋C n} {a b} {A : Ty a} {B : Ty b} {Z : Ty (n + a)}
--       → Γ ⊢ ts ∴ (A ∧ B)
--       → {{_ : FSTs[ n ] ts ∴ A ≡ Z}}
--       → Γ ⊢ Z
--   snd[_] : ∀ n {ts : Tms ⌊ Γ ⌋C n} {a b} {A : Ty a} {B : Ty b} {Z : Ty (n + b)}
--       → Γ ⊢ ts ∴ (A ∧ B)
--       → {{_ : SNDs[ n ] ts ∴ B ≡ Z}}
--       → Γ ⊢ Z
--   boom[_] : ∀ n {ts : Tms ⌊ Γ ⌋C n} {a} {A : Ty a} {Z : Ty (n + a)}
--       → Γ ⊢ ts ∴ ⊥
--       → {{_ : BOOMs[ n ] ts ∴ A ≡ Z}}
--       → Γ ⊢ Z

-- module Derivation where
--   Ren : Cx → Cx → Set
--   Ren Γ Γ′ = ∀ {a} {A : Ty a} → A ∈ Γ → A ∈ Γ′

--   weaken-ren : ∀ {Γ Γ′ a} {A : Ty a} → Ren Γ Γ′ → Ren (Γ , A) (Γ′ , A)
--   weaken-ren f zero    = zero
--   weaken-ren f (suc i) = suc (f i)

--   -- ren : ∀ {Γ Γ′ a} {A : Ty a} → Ren Γ Γ′ → Term.Ren ⌊ Γ ⌋C ⌊ Γ′ ⌋C → Γ ⊢ A → Γ′ ⊢ A
--   -- ren f tf (var[ n ] i)    = {!!} -- var[ n ] {!!}
--   -- ren f tf (lam[ n ] d)    = {!!} -- lam[ n ] (ren (weaken-ren f) d)
--   -- ren f tf (app[ n ] d e)  = {!!} -- app[ n ] (ren f d) (ren f e)
--   -- ren {A = A₀} f tf (up[ n ] {ts} {u} {A = A′} d) = up[ n ] {Terms.ren tf ts} {Term.ren tf u} {A = {!A′!}} {!ren f tf d!} {{{!!}}}-- up[_] {A = {!.A!}} n {ts = Terms.ren ⌊f⌋R ts} {u = Term.ren ⌊f⌋R u} {!ren f ⌊f⌋R d!}
--   -- ren f tf (down[ n ] d)   = {!!} -- down[ n ] (ren f d)
--   -- ren f tf (pair[ n ] d e) = {!!} -- pair[ n ] (ren f d) (ren f e)
--   -- ren f tf (fst[ n ] d)    = {!!} -- fst[ n ] (ren f d)
--   -- ren f tf (snd[ n ] d)    = {!!} -- snd[ n ] (ren f d)
--   -- ren f tf (boom[ n ] d)   = {!!} -- boom[ n ] (ren f d)
