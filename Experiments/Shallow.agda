module Try1.Experiments.Shallow where


-- Truth.

open import Data.Unit using (⊤) renaming (tt to unit) public


-- Falsehood.

open import Data.Empty using (⊥) renaming (⊥-elim to void) public


-- TODO: Explicit provability.

infixl 5 _▷_
data _▷_ (A : Set) : A → Set where    -- TODO: This is wrong.
  [_] : ∀ (t : A) → A ▷ t

up : ∀ {A : Set} {t : A} (d : A ▷ t) → A ▷ t ▷ [ t ]
up [ t ] = [ [ t ] ]

down : ∀ {A : Set} {t : A} (d : A ▷ t) → A
down [ t ] = t


-- Booleans.

open import Data.Bool using (true ; false) renaming (Bool to 𝔹 ; if_then_else_ to if) public


-- Naturals.

open import Data.Nat using (ℕ ; zero ; suc) public

rec : ∀ {A : Set} (k : ℕ) (z : A) (s : ℕ → A → A) → A
rec zero    z s = z
rec (suc k) z s = s k (rec k z s)


-- Conjunction.

infixl 4 _∧_
infixl 2 _,_
record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B
open _∧_ public


-- Disjunction.

infixl 3 _∨_
data _∨_ (A B : Set) : Set where
  inj₁ : ∀ (a : A) → A ∨ B
  inj₂ : ∀ (b : B) → A ∨ B

case : ∀ {A B C : Set} (s : A ∨ B) (l : A → C) (r : B → C) → C
case (inj₁ a) l r = l a
case (inj₂ b) l r = r b


-- Negation.

open import Relation.Nullary using (¬_) public


-- Equivalence.

infix 1 _⟷_
_⟷_ : ∀ (A B : Set) → Set
A ⟷ B = (A → B) ∧ (B → A)
