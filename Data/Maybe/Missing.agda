module Data.Maybe.Missing where

open import Category.Monad using (RawMonad)
open import Data.Maybe using (Maybe ; just ; nothing)
import Data.Maybe as M


return : ∀ {ℓ} {X : Set ℓ} → X → Maybe X
return = RawMonad.return M.monad

infix 2 _>>=_
_>>=_ : ∀ {ℓ} {X Y : Set ℓ} → Maybe X → (X → Maybe Y) → Maybe Y
_>>=_ = RawMonad._>>=_ M.monad

do-notation : ∀ {ℓ} {X Y : Set ℓ} → Maybe X → (X → Maybe Y) → Maybe Y
do-notation = _>>=_

infix 0 do-notation
syntax do-notation M (λ x → N) = x ← M ⁏ N


map₂ : ∀ {A B C : Set} → (A → B → C) → Maybe A → Maybe B → Maybe C
map₂ f (just a) (just b) = just (f a b)
map₂ f _        _        = nothing
