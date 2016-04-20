module Data.Maybe.Missing where

open import Data.Maybe using (Maybe ; just ; nothing)


map₂ : ∀ {A B C : Set} → (A → B → C) → Maybe A → Maybe B → Maybe C
map₂ f (just a) (just b) = just (f a b)
map₂ f _        _        = nothing
