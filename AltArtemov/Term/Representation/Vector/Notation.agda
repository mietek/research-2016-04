module Try2.AltArtemov.Term.Representation.Vector.Notation where

open import Data.Nat using (ℕ ; zero ; suc)

open import Try2.AltArtemov.Context.Representation
open import Try2.AltArtemov.Term.Representation.Core
open import Try2.AltArtemov.Term.Representation.Vector.Core
open import Try2.AltArtemov.Variable.Representation


VARs[_] : ∀ {g} → (n : ℕ) → ◌∈ g → Vec g n
VARs[ zero ]  i = []
VARs[ suc n ] i = VAR[ n ] i ∷ VARs[ n ] i

LAMs[_] : ∀ {g} → (n : ℕ) → Vec (g ,◌) n → Vec g n
LAMs[ zero ]  []       = []
LAMs[ suc n ] (t ∷ ts) = LAM[ n ] t ∷ LAMs[ n ] ts

APPs[_] : ∀ {g} → (n : ℕ) → Vec g n → Vec g n → Vec g n
APPs[ zero ]  []       []       = []
APPs[ suc n ] (t ∷ ts) (u ∷ us) = APP[ n ] t u ∷ APPs[ n ] ts us

PAIRs[_] : ∀ {g} → (n : ℕ) → Vec g n → Vec g n → Vec g n
PAIRs[ zero ]  []       []       = []
PAIRs[ suc n ] (t ∷ ts) (u ∷ us) = PAIR[ n ] t u ∷ PAIRs[ n ] ts us

FSTs[_] : ∀ {g} → (n : ℕ) → Vec g n → Vec g n
FSTs[ zero ]  []       = []
FSTs[ suc n ] (t ∷ ts) = FST[ n ] t ∷ FSTs[ n ] ts

SNDs[_] : ∀ {g} → (n : ℕ) → Vec g n → Vec g n
SNDs[ zero ]  []       = []
SNDs[ suc n ] (t ∷ ts) = SND[ n ] t ∷ SNDs[ n ] ts

UPs[_] : ∀ {g} → (n : ℕ) → Vec g n → Vec g n
UPs[ zero ]  []       = []
UPs[ suc n ] (t ∷ ts) = UP[ n ] t ∷ UPs[ n ] ts

DOWNs[_] : ∀ {g} → (n : ℕ) → Vec g n → Vec g n
DOWNs[ zero ]  []       = []
DOWNs[ suc n ] (t ∷ ts) = DOWN[ n ] t ∷ DOWNs[ n ] ts

BOOMs[_] : ∀ {g} → (n : ℕ) → Vec g n → Vec g n
BOOMs[ zero ]  []       = []
BOOMs[ suc n ] (t ∷ ts) = BOOM[ n ] t ∷ BOOMs[ n ] ts
