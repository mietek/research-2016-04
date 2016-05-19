module AltArtemov.Context.Representation.OPE where

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)

open import AltArtemov.Context.Representation.Core


data _≥ᵍ_ : (g g′ : CxR) → Set where
  id   : ∀ {g} → g ≥ᵍ g
  weak : ∀ {g g′} → g′ ≥ᵍ g → (g′ ,◌) ≥ᵍ g
  lift : ∀ {g g′} → g′ ≥ᵍ g → (g′ ,◌) ≥ᵍ (g ,◌)


_•ᵍ_ : ∀ {g g′ g″} → g″ ≥ᵍ g′ → g′ ≥ᵍ g → g″ ≥ᵍ g
id     •ᵍ r′      = r′
weak r •ᵍ r′      = weak (r •ᵍ r′)
lift r •ᵍ id      = lift r
lift r •ᵍ weak r′ = weak (r •ᵍ r′)
lift r •ᵍ lift r′ = lift (r •ᵍ r′)


r•ᵍid : ∀ {g g′} (r : g ≥ᵍ g′) → r •ᵍ id ≡ r
r•ᵍid id       = refl
r•ᵍid (weak r) = cong weak (r•ᵍid r)
r•ᵍid (lift r) = refl

id•ᵍr : ∀ {g g′} (r : g ≥ᵍ g′) → id •ᵍ r ≡ r
id•ᵍr id       = refl
id•ᵍr (weak r) = refl
id•ᵍr (lift r) = cong lift (id•ᵍr r)


•ᵍassoc : ∀ {g g′ g″ g‴} (r″ : g‴ ≥ᵍ g″) (r′ : g″ ≥ᵍ g′) (r : g′ ≥ᵍ g)
    → (r″ •ᵍ r′) •ᵍ r ≡ r″ •ᵍ (r′ •ᵍ r)
•ᵍassoc id        r′        r        = refl
•ᵍassoc (weak r″) r′        r        = cong weak (•ᵍassoc r″ r′ r)
•ᵍassoc (lift r″) id        r        = refl
•ᵍassoc (lift r″) (weak r′) r        = cong weak (•ᵍassoc r″ r′ r)
•ᵍassoc (lift r″) (lift r′) id       = refl
•ᵍassoc (lift r″) (lift r′) (weak r) = cong weak (•ᵍassoc r″ r′ r)
•ᵍassoc (lift r″) (lift r′) (lift r) = cong lift (•ᵍassoc r″ r′ r)


g≥ᵍ∅ : ∀ {g} → g ≥ᵍ ∅
g≥ᵍ∅ {∅}    = id
g≥ᵍ∅ {g ,◌} = weak g≥ᵍ∅
