module Common.OrderPreservingEmbedding where

open import Common.Context public


data _≥_ {X : Set} : Cx X → Cx X → Set where
  base : ∅ ≥ ∅
  weak : ∀ {Γ Γ′ A} → Γ′ ≥ Γ → (Γ′ , A) ≥ Γ
  lift : ∀ {Γ Γ′ A} → Γ′ ≥ Γ → (Γ′ , A) ≥ (Γ , A)


id : ∀ {X} {Γ : Cx X} → Γ ≥ Γ
id {Γ = ∅}     = base
id {Γ = Γ , A} = lift id

to : ∀ {X} {Γ : Cx X} → Γ ≥ ∅
to {Γ = ∅}     = base
to {Γ = Γ , A} = weak to

drop : ∀ {X} {Γ Γ′ : Cx X} {A} → Γ′ ≥ (Γ , A) → Γ′ ≥ Γ
drop (weak η) = weak (drop η)
drop (lift η) = weak η

keep : ∀ {X} {Γ Γ′ : Cx X} {A} → (Γ′ , A) ≥ (Γ , A) → Γ′ ≥ Γ
keep (weak η) = drop η
keep (lift η) = η

wk : ∀ {X} {Γ : Cx X} {A} → (Γ , A) ≥ Γ
wk = weak id


_•_ : ∀ {X} {Γ Γ′ Γ″ : Cx X} → Γ″ ≥ Γ′ → Γ′ ≥ Γ → Γ″ ≥ Γ
base    • η      = η
weak η′ • η      = weak (η′ • η)
lift η′ • weak η = weak (η′ • η)
lift η′ • lift η = lift (η′ • η)

η•id : ∀ {X} {Γ Γ′ : Cx X} → (η : Γ′ ≥ Γ) → η • id ≡ η
η•id base     = refl
η•id (weak η) = cong weak (η•id η)
η•id (lift η) = cong lift (η•id η)

id•η : ∀ {X} {Γ Γ′ : Cx X} → (η : Γ′ ≥ Γ) → id • η ≡ η
id•η base     = refl
id•η (weak η) = cong weak (id•η η)
id•η (lift η) = cong lift (id•η η)

•assoc : ∀ {X} {Γ‴ Γ″ Γ′ Γ : Cx X} →
         (η″ : Γ‴ ≥ Γ″) (η′ : Γ″ ≥ Γ′) (η : Γ′ ≥ Γ) →
         (η″ • η′) • η ≡ η″ • (η′ • η)
•assoc base      η′        η        = refl
•assoc (weak η″) η′        η        = cong weak (•assoc η″ η′ η)
•assoc (lift η″) (weak η′) η        = cong weak (•assoc η″ η′ η)
•assoc (lift η″) (lift η′) (weak η) = cong weak (•assoc η″ η′ η)
•assoc (lift η″) (lift η′) (lift η) = cong lift (•assoc η″ η′ η)
