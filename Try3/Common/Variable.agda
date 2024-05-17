module Try3.Common.Variable where

open import Try3.Common.OrderPreservingEmbedding public


data Var (X : Set) : Cx X → X → Set where
  top : ∀ {Γ A} → Var X (Γ , A) A
  pop : ∀ {Γ A B} → Var X Γ A → Var X (Γ , B) A


ⁱ⌊_⌋ : ∀ {X} {Γ : Cx X} {x : X} → Var X Γ x → Fin ᵍ⌊ Γ ⌋
ⁱ⌊ top ⌋   = zero
ⁱ⌊ pop x ⌋ = suc ⁱ⌊ x ⌋


x₀ : ∀ {X Γ A} → Var X (Γ , A) A
x₀ = top

x₁ : ∀ {X Γ A B} → Var X ((Γ , A) , B) A
x₁ = pop x₀

x₂ : ∀ {X Γ A B C} → Var X (((Γ , A) , B) , C) A
x₂ = pop x₁


_-_ : ∀ {X A} → (Γ : Cx X) → Var X Γ A → Cx X
∅       - ()
(Γ , A) - top   = Γ
(Γ , A) - pop x = ((Γ - x) , A)


wk-var⁻ : ∀ {X Γ A B} → (x : Var X Γ A) → Var X (Γ - x) B → Var X Γ B
wk-var⁻ top     y       = pop y
wk-var⁻ (pop x) top     = top
wk-var⁻ (pop x) (pop y) = pop (wk-var⁻ x y)


data EqVar⁻ {X : Set} : ∀ {Γ A B} → Var X Γ A → Var X Γ B → Set where
  same : ∀ {Γ A} {x : Var X Γ A} → EqVar⁻ x x
  diff : ∀ {Γ A B} → (x : Var X Γ A) → (y : Var X (Γ - x) B) → EqVar⁻ x (wk-var⁻ x y)

eq-var⁻ : ∀ {X Γ A B} → (x : Var X Γ A) → (y : Var X Γ B) → EqVar⁻ x y
eq-var⁻ top     top                  = same
eq-var⁻ top     (pop y)              = diff top y
eq-var⁻ (pop x) top                  = diff (pop x) top
eq-var⁻ (pop x) (pop y)              with eq-var⁻ x y
eq-var⁻ (pop y) (pop .y)             | same      = same
eq-var⁻ (pop x) (pop .(wk-var⁻ x y)) | diff .x y = diff (pop x) (pop y)


ren-var : ∀ {X Γ Γ′ A} → Γ′ ≥ Γ → Var X Γ A → Var X Γ′ A
ren-var base     x       = x
ren-var (weak η) x       = pop (ren-var η x)
ren-var (lift η) top     = top
ren-var (lift η) (pop x) = pop (ren-var η x)

wk-var : ∀ {X Γ A B} → Var X Γ A → Var X (Γ , B) A
wk-var = ren-var wk

wk₀-var : ∀ {X Γ A} → Var X ∅ A → Var X Γ A
wk₀-var ()


ren-var-id : ∀ {X Γ A} → (x : Var X Γ A) → ren-var id x ≡ x
ren-var-id top     = refl
ren-var-id (pop x) = cong pop (ren-var-id x)

ren-var-• : ∀ {X Γ Γ′ Γ″ A} (η′ : Γ″ ≥ Γ′) (η : Γ′ ≥ Γ) (x : Var X Γ A) →
            ren-var η′ (ren-var η x) ≡ ren-var (η′ • η) x
ren-var-• base      η        x       = refl
ren-var-• (weak η′) η        x       = cong pop (ren-var-• η′ η x)
ren-var-• (lift η′) (weak η) x       = cong pop (ren-var-• η′ η x)
ren-var-• (lift η′) (lift η) top     = refl
ren-var-• (lift η′) (lift η) (pop x) = cong pop (ren-var-• η′ η x)
