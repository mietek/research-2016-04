module LPWithEquality.Examples where

open import LPWithEquality.Core public


≑refl : ∀ {Γ Δ A} → Tm Γ Δ (A ≑ A)
≑refl = ≑I v₀ v₀

≑sym : ∀ {Γ Δ A B} → Tm Γ Δ ((A ≑ B) ⊃ (B ≑ A))
≑sym = lam (≑I (≑E₂ v₁ v₀ v₀) (≑E₁ v₁ v₀ v₀))

≑trans : ∀ {Γ Δ A B C} → Tm Γ Δ ((A ≑ B) ⊃ (B ≑ C) ⊃ (A ≑ C))
≑trans = lam (lam (≑I (≑E₁ v₁ (≑E₁ v₂ v₀ v₀) v₀)
                      (≑E₂ v₂ (≑E₂ v₁ v₀ v₀) v₀)))

X1 : ∀ {Γ Δ A B} → Tm Γ Δ (¬ (A ≑ (B ⊃ B)) ⊃ ¬ (lam v₀ ∴ A))
X1 = lam (lam (app v₁ {!down v₀ ?!}))
