module Examples.AltArtemov where

open import AltArtemov


-- Some theorems of propositional logic.

I : ∀ {A Γ} → Γ ⊢ A ⊃ A
I = lam v0

K : ∀ {A B Γ} → Γ ⊢ A ⊃ B ⊃ A
K = lam (lam v1)

S : ∀ {A B C Γ} → Γ ⊢ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
S = lam (lam (lam (app (app v2 v0) (app v1 v0))))


-- Some theorems of the λ-calculus.

I² : ∀ {A Γ} → Γ ⊢ LAM V0 ∶ (A ⊃ A)
I² = lam² v0²

K² : ∀ {A B Γ} → Γ ⊢ LAM (LAM V1) ∶ (A ⊃ B ⊃ A)
K² = lam² (lam² v1²)

S² : ∀ {A B C Γ} → Γ ⊢ LAM (LAM (LAM (APP (APP V2 V0) (APP V1 V0)))) ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
S² = lam² (lam² (lam² (app² (app² v2² v0²) (app² v1² v0²))))


-- Some theorems of third-level logic.

I³ : ∀ {A Γ} → Γ ⊢ LAM² V0² ∶ LAM V0 ∶ (A ⊃ A)
I³ = lam³ v0³

K³ : ∀ {A B Γ} → Γ ⊢ LAM² (LAM² V1²) ∶ LAM (LAM V1) ∶ (A ⊃ B ⊃ A)
K³ = lam³ (lam³ v1³)

S³ : ∀ {A B C Γ} → Γ ⊢ LAM² (LAM² (LAM² (APP² (APP² V2² V0²) (APP² V1² V0²)))) ∶ LAM (LAM (LAM (APP (APP V2 V0) (APP V1 V0)))) ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
S³ = lam³ (lam³ (lam³ (app³ (app³ v2³ v0³) (app³ v1³ v0³))))


-- Some first-level realisations of theorems of the modal logic S4.

D : ∀ {f x A B Γ} → Γ ⊢ f ∶ (A ⊃ B) ⊃ x ∶ A ⊃ APP f x ∶ B
D = lam (lam (app² v1 v0))

T : ∀ {x A Γ} → Γ ⊢ x ∶ A ⊃ A
T = lam (down v0)

#4 : ∀ {x A Γ} → Γ ⊢ x ∶ A ⊃ quo x ∶ x ∶ A
#4 = lam (up v0)


-- Some second-level realisations of theorems of the modal logic S4.

D² : ∀ {f x A B Γ} → Γ ⊢ LAM (LAM (APP² V1 V0)) ∶ (f ∶ (A ⊃ B) ⊃ x ∶ A ⊃ APP f x ∶ B)
D² = lam² (lam² (app³ v1² v0²))

T² : ∀ {x A Γ} → Γ ⊢ LAM (DOWN V0) ∶ (x ∶ A ⊃ A)
T² = lam² (down² v0²)

#4² : ∀ {x A Γ} → Γ ⊢ LAM (UP V0) ∶ (x ∶ A ⊃ quo x ∶ x ∶ A)
#4² = lam² (up² v0²)


-- Some third-level realisations of theorems of the modal logic S4.

D³ : ∀ {f x A B Γ} → Γ ⊢ LAM² (LAM² (APP³ V1² V0²)) ∶ LAM (LAM (APP² V1 V0)) ∶ (f ∶ (A ⊃ B) ⊃ x ∶ A ⊃ APP f x ∶ B)
D³ = lam³ (lam³ (app⁴ v1³ v0³))

T³ : ∀ {x A Γ} → Γ ⊢ LAM² (DOWN² V0²) ∶ LAM (DOWN V0) ∶ (x ∶ A ⊃ A)
T³ = lam³ (down³ v0³)

#4³ : ∀ {x A Γ} → Γ ⊢ LAM² (UP² V0²) ∶ LAM (UP V0) ∶ (x ∶ A ⊃ quo x ∶ x ∶ A)
#4³ = lam³ (up³ v0³)
