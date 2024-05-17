module Try3.LP.ForgetfulProjection where

open import Try3.LP.Core public
import Try3.S4.Core as S4


⌊_⌋ᴬ : Ty → S4.Ty
⌊ ⊥ ⌋ᴬ    = S4.⊥
⌊ A ⊃ B ⌋ᴬ = ⌊ A ⌋ᴬ S4.⊃ ⌊ B ⌋ᴬ
⌊ A ∧ B ⌋ᴬ = ⌊ A ⌋ᴬ S4.∧ ⌊ B ⌋ᴬ
⌊ t ∴ A ⌋ᴬ = S4.□ ⌊ A ⌋ᴬ

⌊_⌋ᴳ : Cx Ty → Cx S4.Ty
⌊ ∅ ⌋ᴳ       = ∅
⌊ (Γ , A) ⌋ᴳ = (⌊ Γ ⌋ᴳ , ⌊ A ⌋ᴬ)

⌊_⌋ˣ : ∀ {Γ A} → Var Ty Γ A → Var S4.Ty ⌊ Γ ⌋ᴳ ⌊ A ⌋ᴬ
⌊ top ⌋ˣ   = top
⌊ pop x ⌋ˣ = pop ⌊ x ⌋ˣ

⌊_⌋ : ∀ {Γ Δ A} → Tm Γ Δ A → S4.Tm ⌊ Γ ⌋ᴳ ⌊ Δ ⌋ᴳ ⌊ A ⌋ᴬ
⌊ var x ⌋      = S4.var ⌊ x ⌋ˣ
⌊ lam t ⌋      = S4.lam ⌊ t ⌋
⌊ app t₁ t₂ ⌋  = S4.app ⌊ t₁ ⌋ ⌊ t₂ ⌋
⌊ *var x ⌋     = S4.*var ⌊ x ⌋ˣ
⌊ up t ⌋       = S4.up ⌊ t ⌋
⌊ down t₁ t₂ ⌋ = S4.down ⌊ t₁ ⌋ ⌊ t₂ ⌋
⌊ pair t₁ t₂ ⌋ = S4.pair ⌊ t₁ ⌋ ⌊ t₂ ⌋
⌊ fst t ⌋      = S4.fst ⌊ t ⌋
⌊ snd t ⌋      = S4.snd ⌊ t ⌋
