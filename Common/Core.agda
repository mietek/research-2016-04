module Try3.Common.Core where

open import Data.Empty using () renaming (⊥ to Empty ; ⊥-elim to empty) public
open import Data.Fin using (Fin ; zero ; suc) public
--open import Data.List using (List ; [] ; _∷_ ; [_] ; _++_) public
open import Data.Nat using (ℕ ; zero ; suc ; _+_) public
open import Data.Product using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂ ; ∃) public
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂ ; [_,_]) public
open import Data.Unit using () renaming (⊤ to Unit ; tt to unit) public
open import Function using (_∘_ ; _$_) public
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst) public
open import Relation.Binary.HeterogeneousEquality
  using (_≅_ ; ≡-to-≅ ; ≅-to-≡)
  renaming (refl to hrefl ; sym to hsym ; trans to htrans ; cong to hcong ;
    cong₂ to hcong₂ ; subst to hsubst ; subst-removable to hsubst-removable ;
    ≡-subst-removable to subst-removable) public


suc-plus : ∀ k n → suc (n + k) ≡ (n + suc k)
suc-plus k zero    = refl
suc-plus k (suc n) = cong suc (suc-plus k n)

cong₃ : ∀ {ℓ ℓ′ ℓ″ ℓ‴} {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″} {D : Set ℓ‴}
        {a a′ b b′ c c′} (f : A → B → C → D) → a ≡ a′ → b ≡ b′ → c ≡ c′ →
        f a b c ≡ f a′ b′ c′
cong₃ f refl refl refl = refl
