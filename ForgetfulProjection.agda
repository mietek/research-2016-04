module ForgetfulProjection where

open import AltArtemov
open import S4.Type renaming (Ty to °Ty)


infixr 3 _°⊃_
infixl 0 _°⇔_

data _°⇔_ : ∀ (A : Ty) (°A : °Ty) → Set where
  °⊥ : ⊥ °⇔ ⊥

  _°⊃_ : ∀ {A B °A °B}
      → A °⇔ °A    → B °⇔ °B
      → (A ⊃ B) °⇔ (°A ⊃ °B)

  °□_ : ∀ {t A °A}
      → A °⇔ °A
      → (t ∶ A) °⇔ (□ °A)


-- Demonstration of forgetful projection to the modal logic S4.
module Demo where
  ⊥°⇔⊥ : ⊥ °⇔ ⊥
  ⊥°⇔⊥ = °⊥

  A⊃B°⇔A⊃B : ∀ {A B °A °B}
      → A °⇔ °A    → B °⇔ °B
      → A ⊃ B °⇔ °A ⊃ °B
  A⊃B°⇔A⊃B a b = a °⊃ b

  t∶A°⇔□A : ∀ {t A °A}
      → A °⇔ °A
      → t ∶ A °⇔ □ °A
  t∶A°⇔□A a = °□ a


-- Forgetful projection of some theorems of propositional logic.
module °PL where
  °I : ∀ {A °A}
      → A °⇔ °A
      → A ⊃ A °⇔ °A ⊃ °A
  °I a = a °⊃ a

  °K : ∀ {A B °A °B}
      → A °⇔ °A    → B °⇔ °B
      → A ⊃ B ⊃ A °⇔ °A ⊃ °B ⊃ °A
  °K a b = a °⊃ b °⊃ a

  °S : ∀ {A B C °A °B °C}
      → A °⇔ °A    → B °⇔ °B    → C °⇔ °C
      → (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C °⇔ (°A ⊃ °B ⊃ °C) ⊃ (°A ⊃ °B) ⊃ °A ⊃ °C
  °S a b c = (a °⊃ b °⊃ c) °⊃ (a °⊃ b) °⊃ a °⊃ c


-- Forgetful projection of some theorems of the λ-calculus.
module °PL² where
  °I² : ∀ {A °A}
      → A °⇔ °A
      → lam v0 ∶ (A ⊃ A) °⇔ □ (°A ⊃ °A)
  °I² a = °□ (a °⊃ a)

  °K² : ∀ {A B °A °B}
      → A °⇔ °A    → B °⇔ °B
      → lam (lam v1) ∶ (A ⊃ B ⊃ A) °⇔ □ (°A ⊃ °B ⊃ °A)
  °K² a b = °□ (a °⊃ b °⊃ a)

  °S² : ∀ {A B C °A °B °C}
      → A °⇔ °A    → B °⇔ °B    → C °⇔ °C
      → lam (lam (lam (app (app v2 v0) (app v1 v0)))) ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C) °⇔ □ ((°A ⊃ °B ⊃ °C) ⊃ (°A ⊃ °B) ⊃ °A ⊃ °C)
  °S² a b c = °□ ((a °⊃ b °⊃ c) °⊃ (a °⊃ b) °⊃ a °⊃ c)


-- Forgetful projection of some first-level realisations of theorems of the modal logic S4.
module °S4 where
  °K : ∀ {f x A B °A °B}
      → A °⇔ °A    → B °⇔ °B
      → f ∶ (A ⊃ B) ⊃ x ∶ A ⊃ app f x ∶ B °⇔ □ (°A ⊃ °B) ⊃ □ °A ⊃ □ °B
  °K a b = °□ (a °⊃ b) °⊃ °□ a °⊃ °□ b

  °T : ∀ {x A °A}
      → A °⇔ °A
      → (x ∶ A) ⊃ A °⇔
          □ °A ⊃ °A
  °T a = °□ a °⊃ a

  °#4 : ∀ {x A °A}
      → A °⇔ °A
      → x ∶ A ⊃ quo x ∶ x ∶ A °⇔
          □ °A ⊃ □ □ °A
  °#4 a = °□ a °⊃ °□ °□ a


-- Forgetful projection of some second-level realisations of theorems of the modal logic S4.
module °S4² where
  °K² : ∀ {f x A B °A °B}
      → A °⇔ °A    → B °⇔ °B
      → lam (lam (app² v1 v0)) ∶ (f ∶ (A ⊃ B) ⊃ x ∶ A ⊃ app f x ∶ B) °⇔ □ (□ (°A ⊃ °B) ⊃ □ °A ⊃ □ °B)
  °K² a b = °□ (°□ (a °⊃ b) °⊃ °□ a °⊃ °□ b)

  °T² : ∀ {x A °A}
      → A °⇔ °A
      → lam (down v0) ∶ (x ∶ A ⊃ A) °⇔ □ (□ °A ⊃ °A)
  °T² a = °□ (°□ a °⊃ a)

  °#4² : ∀ {x A °A}
      → A °⇔ °A
      → lam (up v0) ∶ (x ∶ A ⊃ quo x ∶ x ∶ A) °⇔ □ (□ °A ⊃ □ □ °A)
  °#4² a = °□ (°□ a °⊃ °□ °□ a)
