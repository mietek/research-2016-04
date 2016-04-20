module Examples.S4 where

open import S4


-- Some theorems of propositional logic.

I : ∀ {A} → ⊩ A ⊃ A
I = lam v0

K : ∀ {A B} → ⊩ A ⊃ B ⊃ A
K = lam (lam v1)

S : ∀ {A B C} → ⊩ (A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C
S = lam (lam (lam (app (app v2 v0) (app v1 v0))))


-- Some modalised theorems of propositional logic.

□I : ∀ {A} → ⊩ □ (A ⊃ A)
□I = box (lam v0)

□K : ∀ {A B} → ⊩ □ (A ⊃ B ⊃ A)
□K = box (lam (lam v1))

□S : ∀ {A B C} → ⊩ □ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
□S = box (lam (lam (lam (app (app v2 v0) (app v1 v0)))))


-- Some twice-modalised theorems of propositional logic.

□□I : ∀ {A} → ⊩ □ □ (A ⊃ A)
□□I = box (box (lam v0))

□□K : ∀ {A B} → ⊩ □ □ (A ⊃ B ⊃ A)
□□K = box (box (lam (lam v1)))

□□S : ∀ {A B C} → ⊩ □ □ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
□□S = box (box (lam (lam (lam (app (app v2 v0) (app v1 v0))))))


-- Some theorems of the modal logic S4.

D : ∀ {A B} → ⊩ □ (A ⊃ B) ⊃ □ A ⊃ □ B
D = lam (lam (unbox v1 (unbox v0 (box (app v1* v0*)))))

T : ∀ {A} → ⊩ □ A ⊃ A
T = lam (unbox v0 v0*)

#4 : ∀ {A} → ⊩ □ A ⊃ □ □ A
#4 = lam (unbox v0 (box (box v0*)))


-- Some modalised theorems of the modal logic S4.

□D : ∀ {A B} → ⊩ □ (□ (A ⊃ B) ⊃ □ A ⊃ □ B)
□D = box (lam (lam (unbox v1 (unbox v0 (box (app v1* v0*))))))

□T : ∀ {A} → ⊩ □ (□ A ⊃ A)
□T = box (lam (unbox v0 v0*))

□#4 : ∀ {A} → ⊩ □ (□ A ⊃ □ □ A)
□#4 = box (lam (unbox v0 (box (box v0*))))


-- Some twice-modalised theorems of the modal logic S4.

□□D : ∀ {A B} → ⊩ □ □ (□ (A ⊃ B) ⊃ □ A ⊃ □ B)
□□D = box (box (lam (lam (unbox v1 (unbox v0 (box (app v1* v0*)))))))

□□T : ∀ {A} → ⊩ □ □ (□ A ⊃ A)
□□T = box (box (lam (unbox v0 v0*)))

□□#4 : ∀ {A} → ⊩ □ □ (□ A ⊃ □ □ A)
□□#4 = box (box (lam (unbox v0 (box (box v0*)))))
