module Notes.Artemov2006.FLP where

open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)

open import AltArtemov


{-

S. Artemov (2006) “On two models of provability”, pp. 33-34


3.7.  The logic of single conclusion proofs

By definition, each single conclusion proof, also known as _functional
proofs_, proves a unique formula.  In the functional logic of proofs,
a formula  t ∶ F  still has the meaning  ‘t  is a proof of formula  F,’
but the class of its interpretations is limited to functional proof
systems only.  It is easy to see that single conclusion proofs lead
to modal identities inconsistent with any normal modal logic, e.g.,
x ∶ ⊤ → ¬ x ∶ (⊤ ∧ ⊤)  is a valid principle of the functional proofs
which, however, has the forgetful projection  □ ⊤ → ¬ □ (⊤ ∧ ⊤)
which is incompatible with any normal modal logic.
    The mathematical problem here was to give a full axiomatization
of all resulting tautologies in the language of LP (without the
operation ‘+,’ which does not work on functional proofs); this problem
was solved by V. Krupski in [112].
    The functionality property of proofs, which states that if
p ∶ F ∧ p ∶ G,  then  F  and  G  must coincide syntactically, does not
look like a propositional condition, since it operates with the strong
notion of syntactic coincidence.  An adequate propositional description
of this property was found in [29] using so-called _conditional
unification._  It was then generalized in [112, 113] to the full
language of the logic of proofs.
    Each formula  C  of type  t₁ ∶ F₁ ∧ … ∧ tₙ ∶ Fₙ  generates a set
of quasi-equations of type  Sc ≔ { t₁ = tⱼ ⇒ Fᵢ = Fⱼ ∣ 1 ≤ i, j ≤ n }.
A _unifier_  σ  of  Sc  is a substitution  σ  such that either
tᵢ σ ≢ tⱼ σ  or  Fᵢ σ ≡ Fⱼ σ  holds for any  i, j.  Here and below
‘X ≡ Y’  denotes the syntactic equality of  X  and  Y.  A = B (mod S)
means that for each unifier  σ  of system  S,  the property  A σ ≡ B σ
holds.  This conditional unification was shown to be decidable in the
cases under consideration (cf. [29, 112, 113]).  By _Unification Axiom_
we understand the schema

                 t₁ ∶ F₁ ∧ … ∧ tₙ ∶ Fₙ → (A ↔ B)

for each condition  C  of type  t₁ ∶ F₁ ∧ … ∧ tₙ ∶ Fₙ  and each  A, B
such that  A = B (mod Sc).
    The Logic of Functional Proofs FLP was introduced by V. Krupski in
[112].  The language of FLP is the language of LP without the operation
‘+’ and without proof constants.  The axioms and rules of FLP are:

-}


-- A0.  Axioms and rules of classical propositional logic


-- A1.  t ∶ (F → G) → (s ∶ F → (t ∙ s) ∶ G)

A1 : ∀ {t s F G} → ⊩ t ∶ (F ⊃ G) ⊃ s ∶ F ⊃ (APP t s) ∶ G
A1 = lam (lam (app² v1 v0))


-- A2.  t ∶ F → F

A2 : ∀ {t F} → ⊩ t ∶ F ⊃ F
A2 = lam (down v0)


-- A3.  t ∶ F → ! t ∶ (t ∶ F)

A3 : ∀ {t F} → ⊩ t ∶ F ⊃ quo t ∶ t ∶ F
A3 = lam (up v0)


-- A4.  Unification axiom

A4 : ∀ {t F G} → ⊩ t ∶ F ⊃ t ∶ G ⊃ F ≑ G
A4 = lam (lam (eq v1 v0))


id² : ∀ {A} → ⊩ LAM V0 ∶ (A ⊃ A)
id² = lam² v0²

test : ∀ {A B} → ⊩ (A ≠ (B ⊃ B)) ⊃ (LAM V0 ∶ A) ⊃ ⊥
test = lam (lam (app v1 (eq v0 id²)))

test² : ∀ {A B} → ⊩ LAM (LAM (APP V1 (EQ V0 (LAM² V0²)))) ∶ ((A ≠ (B ⊃ B)) ⊃ (LAM V0 ∶ A) ⊃ ⊥)
test² = nec test


--Γ ⊢ t₂ ∶ t ∶ A    Γ ⊢ t₂ ∶ t ∶ B
--Γ ⊢ (t ∶ A) ≑ (t ∶ B)




{-

----- 𝑣  ----- 𝑣
t ∶ A    t ∶ A
-------------- ≑
     A ≑ A

-}

refl : ∀ {Γ t A}
    → Γ ⊢ t ∶ A ⊃ A ≑ A
refl = lam (eq v0 v0)


{-

   ----- 𝑣        ----- 𝑣
   t ∶ A          t ∶ A
----------- ⇑  ----------- ⇑
! t ∶ t ∶ A    ! t ∶ t ∶ A
-------------------------- ≑
       t ∶ A ≑ t ∶ A

-}

refl2 : ∀ {Γ t A}
    → Γ ⊢ t ∶ A ⊃ t ∶ A ≑ t ∶ A
refl2 = lam (eq (up v0) (up v0))





{-


Γ ⊢ A ≑ B    Γ , t ∶ A ⊃ t ∶ B ⊢ C
------------------------------------
           Γ ⊢ C



    ------------- 𝑣  ----- 𝑣
    t ∶ A ⊃ t ∶ B    t ∶ A
    ---------------------- ∘
             t ∶ B
    ----------------------- 𝜆
    (t ∶ A ⊃ t ∶ B) ⊃ t ∶ B
------------------------------- 𝜆
t ∶ A ⊃ (t ∶ A ⊃ t ∶ B) ⊃ t ∶ B



         A ⊃ B

    t ∶ A ⊃ t ∶ B
    ----------------
A ≑ B    t ∶ B
-------------- ?  -------------
         t ∶ B    t ∶ A
         -------------- ≑
              B ≑ A
         -------------- 𝜆
          A ≑ B ⊃ B ≑ A

-}

-- TODO: unfinished
-- sym : ∀ {Γ A B}
--     → Γ ⊢ A ≑ B ⊃ B ≑ A
-- sym = {!!}


Ag-refl : ∀ {ℓ} {A : Set ℓ} {x : A}
    → x ≡ x
Ag-refl = ≡-refl

Ag-sym : ∀ {ℓ} {A : Set ℓ} {x y : A}
    → x ≡ y
    → y ≡ x
Ag-sym ≡-refl = ≡-refl

Ag-trans : ∀ {ℓ} {A : Set ℓ} {x y z : A}
    → x ≡ y    → y ≡ z
    → x ≡ z
Ag-trans ≡-refl ≡-refl = ≡-refl

Ag-subst : ∀ {ℓ ℓ′} {A : Set ℓ} {x y : A}
    → (P : A → Set ℓ′)    → x ≡ y    → P x
    → P y
Ag-subst P ≡-refl p = p

Ag-cong : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} {x y : A}
    → (f : A → B)    → x ≡ y
    → f x ≡ f y
Ag-cong f ≡-refl = ≡-refl


{-

    Theorem 3.7 (V. Krupski, [112, 113]).  The logic FLP is decidable,
sound, and complete with respect to the arithmetical provability
interpretation based on functional proof predicates.

    The logic of functional proofs was further developed in [114],
where its extension with references FLPref was introduced.  System
FLPref extends FLP with second-order variables which denote the
operation of reconstructing an object from its reference, e.g.,
determining a formula proven by a given derivation.  FLPref may be
also viewed as a natural formal system for admissible inference rules
in arithmetic.  See also follow-up articles [156, 187].


 [29]  S. Artemov, T. Strassen (1992) “The basic logic of proofs”
[112]  V. Krupski (1997) “Operational logic of proofs with
       functionality condition on proof predicate”
[113]  V. Krupski (2001) “The single-conclusion proof logic and
       inference rules specification”
[114]  V. Krupski (2006) “Referential logic of proofs”
[156]  T. Yavorskaya (Sidon), N. Rubtsova (2007) “Operations on proofs
       and labels”
[187]  T. Yavorskaya (Sidon) (2005) “Negative operations on proofs
       and labels”

-}

-- TODO: unfinished

-- (Γ ⊢ M ∶ A → Γ ⊢ M ∶ B) → (Γ ⊢ M ∶ B → Γ ⊢ M ∶ A)
-- -------------------------------------------------------- ≑I
--                    Γ ⊢ eq(F) ∶ A ≑ B

-- (F0 ∷ ∀ M. Γ ⊢ M ∶ A → Γ ⊢ M ∶ B)    (F1 ∷ ∀ M. Γ ⊢ M ∶ B → Γ ⊢ M ∶ A)
-- ------------------------------------------------------------------------------
--                           Γ ⊢ eq(F0, F1) ∶ A ≑ B

-- fwd(eq(F0,F1),M) = F0(M)   bwd(eq(F0,F1), N) = F1(N)

-- Γ ⊢ f₀ ∶ (m ∶ A ⊃ m ∶ B)    Γ ⊢ f₁ : (m ∶ B ⊃ m ∶ A)
-- ------------------------------------------------------
--              Γ ⊢
