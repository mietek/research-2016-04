module Notes.AltArtemov2001.Definition where

open import AltArtemov


{-

J. Alt, S. Artemov (2001) “Reflective λ-calculus”, pp. 25-


2.  Reflective λ-calculus

The reflective λ-calculus λ∞ below is a joint calculus of propositions
(types) and proofs (λ-terms) with rigid typing.  Every term and all
subterms of a term carry a fixed type.  In other words, in λ∞ we
assume a Church style rigid typing rather than a Curry style type
assignment system.


2.1.  Types and typed terms

The language of reflective λ-calculus includes

-}


-- propositional letters  p₁, p₂, p₃, …


-- type constructors (connectives)  →, ∧


-- term constructors (functional symbols):
-- unary   !, ⇑ⁿ, ⇓ⁿ, 𝜋₀ⁿ, 𝜋₁ⁿ
-- binary  ∘ⁿ, 𝑝ⁿ
-- for  n = 1, 2, 3 …

!_ : ∀ t → Tm
!_ = quo

⇑[_]_ : ∀ n t → Tm
⇑[_]_ = UP[_]
⇑_  = UP
⇑²_ = UP²
⇑³_ = UP³

⇓[_]_ : ∀ n t → Tm
⇓[_]_ = DOWN[_]
⇓_  = DOWN
⇓²_ = DOWN²
⇓³_ = DOWN³

{-𝜋₀[_]_ : ∀ n t → Tm
𝜋₀[_]_ = FST[_]
𝜋₀_  = FST
𝜋₀²_ = FST²
𝜋₀³_ = FST³

𝜋₁[_]_ : ∀ n t → Tm
𝜋₁[_]_ = SND[_]
𝜋₁_  = SND
𝜋₁²_ = SND²
𝜋₁³_ = SND³-}

_∘[_]_ : ∀ t n s → Tm
t ∘[ n ] s = APP[ n ] t s
_∘_  = APP
_∘²_ = APP²
_∘³_ = APP³

{-𝑝[_]⟨_,_⟩ : ∀ n t s → Tm
𝑝[_]⟨_,_⟩ = PAIR[_]
𝑝⟨_,_⟩  = PAIR
𝑝²⟨_,_⟩ = PAIR²
𝑝³⟨_,_⟩ = PAIR³-}


-- operator symbols  ∶, 𝜆¹, 𝜆², …, 𝜆ⁿ, …

𝜆[_]_ : ∀ n t → Tm
𝜆[_]_ = LAM[_]
𝜆_  = LAM
𝜆²_ = LAM²
𝜆³_ = LAM³


-- a countably infinite supply of _variables_  x₁, x₂, x₃, …
-- of each type  F  (definition below), each variable  x  is a term of
-- its unique pre-assigned type.

𝑣[_]_ : ∀ n i → Tm
𝑣[_]_ = VAR[_]
𝑣0  = V0
𝑣0² = V0²
𝑣0³ = V0³
𝑣1  = V1
𝑣1² = V1²
𝑣1³ = V1³
𝑣2  = V2
𝑣2² = V2²
𝑣2³ = V2³


{-

_Types_ and _(well-typed, well-defined, well-formed) terms_ are
defined by a simultaneous induction according to the calculus λ∞
below.
    1.  Propositional letters are _(atomic) types_
    2.  _Types_ (formulas)  F  are built according to the grammar

                  F = p | F → F | F ∧ F | t ∶ F

where  p  is an atomic type,  t  a well-formed term having type  F.
Types of format  t ∶ F  where  t  is a term and  F  a type are called
_type assertions_ or _quasi-atomic types._  Note that only correct
type assertions  t ∶ F  are syntactically allowed inside types.  The
informal semantics for  t ∶ F  is  _t  is a proof of  F;_  so a
formula
                      tₙ ∶ tₙ₋₁ ∶ … ∶ t₁ ∶ A

can be read as  “tₙ  is a proof that  tₙ₋₁  is a proof that … is
a proof that  t₁  proves  A”.  For the sake of brevity we will refer
to types as terms of depth 0.
    3.  _Inhabited types_ and well-formed terms (or terms for short)
are constructed according to the calculus λ∞ below.
    A derivation in λ∞ is a rooted tree with nodes labelled by types,
in particular, type assertions.  Leaves of a derivation are labelled
by axioms of λ∞ which are arbitrary types or type assertions  x ∶ F
where  F  is a type and  x  a variable of type  F.  Note that the set
of axioms is thus also defined inductively according to λ∞: as soon as
we are able to establish that  F  is a type (in particular, for a
quasi-atomic type  s ∶ G  this requires establishing by means of λ∞
that  s  indeed is a term of type  G),  we are entitled to use
variables of type  F  as new axioms.
    A _context_ is a collection of quasi-atomic types
x₁ ∶ A₁, x₂ ∶ A₂, …, xₙ ∶ Aₙ  where  xᵢ, xⱼ  are distinct variables
for  i ≠ j.  A derivation tree is _in a context  Γ_  if all leaves of
the derivation are labelled by some quasi-atomic types from  Γ.
    A step down from leaves to the root is performed by one of the
inference rules of λ∞.  Each rule comes in levels  n = 0, 1, 2, 3, ….
A rule has one or two premises which are types (in particular, type
assertions), and a conclusion.  The intended reading of such a rule is
that if premises are inhabited types, then the conclusion is also
inhabited.  If the level of a rule is greater than 0, then the
premise(s) and the conclusion are all type assertions.  Such a rule is
regarded also as a term formation rule with the intended reading: _the
conclusion  t ∶ F  is a correct type assertion provided the premise(s)
are correct._
    If  t ∶ F  appears as a label in (the root of) a derivation tree,
we say that  t  is a _term of type F._  We also refer to terms as
well-defined, well-typed, well-formed terms.

In λ∞ we use the natural deduction format, where derivations are
represented by proof trees with assumptions, both open (charged) and
closed (discharged).  We will also use the sequent style notation for
derivations in λ∞ by reading  Γ ⊢ F  as an λ∞-derivation of  F  in  Γ.
Within the current definition below we assume that  n = 0, 1, 2, …
and  𝐯 = (v₁, v₂, …, vₙ).  In particular, if  n = 0  then  𝐯  is
empty.  We also agree on the following vector-style notations:

-}


-- 𝐭 ∶ A  denotes
-- tₙ ∶ tₙ₋₁ ∶ … ∶ t₁ ∶ A  (e.g.  𝐭 ∶ A  is  A, when  n = 0),


-- 𝐭 ∶ {A₁, A₂, …, Aₙ}  denotes  {t₁ ∶ A₁, t₂, ∶ A₂, …, tₙ ∶ Aₙ},


-- 𝜆ⁿ 𝐱. 𝐭 ∶ B  denotes
-- 𝜆ⁿ xₙ. tₙ ∶ 𝜆ⁿ⁻¹ xₙ₋₁. tₙ₋₁ ∶ … ∶ 𝜆 x₁. t₁ ∶ B,

𝜆ⁿ_ = λ {n} → LAMs[ n ]
𝑣ⁿ_ = λ {n} → VARs[ n ]


-- (𝐭 ∘ⁿ 𝐬) ∶ B  denotes
-- (tₙ ∘ⁿ sₙ) ∶ (tₙ₋₁ ∘ⁿ⁻¹ sₙ₋₁) ∶ … ∶ (t₁ ∘ s₁) ∶ B,

_∘ⁿ_ = λ {n} → APPs[ n ]


-- ⇑ⁿ 𝐭 ∶ B  denotes  ⇑ⁿ tₙ ∶ ⇑ⁿ⁻¹ tₙ₋₁ ∶ … ∶ ⇑ t₁ ∶ B,
-- likewise for all other functional symbols of λ∞.

⇑ⁿ_     = λ {n} → UPs[ n ]
⇓ⁿ_     = λ {n} → DOWNs[ n ]
--𝜋₀ⁿ_    = λ {n} → FSTs[ n ]
--𝜋₁ⁿ_    = λ {n} → SNDs[ n ]
--𝑝ⁿ⟨_,_⟩ = λ {n} → PAIRs[ n ]


{-

Derivations are generated by the following clauses.  Here  A, B, C
are formulas,  Γ  a finite set of types,  𝐬, 𝐭, 𝐮  are n-vectors of
pseudo-terms,  𝐱  are n-vectors of variables,  n = 0, 1, 2, ….

-}


-- Natural deduction rule
--
-- (𝒗)  𝐱 ∶ A
--
-- Its sequent form
--
-- (𝒗)  Γ ⊢ 𝐱 ∶ A,  if  𝐱 ∶ A  is in  Γ

𝒗ⁿ_ : ∀ {n A Γ}
    → (i : Γ ∋ A)
    → Γ ⊢ 𝑣ⁿ_ {n} (ix i) ∶⋯∶ A
𝒗ⁿ_  = λ {n} → var[ n ]
𝒗𝟎  = v0
𝒗𝟎² = v0²
𝒗𝟎³ = v0³
𝒗𝟏  = v1
𝒗𝟏² = v1²
𝒗𝟏³ = v1³
𝒗𝟐  = v2
𝒗𝟐² = v2²
𝒗𝟐³ = v2³


-- Natural deduction rule
--
--            𝐭 ∶ B
-- (𝝀)  ------------------
--      𝜆ⁿ 𝐱. 𝐭 ∶ (A → B)
--
-- provided  xₙ ∶ xₙ₋₁ ∶ … ∶ x₁ ∶ A,  xᵢ  occurs free neither in  tⱼ
-- for  i ≠ j  nor in  A → B.  Premises corresponding to
-- xₙ ∶ xₙ₋₁ ∶ … ∶ x₁ ∶ A  (if any) are discharged.  In the full
-- sequent form this rule is
--
--         Γ, xₙ ∶ xₙ₋₁ ∶ … ∶ x₁ ∶ A ⊢ tₙ ∶ tₙ₋₁ ∶ … ∶ t₁ ∶ B
-- (𝝀)  ----------------------------------------------------------
--      Γ ⊢ 𝜆ⁿ xₙ. tₙ ∶ 𝜆ⁿ⁻¹ xₙ₋₁. tₙ₋₁ ∶ … ∶ 𝜆 x₁. t₁ ∶ (A → B)
--
-- where none of  𝐱  occurs free in the conclusion sequent.

𝝀ⁿ_ : ∀ {n} {𝐭 : Tms n} {A B Γ}
    → Γ , A ⊢ 𝐭 ∶⋯∶ B
    → Γ ⊢ 𝜆ⁿ 𝐭 ∶⋯∶ (A ⊃ B)
𝝀ⁿ_ = λ {n} → lam[ n ]
𝝀_  = lam
𝝀²_ = lam²
𝝀³_ = lam³


-- All the rules below do not bind/unbind variables.
--
--      𝐭 ∶ (A → B)    𝐬 ∶ A
-- (∙)  ---------------------
--          (𝐭 ∘ⁿ 𝐬) ∶ B

_∙ⁿ_ : ∀ {n} {𝐭 𝐬 : Tms n} {A B Γ}
    → Γ ⊢ 𝐭 ∶⋯∶ (A ⊃ B)    → Γ ⊢ 𝐬 ∶⋯∶ A
    → Γ ⊢ 𝐭 ∘ⁿ 𝐬 ∶⋯∶ B
_∙ⁿ_ = λ {n} → app[ n ]
_∙_  = app
_∙²_ = app²
_∙³_ = app³


--        𝐭 ∶ A    𝐬 ∶ B
-- (𝒑)  ------------------
--      𝑝ⁿ(𝐭, 𝐬) ∶ (A ∧ B)

{-𝒑ⁿ⟨_,_⟩ : ∀ {n} {𝐭 𝐬 : Tms n} {A B Γ}
    → Γ ⊢ 𝐭 ∶⋯∶ A    → Γ ⊢ 𝐬 ∶⋯∶ B
    → Γ ⊢ 𝑝ⁿ⟨ 𝐭 , 𝐬 ⟩ ∶⋯∶ (A ∧ B)
𝒑ⁿ⟨_,_⟩ = λ {n} → pair[ n ]
𝒑⟨_,_⟩  = pair
𝒑²⟨_,_⟩ = pair²
𝒑³⟨_,_⟩ = pair³-}


--       𝐭 ∶ (A₀ ∧ A₁)
-- (𝝅ᵢ)  ------------- (i = 0, 1)
--         𝜋ᵢⁿ 𝐭 ∶ Aᵢ

{-𝝅₀ⁿ_ : ∀ {n} {𝐭 : Tms n} {A₀ A₁ Γ}
    → Γ ⊢ 𝐭 ∶⋯∶ (A₀ ∧ A₁)
    → Γ ⊢ 𝜋₀ⁿ 𝐭 ∶⋯∶ A₀
𝝅₀ⁿ_ = λ {n} → fst[ n ]
𝝅₀_  = fst
𝝅₀²_ = fst²
𝝅₀³_ = fst³

𝝅₁ⁿ_ : ∀ {n} {𝐭 : Tms n} {A₀ A₁ Γ}
    → Γ ⊢ 𝐭 ∶⋯∶ (A₀ ∧ A₁)
    → Γ ⊢ 𝜋₁ⁿ 𝐭 ∶⋯∶ A₁
𝝅₁ⁿ_ = λ {n} → snd[ n ]
𝝅₁_  = snd
𝝅₁²_ = snd²
𝝅₁³_ = snd³-}


--          𝐭 ∶ u ∶ A
-- (⬆)  --------------------
--      ⇑ⁿ 𝐭 ∶ ! u ∶ u ∶ A

⬆ⁿ_ : ∀ {n} {𝐭 : Tms n} {u A Γ}
    → Γ ⊢ 𝐭 ∶⋯∶ u ∶ A
    → Γ ⊢ ⇑ⁿ 𝐭 ∶⋯∶ ! u ∶ u ∶ A
⬆ⁿ_ = λ {n} → up[ n ]
⬆_  = up
⬆²_ = up²
⬆³_ = up³


--      𝐭 ∶ u ∶ A
-- (⬇)  -----------
--       ⇑ⁿ 𝐭 ∶ A

⬇ⁿ_ : ∀ {n} {𝐭 : Tms n} {u A Γ}
    → Γ ⊢ 𝐭 ∶⋯∶ u ∶ A
    → Γ ⊢ ⇓ⁿ 𝐭 ∶⋯∶ A
⬇ⁿ_ = λ {n} → down[ n ]
⬇_  = down
⬇²_ = down²
⬇³_ = down³


{-

Remark 1.  The intuitionistic logic for implication/conjunction and
λ-calculus are the special cases for rules with  n = 0  and  n = 1
only, respectively, if we furthermore restrict all of the displayed
formulas to types which do not contain quasi-atoms.

Example 1.  Here are some examples of λ∞-derivations in the sequent
format (cf. 3.2).  We skip the trivial axiom parts for brevity.

-}


--       y ∶ x ∶ A ⊢ ⇓ y ∶ A
-- 1)  --------------------------
--     ⊢ 𝜆 y. ⇓ y ∶ (x ∶ A → A)

E1-1 : ∀ {x A} → ⊩ 𝜆 ⇓ 𝑣0 ∶ (x ∶ A ⊃ A)
E1-1 = 𝝀² ⬇² v0²


--        y ∶ x ∶ A ⊢ ⇑ y ∶ ! x ∶ x ∶ A
-- 2)  ------------------------------------
--     ⊢ 𝜆 y. ⇑ y ∶ (x ∶ A → ! x ∶ x ∶ A)

E1-2 : ∀ {x A} → ⊩ 𝜆 ⇑ 𝑣0 ∶ (x ∶ A ⊃ ! x ∶ x ∶ A)
E1-2 = 𝝀² ⬆² 𝒗𝟎²


--         u ∶ x ∶ A, v ∶ y ∶ B ⊢ 𝑝²(u, v) ∶ 𝑝(x, y) ∶ (A ∧ B)
--     -----------------------------------------------------------
-- 3)  u ∶ x ∶ A ⊢ 𝜆² v. 𝑝²(u, v) ∶ 𝜆 y. 𝑝(x, y) ∶ (B → (A ∧ B))
--     ------------------------------------------------------------
--     ⊢ 𝜆² u v. 𝑝²(u, v) ∶ 𝜆 x y. 𝑝(x, y) ∶ (A → (B → (A ∧ B)))

--E1-3 : ∀ {A B} → ⊩ 𝜆² 𝜆² 𝑝²⟨ 𝑣1² , 𝑣0² ⟩ ∶ 𝜆 𝜆 𝑝⟨ 𝑣1 , 𝑣0 ⟩ ∶ (A ⊃ B ⊃ A ∧ B)
--E1-3 = 𝝀³ 𝝀³ 𝒑³⟨ 𝒗𝟏³ , 𝒗𝟎³ ⟩


--                u ∶ x ∶ A, v ∶ y ∶ B ⊢ 𝑝²(u, v) ∶ 𝑝(x, y) ∶ (A ∧ B)
--         ------------------------------------------------------------------
-- 4)      u ∶ x ∶ A, v ∶ y ∶ B ⊢ ⇑ 𝑝²(u, v) ∶ ! 𝑝(x, y) ∶ 𝑝(x, y) ∶ (A ∧ B)
--     --------------------------------------------------------------------------
--     ⊢ 𝜆 u v. ⇑ 𝑝²(u, v) ∶ (x ∶ A → (y ∶ B → ! 𝑝(x, y) ∶ 𝑝(x, y) ∶ (A ∧ B)))

--E1-4 : ∀ {x y A B} → ⊩ 𝜆 𝜆 ⇑ 𝑝²⟨ 𝑣1 , 𝑣0 ⟩ ∶ (x ∶ A ⊃ y ∶ B ⊃ ! 𝑝⟨ x , y ⟩ ∶ 𝑝⟨ x , y ⟩ ∶ (A ∧ B))
--E1-4 = 𝝀² 𝝀² ⬆² 𝒑³⟨ 𝒗𝟏² , 𝒗𝟎² ⟩


{-

Note that unlike in the previous example we cannot introduce  𝜆²  in
place of  𝜆  at the last stage here since the resulting sequent would
be
     ⊢ 𝜆² u v. ⇑ 𝑝²(u, v) ∶ 𝜆 x y. ! 𝑝(x, y) ∶ (A → (B → 𝑝(x, y) ∶ (A ∧ B)))

which is illegal.
    Here is an informal explanation of why such a derivation should
not be permitted.  Substituting different terms for  x  and  y  in the
last sequent produces different types from  A → (B → 𝑝(x, y) ∶ (A ∧ B)),
whereas neither of the terms  𝜆 x y. ! 𝑝(x, y)  and  𝜆² u v. ⇑ 𝑝²(u, v)
changes after such substitutions.  This is bad syntactically, since
the same terms will be assigned different types.  Semantically this is
bad either, since this would violate the one proof - one theorem
convention.

Proposition 1.  (Closure under substitution)  If  t (x)  is a well-
defined term,  x  a variable of type  A,  s  a term of type  A
free for  x  in  t (x),  then  t (s)  is a well-defined term of the
same type as  t (x).

-}

-- TODO


{-

Proposition 2.  (Uniqueness of Types)  If both  t ∶ F  and  t ∶ F′
are well-typed terms, then  F ≡ F′.

-}

-- TODO


{-

Theorem 1.  (Internalization Property for λ∞)  Let λ∞ derive

                     A₁, A₂, …, Aₘ ⊢ B.

Then one can build a well-defined term  t (x₁, x₂, …, xₘ)  with
fresh variables  𝐱  such that λ∞ also derives

      x₁ ∶ A₁, x₂ ∶ A₂, …, xₘ ∶ Aₘ ⊢ t (x₁, x₂, …, xₘ) ∶ B.

-}

T1 : ∀ {Γ B} (d : Γ ⊢ B) → Γ ⊢ rep d ∶ B
T1 = int


{-

Proof.  We increment  n  at every node of the derivation
A₁, A₂, …, Aₘ ⊢ B.  The base case is obvious.  We will check the most
principal step clause (𝝀) leaving the rest as an exercise.  Let the
last step of a derivation be

       Γ, yₙ ∶ yₙ₋₁ ∶ … ∶ y₁ ∶ A ⊢ tₙ ∶ tₙ₋₁ ∶ … ∶ t₁ ∶ B
    -----------------------------------------------------------.
    Γ ⊢ 𝜆ⁿ yₙ. tₙ ∶ 𝜆ⁿ⁻¹ yₙ₋₁. tₙ₋₁ ∶ … ∶ 𝜆 y₁. t₁ ∶ (A → B)

By the induction hypothesis, for some term  s (𝐱, xₘ₊₁)  of fresh
variables  𝐱, xₘ₊₁

    𝐱 ∶ Γ, xₘ₊₁ ∶ yₙ ∶ yₙ₋₁ ∶ … ∶ y₁ ∶ A ⊢ s (𝐱, xₘ₊₁) ∶ tₙ ∶ tₙ₋₁ ∶ … ∶ t₁ ∶ B.

Apply the rule (𝝀) for  n + 1  to obtain

    𝐱 ∶ Γ ⊢ 𝜆ⁿ⁺¹ xₘ₊₁. s ∶ 𝜆ⁿ yₙ. tₙ ∶ 𝜆ⁿ⁻¹ yₙ₋₁. tₙ₋₁ ∶ … ∶ 𝜆 y₁. t₁ ∶ (A → B),

and put  t (x₁, x₂, …, xₘ) = 𝜆ⁿ⁺¹ xₘ₊₁. s (𝐱, xₘ₊₁).

-}
