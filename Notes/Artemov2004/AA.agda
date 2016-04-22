module Notes.Artemov2004.AA where

open import AltArtemov


{-

S. Artemov (2004) “Kolmogorov and Gödel’ approach to
intuitionistic logic: current developments”, pp. 220-221


5.8.  Reflection in λ-calculi

The Logic of Proofs naturally bridges two domains: the epistemic
represented by modal logic and the computational represented by typed
λ-calculi and combinatory logic.  LP may be considered both as a
realized modal logic S4 and as a typed combinatory logic with added
expressive power [21].  There is a natural analogy with the
Curry-Howard isomorphism which states the identity of intuitionistic
proofs and typed λ-terms understood as computational programs.  This
analogy may be expressed in precise mathematical form as in [14],
where the reflexive λ-calculus λ∞ was introduced.
    For the purposes of compactness and closeness to the object under
study, that is, the modal logic S4, the canonical formulation of LP
was chosen to be in the typed combinatory logic CL→ format rather than
in the more common λ-calculus format.  Needless to say, LP can emulate
the λ-abstraction operator [19], for example, in Curry style as is
standard in combinatory logic CL→ (see, for example, [84], p. 17).
Still, the problem of translating LP and its fragments into the format
of λ-terms is very important.  These studies are aimed at developing a
new generation of λ-calculi, more expressible than their predecessors.
Considering that λ-calculi have become a prototype of a certain class
of programming languages, any progress in this direction also
represents a special interest from that point of view.
    LP has many features not typical of λ-calculi, such as
polymorphism, self-referentiality, the classical logic in the
background, the capability to internalize its own derivations, and so
on.  The desire for the fundamental property of normalizability of
terms makes it necessary to give up polymorphism of terms and adopt
the approach that each term has a unique type.  Thus, self-
referentiality in the language of λ-terms becomes impossible.  Indeed,
the type of the outer occurrence of the variable  x  in  x ∶ A (x)
is syntactically different from the types of its inner occurrences.
Recall that formulae of type  x ∶ x ∶ F  are quite legal in LP and may
be easily interpreted in the standard provability semantics.  In [14]
it was shown that the internalization property may be extended to the
λ-calculus format.
    A λ-calculus has been developed based on the implicative
intuitionistic (minimal) logic as a type system.  In the system λ∞ in
[14], the role of atoms is played by both the usual propositional
variables (atomic types) and statements of the form  t ∶ F,  where
t  is a term and  F  is a type.  The ‘term ∶ type’ correspondence is a
rigid typing ‘a lá Church’.  The system λ∞ is based on the following
principles:

-}


-- 1.  λ∞ contains the natural deduction system for implicative
--     intuitionistic logic.


-- 2.  λ∞ postulates the principle  x ∶ A ⊢ A.  -}

P2 : ∀ {x A} → ⊩ x ∶ A ⊃ A
P2 = lam (down v0)


-- 3.  λ∞ enjoys the internalization rule: if  A₁, …, Aₙ ⊢ B,  then
--     for any set of fresh variables  x₁, …, xₙ  of corresponding
--     types it is possible to construct a λ-term  t (x₁, …, xₙ)
--     such that  x₁ ∶ A₁, …, xₙ ∶ Aₙ ⊢ t (x₁, …, xₙ) ∶ B.

P3 : ∀ {Γ B} (d : Γ ⊢ B) → Γ ⊢ rep d ∶ B
P3 = int


{-

A full description of the system λ∞ may be found in the paper [14].
    According to the formulation in [14], λ∞ has several countable
series of term-building operations.  Admissibility of the
internalization rule for λ∞ is proved as a metatheorem.  It would be
interesting to give an alternative formulation of λ∞ with the
postulated internalization rule added to rules 1 and 2, after which
all specific operations would become instances of internalization.
    Let the level of a λ∞-formula  F  be the maximal depth of the
typing operation in  F.  It is easy to see that the Curry-Howard
isomorphism corresponds in λ∞ to internalization on level 0, which may
give some idea about the new expressive abilities of the system λ∞.
    The choice of a reduction system and the existence and uniqueness
of normal forms in λ∞ all turn out to be connected with the depth of
type preservation during reductions, which is a new phenomenon
compared to the ordinary λ-calculus.  This theory is currently under
development.


[14]  J. Alt, S. Artemov (2001) “Reflective λ-calculus”
[19]  S. Artemov (2001) “Explicit provability and constructive
      semantics”
[21]  S. Artemov (2001) “Unified semantics for modality and lambda-
      terms via proof polynomials”
[84]  A. Troelstra, H. Schwichtenberg (1996) “Basic proof theory”

-}
