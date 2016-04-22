module Notes.Artemov2004.RCL where

open import AltArtemov


{-

S. Artemov (2004) “Kolmogorov and Gödel’ approach to
intuitionistic logic: current developments”, pp. 221-224


5.9.  The Reflexive Combinatory Logic

Systems of combinatory logic are usually more compact than their
corresponding λ-calculi.  Reflexive λ-calculus is no exception.
    Below a reflexive combinatory logic RCL→ with rigid typing based
on the Hilbert-style calculus for the implicative intuitionistic logic
is formulated.  Terms in RCL→ are built from rigidly typed variables
and constants.
    The language of RCL→, well-formed formulae, and derivable formulae
are defined by mutual induction.
    1.  The language of RCL→ contains propositional variables  p₀, p₁, …
and the Boolean connective  →.  Each propositional variable is an
(atomic) formula.
    2.  If  S  and  T  are formulae, then  S → T  is also a formula.
    3.  Each formula F  has its own fixed set of proof variables
x₀, x₁, ….  If  x  is a variable of type  F,  then  x ∶ F  is a
formula.  In this subsection the statements  “t ∶ F  is a formula” and
“t  is a term of type  F”  are used interchangeably.
    4.  Each axiom A1-A6 is a formula.

-}


-- A1.  For each pair of formulae  A  and  t ∶ A,  there is an axiom
--      t ∶ A → A.

A1 : ∀ {t A} → ⊩ t ∶ A ⊃ A
A1 = lam (down v0)


-- A2.  For each formula  A → (B → A),  a constant  k  is fixed along
--      with an axiom  k ∶ (A → (B → A)).

k : Tm
k = LAM (LAM V1)

A2 : ∀ {A B} → ⊩ k ∶ (A ⊃ B ⊃ A)
A2 = lam² (lam² v1²)


-- A3.  For each formula  (A → (B → C)) → ((A → B) → (A → C)),
--      a constant  s  is fixed along with an axiom
--      s ∶ ((A → (B → C)) → ((A → B) → (A → C))).

s : Tm
s = LAM (LAM (LAM (APP (APP V2 V0) (APP V1 V0))))

A3 : ∀ {A B C} → ⊩ s ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
A3 = lam² (lam² (lam² (app² (app² v2² v0²) (app² v1² v0²))))


-- A4.  For each formula  t ∶ A → A,  a constant  d  is fixed along with
--      an axiom  d ∶ (t ∶ A → A).

d : Tm
d = LAM (DOWN V0)

A4 : ∀ {t A} → ⊩ d ∶ (t ∶ A ⊃ A)
A4 = lam² (down² v0²)


-- A5.  If  A, B, u ∶ (A → B), v ∶ A  are formulae, then  (u ∙ v) ∶ B
--      is also a formula, and for the formula
--      u ∶ (A → B) → (v ∶ A → (u ∙ v) ∶ B)  a constant  o  is fixed
--      along with an axiom
--      o ∶ (u ∶ (A → B) → (v ∶ A → (u ∙ v) ∶ B)).

o : Tm
o = LAM (LAM (APP² V1 V0))

A5 : ∀ {u v A B} → ⊩ o ∶ (u ∶ (A ⊃ B) ⊃ v ∶ A ⊃ (APP u v) ∶ B)
A5 = lam² (lam² (app³ v1² v0²))


-- A6.  If  A  and  t ∶ A  are formulae, then  ! t ∶ t ∶ A  is also
--      a formula, and for the formula  t ∶ A → ! t ∶ t ∶ A,  a constant
--      c  is fixed along with an axiom  c ∶ (t ∶ A → ! t ∶ t ∶ A).

c : Tm
c = LAM (UP V0)

A6 : ∀ {t A} → ⊩ c ∶ (t ∶ A ⊃ quo t ∶ t ∶ A)
A6 = lam² (up² v0²)


{-
    5.  Each formula derivable from hypotheses is a well-formed
formula.  _Hypotheses_ are any finite multiset  Γ  of formulae.
A derivation from the hypotheses  Γ  is a finite sequence of formulae,
where each formula is a hypothesis from  Γ,  or is an axiom, or
follows from previous formulae in the sequence by the _modus ponens_
rule,
                        A → B    A
                        -----------.
                             B

The notation  Γ ⊢ F  means that there exists a derivation from the
hypotheses  Γ  containing  F.
    RCL→ has a natural semantics inherited from LP, namely the
provability semantics.  Combinatory terms stand for proofs in, say, PA
or in intuitionistic arithmetic HA.  The formulae  t ∶ F  are
interpreted as arithmetical statements about provability,
Proof(t, F),  and the combinators  k, s, d, o, c  denote terms
corresponding to proofs of arithmetical translations of axioms in
A2-A6.
    Terminology of formulae in RCL→ can be translated into the usual
typed language.  Under this translation well-formed formulae become
_types,_ objects  t  in formulae  t ∶ F  become _combinatory terms of
type  F,_  constants become _constant combinators_ of a given type,
hypotheses become a _context,_ formulae derivable from  Γ  become
_inhabited types in the context  Γ,_  and so on.
    RCL→ evidently contains implicative intuitionistic logic, the
usual combinatory logic CL→.  Below is an example of how RCL→ emulates
the combinatory application rule

                    u ∶ (A → B)    v ∶ A
                    ---------------------.
                         (u ∙ v) ∶ B

1.  u ∶ (A → B)                                    hypothesis
2.  v ∶ A                                           hypothesis
3.  o ∶ (u ∶ (A → B) → (v ∶ A → (u ∙ v) ∶ B))    A5
4.  o ∶ (u ∶ (A → B) → (v ∶ A → (u ∙ v) ∶ B))    A1
     → (u ∶ (A → B) → (v ∶ A → (u ∙ v) ∶ B))
5.  u ∶ (A → B) → (v ∶ A → (u ∙ v) ∶ B)          from 3, 4
6.  v ∶ A → (u ∙ v) ∶ B                            from 1, 5
7.  (u ∙ v) ∶ B                                     from 2, 6

-}

X1 : ∀ {u v A B} → ⊩ u ∶ (A ⊃ B) ⊃ v ∶ A ⊃ (APP u v) ∶ B
X1 = lam (lam (app (app (app A1 A5) v1) v0))


{-

Here is another example of a derivation in RCL→, this time without
hypotheses.  Let  f ∶ A  be one of axioms A2-A6.

1.  f ∶ A                         axiom
2.  c ∶ (f ∶ A → ! f ∶ f ∶ A)    A6
3.  c ∶ (f ∶ A → ! f ∶ f ∶ A)    A1
     → (f ∶ A → ! f ∶ f ∶ A)
4.  f ∶ A → ! f ∶ f ∶ A          from 2, 3
5.  ! f ∶ f ∶ A                   from 1, 4

-}

X2 : ∀ {f A} → ⊩ f ∶ A ⊃ quo f ∶ f ∶ A
X2 = lam (app (app A1 A6) v0)


{-

Theorem.  RCL→ enjoys the internalization property:
if  A₁, …, Aₙ ⊢ B,  then for any set of fresh variables  x₁, …, xₙ
of corresponding types it is possible to construct a term
t (x₁, …, xₙ)  such that

          x₁ ∶ A₁, …, xₙ ∶ Aₙ ⊢ t (x₁, …, xₙ) ∶ B.

-}

X3 : ∀ {Γ B} (d : Γ ⊢ B) → Γ ⊢ rep d ∶ B
X3 = int


{-

Proof.  By induction on the derivation of  A₁, …, Aₙ ⊢ B.  Consider
the hypotheses  Γ′ = {x₁ ∶ A₁, …, xₙ ∶ Aₙ}.  If  B  is  Aᵢ,  then let
t ≔ xᵢ.  If  B  is the axiom A1, then let  t  be the constant  d  of
type  s ∶ A → A  and use A4.  If  B  is an axiom A2-A6 of the form
f ∶ A,  then let  t  be  ! f  and use the latter example above.  Since
! f ∶ f ∶ A  is derivable without hypotheses, it is also derivable
from  Γ′.  Finally, suppose that  B  is obtained by the _modus ponens_
rule from  A → B  and  A.  By the induction hypothesis,
Γ′ ⊢ p (x⃗) ∶ (A → B)  and  Γ′ ⊢ q (x⃗) ∶ A.  Let  t  be
p (x⃗) ∙ q (x⃗)  and use the former example above to show that
Γ′ ⊢ t ∶ B.                                                         ■
    One of the goals of RCL→ is to introduce a more expressive system
of types and terms intended for programming language applications.
Thus, it is interesting to consider the following natural (though
informal) computational semantics for combinators of RCL→.  This
semantics is based on the standard set-theoretic semantics of types,
that is, a type is a set and the implication type  U → V  is a set of
functions from  U  to  V.  Some elements of a given type may be
constructive objects which have _names_, that is, computational
programs.  Terms of RCL→ are names of constructive objects, which are
either specific (for example, combinators  k, s, d, o,  or  c)  or
variable.  The type  t ∶ F  is interpreted as a set consisting of the
object corresponding to the term  t.  Basic combinators of RCL→ are
understood as follows:

k ∶ (A → (B → A))                                constant functions
s ∶ ((A → (B → C)) → ((A → B) → (A → C)))    superposition
d ∶ (t ∶ F → F)                                   denotate
o ∶ (u ∶ (F → G) → (v ∶ F → (u ∙ v) ∶ G))       interpreter
c ∶ (t ∶ F → ! t ∶ (t ∶ F))                       coding

The combinators  k  and  s  are borrowed from the combinatory logic
CL→ along with their standard functional semantics.  For example,  k
maps an element  x ∈ A  into the constant function  λ y. x  with  y
ranging over  B.
    The _denotate_ combinator  d ∶ (t ∶ F → G)  realizes the
fundamental denotate function which maps a name (program) into the
object with the given name.  A canonical example is the correspondence
between indexes of computable functions and the functions themselves.
    The _interpreter_ combinator
o ∶ (u ∶ (F → G) → (v ∶ F → (u ∙ v) ∶ G))  realizes the interpreter
program which maps the program  u  and the input  v  into the result of
applying  u  to  v.
    The _coding_ combinator  c ∶ (t ∶ F → ! t ∶ (t ∶ F))  maps
a program  t  into its code  ! t  (alias, specific key in a database,
and so on).

-}
