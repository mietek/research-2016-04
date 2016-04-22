module Notes.Artemov2006.RCL where

open import AltArtemov


{-

S. Artemov (2006) “On two models of provability”, pp. 36-38


3.8.  Applications

4.  Reflection in typed combinatory logic and λ-calculus

Typed λ-calculi and Combinatory Logic are mathematical prototypes of
functional programming languages with types (cf., for example,
[62]).  There are reasons to believe that this area would benefit
from extending λ-calculi and Combinatory Logic by self-referential
capacities which enable systems to simultaneously operate with
related objects of different abstraction levels: functions, their high
level programs, their low level codes, etc.  Reflexive Combinatory
Logic RCL ([17]) was invented to meet these kinds of expectations.
RCL introduces a reflexivity mechanism into Combinatory Logic,
hence to λ-calculus.  RCL has the implicative intuitionistic (minimal)
logic as a type system, a rigid typing.  Reflexive combinatory terms
are built from variables, ‘old’ combinators  k  and  s,  and new
combinators  d,  o,  and  c.   The principles of RCL are:

-}


-- A1.  t ∶ A → A

A1 : ∀ {t A} → ⊩ t ∶ A ⊃ A
A1 = lam (down v0)


-- A2.  k ∶ (A → (B → A))

k : Tm
k = LAM (LAM V1)

A2 : ∀ {A B} → ⊩ k ∶ (A ⊃ B ⊃ A)
A2 = lam² (lam² v1²)


-- A3.  s ∶ ((A → (B → C)) → ((A → B) → (A → C)))

s : Tm
s = LAM (LAM (LAM (APP (APP V2 V0) (APP V1 V0))))

A3 : ∀ {A B C} → ⊩ s ∶ ((A ⊃ B ⊃ C) ⊃ (A ⊃ B) ⊃ A ⊃ C)
A3 = lam² (lam² (lam² (app² (app² v2² v0²) (app² v1² v0²))))


-- A4.  d ∶ (t ∶ A → A)

d : Tm
d = LAM (DOWN V0)

A4 : ∀ {t A} → ⊩ d ∶ (t ∶ A ⊃ A)
A4 = lam² (down² v0²)


-- A5.  o ∶ (u ∶ (A → B) → (v ∶ A → (u ∙ v) ∶ B))

o : Tm
o = LAM (LAM (APP² V1 V0))

A5 : ∀ {u v A B} → ⊩ o ∶ (u ∶ (A ⊃ B) ⊃ v ∶ A ⊃ (APP u v) ∶ B)
A5 = lam² (lam² (app³ v1² v0²))


-- A6.  c ∶ (t ∶ A → ! t ∶ (t ∶ A))

c : Tm
c = LAM (UP V0)

A6 : ∀ {t A} → ⊩ c ∶ (t ∶ A ⊃ quo t ∶ t ∶ A)
A6 = lam² (up² v0²)


-- Rule modus ponens,
--                         A → B    A
--                         -----------.
--                              B

MP : ∀ {A B} → ⊩ A ⊃ B → ⊩ A → ⊩ B
MP f x = app f x


{-

RCL has a natural provability semantics inherited from LP.  Combi-
natory terms stand for proofs in PA or in intuitionistic arithmetic
HA.  Formulas  t ∶ F  are interpreted as arithmetical statements about
provability,  Proof(t , F),  combinators  k,  s,  d,  o,  and  c
denote terms corresponding to proofs of arithmetical translations of
axioms A2-A6.
    RCL evidently contains implicative intuitionistic logic,
ordinary Combinatory Logic CL→, and is closed under the combinatory
application rule
                    u ∶ (A → B)    v ∶ A
                    ---------------------.
                         (u ∙ v) ∶ B

-}

X1 : ∀ {u v A B} → ⊩ u ∶ (A ⊃ B) ⊃ v ∶ A ⊃ (APP u v) ∶ B
X1 = lam (lam (app² v1 v0))


{-

Furthermore, RCL enjoys the internalization property ([17]): if
A₁, …, Aₙ ⊢ B  then for any set of variables  x₁, …, xₙ  of respective
types, it is possible to construct a term  t (x₁, …, xₙ)  such that

          x₁ ∶ A₁, …, xₙ ∶ Aₙ ⊢ t (x₁, …, xₙ) ∶ B.

-}

X2 : ∀ {Γ B} (d : Γ ⊢ B) → Γ ⊢ rep d ∶ B
X2 = int


{-

It is interesting to consider the following natural (though so far
informal) computational semantics for combinators of RCL.  This
semantics is based on the standard set-theoretic semantics of types,
i.e., a type is a set and the implication type  U → V  is a set of
functions from U to V.  Some elements of a given type may be
constructive objects which have _names,_ i.e., computational
programs.  Terms of RCL are names of constructive objects, some of
them specific, e.g., combinators  k,  s,  d,  o,  or  c.  The type
t ∶ F  is interpreted as a set consisting of the object corresponding
to term  t.
    Basic combinators of RCL are understood as follows.  Combinators
k  and  s  have the same meaning as in the combinatory logic CL→.
For example,  k  maps an element  x ∈ A  into the
constant function  λ y. x  with  y  ranging over  B.  The _denotate_
combinator  d ∶ (t ∶ F → F)  realizes the function which maps a
name (program) into the object with the given name.  A primary
example is the correspondence between indexes of computable
functions and functions themselves.  The _interpreter_ combinator
o ∶ (u ∶ (F → G) → (v ∶ F → (u ∙ v) ∶ G))  realizes the program
which maps program  u  and input  v  into the result of applying
u  to  v.  The _coding_ combinator  c ∶ (t ∶ F → ! t ∶ (t ∶ F)) maps
program  t  into its code  ! t  (alias, specific key in a database,
etc.).
    In the followup papers [109, 111], N. Krupski established that
typability and type restoration can be done in polynomial time and
that the derivability relation for RCL is decidable and PSPACE-
complete.
    In [1], some version of reflexive λ-calculus was considered that
has an unrestricted internalization property.


  [1]  J. Alt, S. Artemov (2001) “Reflective λ-calculus”
 [17]  S. Artemov (2004) “Kolmogorov and Gödel’s approach to
       intuitionistic logic: current developments”
 [62]  R. Constable (1998) “Types in logic, mathematics and
       programming”
[109]  N. Krupski (2006) “Some algorithmic questions in formal
       systems with internalization” (in Russian)
[111]  N. Krupski (2006) “Typing in reflective combinatory logic”

-}
