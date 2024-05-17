module Everything where


--------------------------------------------------------------------------------

-- Some theorems of propositional logic and the λ-calculus, and some first-
-- and second-level realisations of theorems of the modal logic S4.
import Try1.Examples.AltArtemov

-- Some theorems of propositional logic and the modal logic S4.
import Try1.Examples.S4

-- Demonstration of forgetful projection from the reflective λ-calculus to
-- the modal logic S4.
import Try1.Examples.ForgetfulProjection

-- Demonstration of the isomorphism between propositional logic and the
-- λ-calculus, and between first- and second-level realisations of theorems
-- of the modal logic S4.
import Try1.Examples.Isomorphism

-- Some examples of reasoning with negation and principle of explosion.
import Try1.Examples.Negation

-- Descriptions of the reflective λ-calculus (λ∞) and reflective combinatory
-- logic (RCL).
import Try1.Notes.Artemov2004.AA
import Try1.Notes.Artemov2004.RCL

-- Descriptions of the logic of functional proofs (FLP) and RCL.
import Try1.Notes.Artemov2006.FLP
import Try1.Notes.Artemov2006.RCL


--------------------------------------------------------------------------------

import Try1.Data.Nat.Missing
import Try1.Data.Maybe.Missing

import Try1.AltArtemov
import Try1.AltArtemov.Context
import Try1.AltArtemov.Context.Core
import Try1.AltArtemov.Context.Notation
import Try1.AltArtemov.Context.Properties
import Try1.AltArtemov.Derivation
import Try1.AltArtemov.Derivation.Core
import Try1.AltArtemov.Derivation.Notation.Level1
import Try1.AltArtemov.Derivation.Notation.Level2
import Try1.AltArtemov.Derivation.Notation.Level3
import Try1.AltArtemov.Derivation.Notation.Level4
import Try1.AltArtemov.Derivation.Properties
import Try1.AltArtemov.Term
import Try1.AltArtemov.Term.Core
import Try1.AltArtemov.Term.Inversions
import Try1.AltArtemov.Term.Notation.Level1
import Try1.AltArtemov.Term.Notation.Level2
import Try1.AltArtemov.Term.Notation.Level3
import Try1.AltArtemov.Term.Notation.Level4
import Try1.AltArtemov.Term.Properties
import Try1.AltArtemov.TermVector
import Try1.AltArtemov.TermVector.Core
import Try1.AltArtemov.TermVector.Notation
import Try1.AltArtemov.Type
import Try1.AltArtemov.Type.Core
import Try1.AltArtemov.Type.Inversions
import Try1.AltArtemov.Type.Properties

import Try1.S4
import Try1.S4.Context
import Try1.S4.Context.Core
import Try1.S4.Context.Notation
import Try1.S4.Derivation
import Try1.S4.Derivation.Core
import Try1.S4.Derivation.Notation
import Try1.S4.Type

import Try1.Experiments.Prelude

import Try1.Experiments.FishAndChips -- TODO: unfinished
import Try1.Experiments.Examples.FishAndChips

import Try1.Experiments.Shallow
import Try1.Experiments.Examples.Shallow

import Try1.Experiments.Typing

import Try1.Experiments.Interpretation -- TODO: unfinished


--------------------------------------------------------------------------------

-- TODO: separate

import Try2.Everything


--------------------------------------------------------------------------------
