module Everything where


--------------------------------------------------------------------------------

-- Some theorems of propositional logic and the λ-calculus, and some first-
-- and second-level realisations of theorems of the modal logic S4.
import Examples.AltArtemov

-- Some theorems of propositional logic and the modal logic S4.
import Examples.S4

-- Demonstration of forgetful projection from the reflective λ-calculus to
-- the modal logic S4.
import Examples.ForgetfulProjection

-- Demonstration of the isomorphism between propositional logic and the
-- λ-calculus, and between first- and second-level realisations of theorems
-- of the modal logic S4.
import Examples.Isomorphism

-- Some examples of reasoning with negation and principle of explosion.
import Examples.Negation

-- Descriptions of the reflective λ-calculus (λ∞) and reflective combinatory
-- logic (RCL).
import Notes.Artemov2004.AA
import Notes.Artemov2004.RCL

-- Descriptions of the logic of functional proofs (FLP) and RCL.
import Notes.Artemov2006.FLP
import Notes.Artemov2006.RCL


--------------------------------------------------------------------------------

import Data.Nat.Missing
import Data.Maybe.Missing

import AltArtemov
import AltArtemov.Context
import AltArtemov.Context.Core
import AltArtemov.Context.Notation
import AltArtemov.Context.Properties
import AltArtemov.Derivation
import AltArtemov.Derivation.Core
import AltArtemov.Derivation.Notation.Level1
import AltArtemov.Derivation.Notation.Level2
import AltArtemov.Derivation.Notation.Level3
import AltArtemov.Derivation.Notation.Level4
import AltArtemov.Derivation.Properties
import AltArtemov.Term
import AltArtemov.Term.Core
import AltArtemov.Term.Inversions
import AltArtemov.Term.Notation.Level1
import AltArtemov.Term.Notation.Level2
import AltArtemov.Term.Notation.Level3
import AltArtemov.Term.Notation.Level4
import AltArtemov.Term.Properties
import AltArtemov.TermVector
import AltArtemov.TermVector.Core
import AltArtemov.TermVector.Notation
import AltArtemov.Type
import AltArtemov.Type.Core
import AltArtemov.Type.Inversions
import AltArtemov.Type.Properties

import S4
import S4.Context
import S4.Context.Core
import S4.Context.Notation
import S4.Derivation
import S4.Derivation.Core
import S4.Derivation.Notation
import S4.Type

import Experiments.Prelude

import Experiments.FishAndChips -- TODO: unfinished
import Experiments.Examples.FishAndChips

import Experiments.Shallow
import Experiments.Examples.Shallow

import Experiments.Typing

import Experiments.Interpretation -- TODO: unfinished


--------------------------------------------------------------------------------
