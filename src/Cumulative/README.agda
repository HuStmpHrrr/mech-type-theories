{-# OPTIONS --without-K #-}

-- This file guides through how one should read this project
module Cumulative.README where

open import Level
open import Axiom.Extensionality.Propositional


-- We only rely on functional extensionality (fext). We use this axiom to prove the
--    equality of PER and gluing models for universes. This use is not strictly
--    necessary and only require functional extensionality at level 1:
--
--        Extensionality 0ℓ 1ℓ
--
-- In this mechanization, all concepts are defined without fext. For properties of
-- semantics that do not require fext, we place them in Properties.NoFunExt.
postulate
  fext : Extensionality 0ℓ (suc 0ℓ)


-- Syntax, typing rules and equivalence rules
import Cumulative.Statics

-- Properties of the syntactic judgments
import Cumulative.Statics.Properties

-------------------------------------------------
-- Definitions of Semantics and the NbE algorithm

-- Definitions of the untyped semantic domain which the syntax is evaluated to
import Cumulative.Semantics.Domain

-- Evaluation from syntactic terms to the domain model
import Cumulative.Semantics.Evaluation

-- Read from the domain model back to the syntax as normal/neutral terms
import Cumulative.Semantics.Readback

-- PER model for the semantics
import Cumulative.Semantics.PER

-- Realizability for the semantics
import Cumulative.Semantics.Realizability

------------------------------------
-- Completeness of the NbE algorithm

-- Definitions of semantic judgments for completeness
import Cumulative.Completeness.LogRel

-- Fundamental theorems of semantic judgments
import Cumulative.Completeness.Fundamental fext as Fundamental

-- Proof of the completeness theorem
import Cumulative.Completeness fext as Completeness

-- Consequences of completeness
import Cumulative.Completeness.Consequences fext as Consequence

---------------------------------
-- Soundness of the NbE algorithm

-- Definitions of the gluing models and semantic judgments for soundness
import Cumulative.Soundness.LogRel

-- Realizability for the gluing model
import Cumulative.Soundness.Realizability

-- Cumulativity for the gluing model
import Cumulative.Soundness.Cumulativity

-- Fundamental theorems of semantic judgments for soundness
import Cumulative.Soundness.Fundamental fext as Fundamental′

-- Proof of the soundness theorem
import Cumulative.Soundness fext as Soundness

---------------------------------
-- Consequences of soundness

import Cumulative.Consequences fext as Consequence′
