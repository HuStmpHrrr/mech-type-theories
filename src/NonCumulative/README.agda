{-# OPTIONS --without-K #-}

-- This file guides through how one should read this project
module NonCumulative.README where

open import Level
open import Axiom.Extensionality.Propositional


-- We only rely on functional extensionality (fext). We use this axiom to prove the
--    equality of PER and gluing models for universes. This use is not strictly
--    necessary and only require functional extensionality at level 1 and 2:
--
--        Extensionality 0ℓ 1ℓ
--        Extensionality 1ℓ 2ℓ
-- 
-- However, for brevity, we still postulate fext with arbitrary levels.
-- 
-- In this mechanization, all concepts are defined without fext. For properties of
-- semantics that do not require fext, we place them in Properties.NoFunExt.
postulate
  fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂


-- Syntax, typing rules and equivalence rules
import NonCumulative.Statics.Ascribed.Full

-- Properties of the syntactic judgments
import NonCumulative.Statics.Ascribed.Properties

-------------------------------------------------
-- Definitions of Semantics and the NbE algorithm

-- Definitions of the untyped semantic domain which the syntax is evaluated to
import NonCumulative.Semantics.Domain

-- Evaluation from syntactic terms to the domain model
import NonCumulative.Semantics.Evaluation

-- Read from the domain model back to the syntax as normal/neutral terms
import NonCumulative.Semantics.Readback

-- PER model for the semantics
import NonCumulative.Semantics.PER

-- Realizability for the semantics
import NonCumulative.Semantics.Realizability

------------------------------------
-- Completeness of the NbE algorithm

-- Definitions of semantic judgments for completeness
import NonCumulative.Completeness.LogRel

-- Fundamental theorems of semantic judgments
import NonCumulative.Completeness.Fundamental fext as Fundamental

-- Proof of the completeness theorem
import NonCumulative.Completeness fext as Completeness

-- Consequences of completeness
import NonCumulative.Completeness.Consequences fext as Consequence

---------------------------------
-- Soundness of the NbE algorithm

-- Definitions of the gluing models and semantic judgments for soundness
import NonCumulative.Soundness.LogRel

-- Realizability for the gluing model
import NonCumulative.Soundness.Realizability

-- Fundamental theorems of semantic judgments for soundness
import NonCumulative.Soundness.Fundamental fext as Fundamental′

-- Proof of the soundness theorem
import NonCumulative.Soundness fext as Soundness

---------------------------------
-- Consequences of soundness

import NonCumulative.Consequences fext as Consequence′

---------------------------------
-- Properties of an unascribed set of rules

-- Unascribed system is complete to the ascribe one
import NonCumulative.Statics.Equivalence.Completeness as UCompleteness

-- Unascribed system is sound to the ascribe one
import NonCumulative.Statics.Equivalence.Soundness as USoundness

-- Transfer of some properties from the ascribed system to the unascribed one 
-- using soundness and completeness
import NonCumulative.Statics.Unascribed.Properties as UProperties