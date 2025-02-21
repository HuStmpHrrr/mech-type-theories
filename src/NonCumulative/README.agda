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
import NonCumulative.Ascribed.Statics.Full

-- Properties of the syntactic judgments
import NonCumulative.Ascribed.Statics.Properties

-------------------------------------------------
-- Definitions of Semantics and the NbE algorithm

-- Definitions of the untyped semantic domain which the syntax is evaluated to
import NonCumulative.Ascribed.Semantics.Domain

-- Evaluation from syntactic terms to the domain model
import NonCumulative.Ascribed.Semantics.Evaluation

-- Read from the domain model back to the syntax as normal/neutral terms
import NonCumulative.Ascribed.Semantics.Readback

-- PER model for the semantics
import NonCumulative.Ascribed.Semantics.PER

-- Realizability for the semantics
import NonCumulative.Ascribed.Semantics.Realizability

------------------------------------
-- Completeness of the NbE algorithm

-- Definitions of semantic judgments for completeness
import NonCumulative.Ascribed.Completeness.LogRel

-- Fundamental theorems of semantic judgments
import NonCumulative.Ascribed.Completeness.Fundamental fext as Fundamental

-- Proof of the completeness theorem
import NonCumulative.Ascribed.Completeness fext as Completeness

-- Consequences of completeness
import NonCumulative.Ascribed.Completeness.Consequences fext as Consequence

---------------------------------
-- Soundness of the NbE algorithm

-- Definitions of the gluing models and semantic judgments for soundness
import NonCumulative.Ascribed.Soundness.LogRel

-- Realizability for the gluing model
import NonCumulative.Ascribed.Soundness.Realizability

-- Fundamental theorems of semantic judgments for soundness
import NonCumulative.Ascribed.Soundness.Fundamental fext as Fundamental′

-- Proof of the soundness theorem
import NonCumulative.Ascribed.Soundness fext as Soundness

---------------------------------
-- Consequences of soundness

import NonCumulative.Ascribed.Consequences fext as Consequence′

---------------------------------
-- Properties of an unascribed set of rules

-- Unascribed system is complete to the ascribe one
import NonCumulative.Unascribed.Properties.Equivalence.Completeness as Completeness

-- Unascribed system is sound to the ascribe one
import NonCumulative.Unascribed.Properties.Equivalence.Soundness as USoundness

-- Transfer of some properties from the ascribed system to the unascribed one 
-- using soundness and completeness
import NonCumulative.Unascribed.Properties.Equivalence.Consequences fext as UConsequences

-- Unascribed NbE is also sound and complete wrt to the syntactic rules of the unascribed systems
import NonCumulative.Unascribed.Properties.NbE.Soundness fext as UNbESoundness
import NonCumulative.Unascribed.Properties.NbE.Completeness fext as UNbECompleteness