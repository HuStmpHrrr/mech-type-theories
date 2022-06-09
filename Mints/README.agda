{-# OPTIONS --without-K #-}

-- This file guides through how one should read this project
module Mints.README where

open import Axiom.Extensionality.Propositional


-- We only rely on functional extensionality (fext). We use this axiom in
-- two places:
--
-- 1. Fext is necessary to establish the equality between evaluation environments in
--    the domain model. Interestingly, this necessity is introduced because of □
--    modality, i.e. if we formalize ordinary Martin-Löf type theory (MLTT), we would
--    not even need fext. Instead of a just keeping tracking of values as in MLTT, we
--    also need to keep track of modal offsets in the evaluation environments, thus
--    requiring fext.
--
--    Use of fext in this case only require functional extensionality at level 0:
--
--        Extensionality 0ℓ 0ℓ
--
-- 2. Since we are postulating functional extensionality, we might as well abuse it
--    a little bit and use it in proving the equality of PER and gluing models for
--    universes. This use is not strictly necessary and only require functional
--    extensionality at level 1:
--
--        Extensionality 1ℓ 1ℓ
--
-- In this mechanization, all concepts are defined without fext. For properties of
-- semantics that do not require fext, we place them in Properties.NoFunExt.
postulate
  fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′


-- Syntax, typing rules and equivalence rules
import Mints.Statics

-- Properties of the syntactic judgments
import Mints.Statics.Properties

-------------------------------------------------
-- Definitions of Semantics and the NbE algorithm

-- Definitions of the untyped semantic domain which the syntax is evaluated to
import Mints.Semantics.Domain

-- Evaluation from syntactic terms to the domain model
import Mints.Semantics.Evaluation

-- Read from the domain model back to the syntax as normal/neutral terms
import Mints.Semantics.Readback

-- PER model for the semantics
import Mints.Semantics.PER

-- Realizability for the semantics
import Mints.Semantics.Realizability

------------------------------------
-- Completeness of the NbE algorithm

-- Definitions of semantic judgments for completeness
import Mints.Completeness.LogRel

-- Fundamental theorems of semantic judgments
import Mints.Completeness.Fundamental fext as Fundamental

-- Proof of the completeness theorem
import Mints.Completeness fext as Completeness

-- Consequences of completeness
import Mints.Completeness.Consequences fext as Consequence

---------------------------------
-- Soundness of the NbE algorithm

-- Definitions of the gluing models and semantic judgments for soundness
import Mints.Soundness.LogRel

-- Realizability for the gluing model
import Mints.Soundness.Realizability

-- Cumulativity for the gluing model
import Mints.Soundness.Cumulativity

-- Fundamental theorems of semantic judgments for soundness
import Mints.Soundness.Fundamental fext as Fundamental′

-- Proof of the soundness theorem
import Mints.Soundness fext as Soundness

---------------------------------
-- Consequences of soundness

import Mints.Consequences fext as Consequence′
