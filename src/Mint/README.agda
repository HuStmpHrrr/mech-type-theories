{-# OPTIONS --without-K #-}

-- This file guides through how one should read this project
module Mint.README where

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
import Mint.Statics

-- Properties of the syntactic judgments
import Mint.Statics.Properties

-------------------------------------------------
-- Definitions of Semantics and the NbE algorithm

-- Definitions of the untyped semantic domain which the syntax is evaluated to
import Mint.Semantics.Domain

-- Evaluation from syntactic terms to the domain model
import Mint.Semantics.Evaluation

-- Read from the domain model back to the syntax as normal/neutral terms
import Mint.Semantics.Readback

-- PER model for the semantics
import Mint.Semantics.PER

-- Realizability for the semantics
import Mint.Semantics.Realizability

------------------------------------
-- Completeness of the NbE algorithm

-- Definitions of semantic judgments for completeness
import Mint.Completeness.LogRel

-- Fundamental theorems of semantic judgments
import Mint.Completeness.Fundamental fext as Fundamental

-- Proof of the completeness theorem
import Mint.Completeness fext as Completeness

-- Consequences of completeness
import Mint.Completeness.Consequences fext as Consequence

---------------------------------
-- Soundness of the NbE algorithm

-- Definitions of the gluing models and semantic judgments for soundness
import Mint.Soundness.LogRel

-- Realizability for the gluing model
import Mint.Soundness.Realizability

-- Cumulativity for the gluing model
import Mint.Soundness.Cumulativity

-- Fundamental theorems of semantic judgments for soundness
import Mint.Soundness.Fundamental fext as Fundamental′

-- Proof of the soundness theorem
import Mint.Soundness fext as Soundness

---------------------------------
-- Consequences of soundness

import Mint.Consequences fext as Consequence′
