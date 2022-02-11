{-# OPTIONS --without-K #-}

module kMLTT.README where

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
postulate
  fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′


-- Syntax, typing rules and equivalence rules
open import kMLTT.Statics

-- Definitions of the untyped semantic domain which the syntax is evaluated to
open import kMLTT.Semantics.Domain

open import kMLTT.Completeness fext

open import kMLTT.Soundness fext

open import kMLTT.Consequences fext
