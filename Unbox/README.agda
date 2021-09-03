{-# OPTIONS --without-K #-}

module Unbox.README where

open import Level using (0ℓ)
open import Axiom.Extensionality.Propositional

-- we have to postulate functional extensionality to prove properties about evaluation environments.
postulate
  fext : Extensionality 0ℓ 0ℓ

-- static semantics
open import Unbox.Statics

-- nbe based on a presheaf model
open import Unbox.Presheaf

-- nbe based on an untyped domain
open import Unbox.Semantics
-- completeness for nbe
open import Unbox.PER fext
-- soundness for nbe
open import Unbox.Soundness fext
