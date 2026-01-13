{-# OPTIONS --without-K #-}

module STLCSubst.README where

open import Level
open import Axiom.Extensionality.Propositional

postulate
  fext : Extensionality 0ℓ 0ℓ

-- static semantics
import STLCSubst.Statics

-- nbe operations for βη equivalence
import STLCSubst.Semantics.Definitions

-- PER model for nbe
import STLCSubst.Semantics.PER

-- completeness for nbe
import STLCSubst.Semantics.Rules fext as Completeness

-- soundness for nbe
import STLCSubst.Soundness
