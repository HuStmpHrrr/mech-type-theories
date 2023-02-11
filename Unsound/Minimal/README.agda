{-# OPTIONS --without-K --safe #-}

module Minimal.README where

-- static semantics
import Minimal.Statics


-- nbe operations for βη equivalence
import Minimal.TypedSem
-- completeness for nbe
import Minimal.PER
-- soundness for nbe
import Minimal.Soundness
