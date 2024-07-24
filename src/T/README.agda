{-# OPTIONS --without-K --safe #-}

module T.README where

-- static semantics
import T.Statics

-- nbe operations for β equivalence
import T.Semantics
-- (partial) completeness for nbe
import T.Strict


-- nbe operations for βη equivalence
import T.TypedSem
-- completeness for nbe
import T.PER
-- soundness for nbe
import T.Soundness
