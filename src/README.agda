{-# OPTIONS --without-K #-}

module README where

-- Various normalization method for STLC
import STLC.README

-- NbE for System T using an untyped domain model
--   with a completeness and a soundness theorems
import T.README

-- NbE for minimal STLC, a reduced version of the previous one
--   with a completeness and a soundness theorems
import Minimal.README

-- NbE for λ□ using an untyped domain model and a presheaf model
--   with a completeness and a soundness theorems for the untyped domain model
import Unbox.README

-- NbE for layered modal type theory using a presheaf model
import Layered.README
-- NbE for layered modal type theory using a presheaf model
import CLayered.README

-- NbE for Martin-Löf type theory using an untyped domain model
--   with a completeness and a soundness theorems
import MLTT.README


-- NbE for Mint, a modal intuitionistic type theory, using an untyped domain model
--   with a completeness and a soundness theorems
import Mint.README
