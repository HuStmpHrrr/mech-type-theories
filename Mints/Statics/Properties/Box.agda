{-# OPTIONS --without-K --safe #-}

module Mints.Statics.Properties.Box where

open import Lib

open import Mints.Statics.Full
open import Mints.Statics.Refl

inv-□-wf : Γ ⊢ □ T ∶ T′ →
           ----------------
           [] ∷⁺ Γ ⊢ T
inv-□-wf (□-wf ⊢T)    = _ , ⊢T
inv-□-wf (cumu ⊢□T)   = inv-□-wf ⊢□T
inv-□-wf (conv ⊢□T _) = inv-□-wf ⊢□T
