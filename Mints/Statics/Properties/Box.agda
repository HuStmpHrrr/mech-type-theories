{-# OPTIONS --without-K --safe #-}

module Apini.Statics.Properties.Box where

open import Lib

open import Apini.Statics.Full
open import Apini.Statics.Refl

inv-□-wf : Γ ⊢ □ T ∶ T′ →
           ----------------
           [] ∷⁺ Γ ⊢ T
inv-□-wf (□-wf ⊢T)    = _ , ⊢T
inv-□-wf (cumu ⊢□T)   = inv-□-wf ⊢□T
inv-□-wf (conv ⊢□T _) = inv-□-wf ⊢□T
