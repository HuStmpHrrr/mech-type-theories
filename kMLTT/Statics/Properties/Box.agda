{-# OPTIONS --without-K --safe #-}

module kMLTT.Statics.Properties.Box where

open import Lib

open import kMLTT.Statics.Full
open import kMLTT.Statics.Refl

inv-□-wf : Γ ⊢ □ T ∶ T′ →
           ----------------
           [] ∷⁺ Γ ⊢ T
inv-□-wf (□-wf ⊢T)    = _ , ⊢T
inv-□-wf (cumu ⊢□T)   = inv-□-wf ⊢□T
inv-□-wf (conv ⊢□T _) = inv-□-wf ⊢□T
