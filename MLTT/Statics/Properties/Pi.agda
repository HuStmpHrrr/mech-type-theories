{-# OPTIONS --without-K --safe #-}

module MLTT.Statics.Properties.Pi where

open import Lib

open import MLTT.Statics.Full

inv-Π-wf : Γ ⊢ Π S T ∶ T′ →
           ----------------
           S ∷ Γ ⊢ T
inv-Π-wf (Π-wf ⊢S ⊢T) = _ , ⊢T
inv-Π-wf (cumu ⊢Π)    = inv-Π-wf ⊢Π
inv-Π-wf (conv ⊢Π _)  = inv-Π-wf ⊢Π

inv-Π-wf′ : Γ ⊢ Π S T ∶ T′ →
            ----------------
            Γ ⊢ S
inv-Π-wf′ (Π-wf ⊢S ⊢T) = _ , ⊢S
inv-Π-wf′ (cumu ⊢Π)    = inv-Π-wf′ ⊢Π
inv-Π-wf′ (conv ⊢Π _)  = inv-Π-wf′ ⊢Π
