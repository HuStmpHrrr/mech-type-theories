{-# OPTIONS --without-K --safe #-}

module NonCumulative.Statics.Ascribed.Properties.Liftt where

open import Lib
open import NonCumulative.Statics.Ascribed.Full


inv-Liftt-wf : ∀ {i j n} →
               Γ ⊢ Liftt n (T ↙ j) ∶[ suc i ] T′ →
               --------------------------
               i ≡ n + j × Γ ⊢ T ∶[ suc j ] Se j
inv-Liftt-wf (Liftt-wf n ⊢LT) = refl , ⊢LT
inv-Liftt-wf (conv ⊢LT _)     = inv-Liftt-wf ⊢LT
