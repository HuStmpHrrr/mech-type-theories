{-# OPTIONS --without-K --safe #-}

module NonCumulative.Statics.Anno.Properties.Liftt where

open import Lib
open import NonCumulative.Statics.Anno


inv-Liftt-wf : ∀ {i n} →
               Γ ⊢ Liftt n T ∶[ suc i ] T′ →
               --------------------------
               ∃ λ j → i ≡ n + j × Γ ⊢ T ∶[ suc j ] Se j
inv-Liftt-wf (Liftt-wf n ⊢LT) = -, refl , ⊢LT
inv-Liftt-wf (conv ⊢LT _)     = inv-Liftt-wf ⊢LT
