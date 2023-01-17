{-# OPTIONS --without-K --safe #-}

module NonCumulative.Statics.Ascribed.Simpl where

open import Lib

open import NonCumulative.Statics.Ascribed.Full
open import NonCumulative.Statics.Ascribed.Presup
open import NonCumulative.Statics.Ascribed.CtxEquiv


∷-cong-simp : ∀ {i} →
              ⊢ Γ ≈ Δ →
              Γ ⊢ T ≈ T′ ∶[ 1 + i ] Se i →
              ----------------
              ⊢ (T ↙ i) ∷ Γ ≈ (T′ ↙ i) ∷ Δ
∷-cong-simp Γ≈Δ T≈T′
  with presup-≈ T≈T′
...  | _ , ⊢T , ⊢T′ , _ = ∷-cong Γ≈Δ ⊢T (ctxeq-tm Γ≈Δ ⊢T′) T≈T′ (ctxeq-≈ Γ≈Δ T≈T′)
