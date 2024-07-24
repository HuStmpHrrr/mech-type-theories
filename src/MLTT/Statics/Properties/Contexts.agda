{-# OPTIONS --without-K --safe #-}

module MLTT.Statics.Properties.Contexts where

open import Data.Nat.Properties

open import Lib
open import MLTT.Statics.Full
open import MLTT.Statics.Refl
open import MLTT.Statics.Misc

≈⇒len≡ : ⊢ Γ ≈ Δ →
         -------------
         len Γ ≡ len Δ
≈⇒len≡ []-≈                 = refl
≈⇒len≡ (∷-cong Γ≈Δ _ _ _ _) = cong suc (≈⇒len≡ Γ≈Δ)

∈!⇒ty-wf : ∀ {x} →
           ⊢ Γ →
           x ∶ T ∈! Γ →
           ------------
           Γ ⊢ T
∈!⇒ty-wf ⊢TΓ@(⊢∷ ⊢Γ ⊢T) here = _ , t[σ]-Se ⊢T (s-wk ⊢TΓ)
∈!⇒ty-wf ⊢TΓ@(⊢∷ ⊢Γ ⊢S) (there T∈Γ)
  with ∈!⇒ty-wf ⊢Γ T∈Γ
...  | i , ⊢T                = _ , t[σ]-Se ⊢T (s-wk ⊢TΓ)

presup-⊢≈ : ⊢ Γ ≈ Δ →
            ----------
            ⊢ Γ × ⊢ Δ
presup-⊢≈ []-≈ = ⊢[] , ⊢[]
presup-⊢≈ (∷-cong Γ≈Δ ⊢T ⊢T′ _ _)
  with presup-⊢≈ Γ≈Δ
...  | ⊢Γ , ⊢Δ = ⊢∷ ⊢Γ ⊢T , ⊢∷ ⊢Δ ⊢T′

∈!⇒ty≈ : ∀ {x} →
         ⊢ Γ ≈ Δ →
         x ∶ T ∈! Γ →
         ---------------------------------
         ∃ λ T′ → (x ∶ T′ ∈! Δ) × Γ ⊢ T ≈ T′ × Δ ⊢ T ≈ T′
∈!⇒ty≈ (∷-cong Γ≈Δ ⊢T ⊢T′ T≈T′ T≈T′₁) here
  with presup-⊢≈ Γ≈Δ
...  | ⊢Γ , ⊢Δ                            = -, here , (-, []-cong-Se′ T≈T′ (s-wk (⊢∷ ⊢Γ ⊢T))) , -, []-cong-Se′ T≈T′₁ (s-wk (⊢∷ ⊢Δ ⊢T′))
∈!⇒ty≈ (∷-cong Γ≈Δ ⊢T ⊢T′ _ _) (there T∈Γ)
  with presup-⊢≈ Γ≈Δ | ∈!⇒ty≈ Γ≈Δ T∈Γ
...  | ⊢Γ , ⊢Δ
     | T′ , T′∈Δ , (_ , T≈T′) , _ , T≈T′₁ = -, there T′∈Δ , (-, []-cong-Se′ T≈T′ (s-wk (⊢∷ ⊢Γ ⊢T))) , (-, []-cong-Se′ T≈T′₁ (s-wk (⊢∷ ⊢Δ ⊢T′)))

⊢≈-sym : ⊢ Γ ≈ Δ → ⊢ Δ ≈ Γ
⊢≈-sym []-≈                           = []-≈
⊢≈-sym (∷-cong Γ≈Δ ⊢T ⊢T′ T≈T′ T≈T′₁) = ∷-cong (⊢≈-sym Γ≈Δ) ⊢T′ ⊢T (≈-sym T≈T′₁) (≈-sym T≈T′)
