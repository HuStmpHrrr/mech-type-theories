{-# OPTIONS --without-K --safe #-}

module NonCumulative.Statics.Ascribed.Properties.Contexts where

open import Data.Nat.Properties

open import Lib
open import NonCumulative.Statics.Ascribed.Full
open import NonCumulative.Statics.Ascribed.Misc

≈⇒len≡ : ⊢ Γ ≈ Δ →
         -------------
         len Γ ≡ len Δ
≈⇒len≡ []-≈                 = refl
≈⇒len≡ (∷-cong Γ≈Δ _ _ _ _) = cong suc (≈⇒len≡ Γ≈Δ)

∈⇒ty-wf : ∀ {x i} →
          ⊢ Γ →
          x ∶[ i ] T ∈! Γ →
          ------------
          Γ ⊢ T ∶[ 1 + i ] Se i
∈⇒ty-wf ⊢TΓ@(⊢∷ ⊢Γ ⊢T) here        = conv (t[σ] ⊢T (s-wk ⊢TΓ)) (Se-[] _ (s-wk ⊢TΓ))
∈⇒ty-wf ⊢TΓ@(⊢∷ ⊢Γ ⊢T) (there T∈Γ) = conv (t[σ] (∈⇒ty-wf ⊢Γ T∈Γ) (s-wk ⊢TΓ)) (Se-[] _ (s-wk ⊢TΓ))

presup-⊢≈ : ⊢ Γ ≈ Δ →
            ----------
            ⊢ Γ × ⊢ Δ
presup-⊢≈ []-≈ = ⊢[] , ⊢[]
presup-⊢≈ (∷-cong Γ≈Δ ⊢T ⊢T′ _ _)
  with presup-⊢≈ Γ≈Δ
...  | ⊢Γ , ⊢Δ = ⊢∷ ⊢Γ ⊢T , ⊢∷ ⊢Δ ⊢T′

∈⇒ty≈ : ∀ {x i} →
        ⊢ Γ →
        ⊢ Γ ≈ Δ →
        x ∶[ i ] T ∈! Γ →
        ---------------------------------
        ∃₂ λ T′ (⊢Δ : ⊢ Δ) → (x ∶[ i ] T′ ∈! Δ) × Γ ⊢ T ≈ T′ ∶[ suc i ] Se i × Δ ⊢ T ≈ T′ ∶[ suc i ] Se i
∈⇒ty≈ ⊢TΓ@(⊢∷ ⊢Γ ⊢T) (∷-cong Γ≈Δ _ ⊢T′ T≈ T≈′) here = -, ⊢∷ ⊢Δ ⊢T′ , here , []-cong-Se′ T≈ (s-wk ⊢TΓ) , []-cong-Se′ T≈′ (s-wk (⊢∷ ⊢Δ ⊢T′))
  where ⊢Δ = proj₂ (presup-⊢≈ Γ≈Δ)
∈⇒ty≈ ⊢TΓ@(⊢∷ ⊢Γ ⊢T) (∷-cong Γ≈Δ _ ⊢T′ T≈ T≈′) (there T∈Γ)
  with ∈⇒ty≈ ⊢Γ Γ≈Δ T∈Γ
...  | T″ , ⊢Δ , T″∈Δ , ≈T″ , ≈T″₁ = -, ⊢∷ ⊢Δ ⊢T′ , there T″∈Δ , []-cong-Se′ ≈T″ (s-wk ⊢TΓ) , []-cong-Se′ ≈T″₁ (s-wk (⊢∷ ⊢Δ ⊢T′))

⊢≈-sym : ⊢ Γ ≈ Δ → ⊢ Δ ≈ Γ
⊢≈-sym []-≈                           = []-≈
⊢≈-sym (∷-cong Γ≈Δ ⊢T ⊢T′ T≈T′ T≈T′₁) = ∷-cong (⊢≈-sym Γ≈Δ) ⊢T′ ⊢T (≈-sym T≈T′₁) (≈-sym T≈T′)
