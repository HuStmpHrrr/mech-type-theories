{-# OPTIONS --without-K --safe #-}

module kMLTT.Statics.Misc where

open import Lib
open import Data.Nat
import Data.Nat.Properties as ℕₚ

open import kMLTT.Statics.Full

lift-⊢-Se-step : ∀ {i} j →
                 Γ ⊢ T ∶ Se i →
                 Γ ⊢ T ∶ Se (j + i)
lift-⊢-Se-step zero ⊢T = ⊢T
lift-⊢-Se-step (suc j) ⊢T = cumu (lift-⊢-Se-step j ⊢T)

lift-⊢-Se : ∀ {i j} →
            Γ ⊢ T ∶ Se i →
            i ≤ j →
            Γ ⊢ T ∶ Se j
lift-⊢-Se ⊢T i≤j
  rewrite sym (trans (ℕₚ.+-comm (≤-diff i≤j) _) (≤-diff-+ i≤j)) = lift-⊢-Se-step _ ⊢T

lift-⊢-Se-max : ∀ {i j} → Γ ⊢ T ∶ Se i → Γ ⊢ T ∶ Se (i ⊔ j)
lift-⊢-Se-max ⊢T = lift-⊢-Se ⊢T (ℕₚ.m≤m⊔n _ _)

lift-⊢-Se-max′ : ∀ {i j} → Γ ⊢ T ∶ Se i → Γ ⊢ T ∶ Se (j ⊔ i)
lift-⊢-Se-max′ ⊢T = lift-⊢-Se ⊢T (ℕₚ.m≤n⊔m _ _)

lift-⊢≈-Se-step : ∀ {i} j →
                  Γ ⊢ T ≈ T′ ∶ Se i →
                  Γ ⊢ T ≈ T′ ∶ Se (j + i)
lift-⊢≈-Se-step zero T≈T′    = T≈T′
lift-⊢≈-Se-step (suc j) T≈T′ = ≈-cumu (lift-⊢≈-Se-step j T≈T′)

lift-⊢≈-Se : ∀ {i j} →
             Γ ⊢ T ≈ T′ ∶ Se i →
             i ≤ j →
             Γ ⊢ T ≈ T′ ∶ Se j
lift-⊢≈-Se T≈T′ i≤j
  rewrite sym (trans (ℕₚ.+-comm (≤-diff i≤j) _) (≤-diff-+ i≤j)) = lift-⊢≈-Se-step _ T≈T′

lift-⊢≈-Se-max : ∀ {i j} → Γ ⊢ T ≈ T′ ∶ Se i → Γ ⊢ T ≈ T′ ∶ Se (i ⊔ j)
lift-⊢≈-Se-max T≈T′ = lift-⊢≈-Se T≈T′ (ℕₚ.m≤m⊔n _ _)

lift-⊢≈-Se-max′ : ∀ {i j} → Γ ⊢ T ≈ T′ ∶ Se i → Γ ⊢ T ≈ T′ ∶ Se (j ⊔ i)
lift-⊢≈-Se-max′ T≈T′ = lift-⊢≈-Se T≈T′ (ℕₚ.m≤n⊔m _ _)
