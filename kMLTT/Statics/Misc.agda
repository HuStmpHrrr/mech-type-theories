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

N-≈ : ∀ i →
      ⊢ Γ →
      Γ ⊢ N ≈ N ∶ Se i
N-≈ i ⊢Γ = ≈-trans (≈-sym (N-[] i (s-I ⊢Γ))) (N-[] i (s-I ⊢Γ))

Se-≈ : ∀ {i} →
       ⊢ Γ →
       Γ ⊢ Se i ≈ Se i ∶ Se (1 + i)
Se-≈ {_} {i} ⊢Γ = ≈-trans (≈-sym (Se-[] i (s-I ⊢Γ))) (Se-[] i (s-I ⊢Γ))

-- Rename this lemma with more reasonable names
conv-Se : ∀ {i} → Δ ⊢ T ∶ Se i → Γ ⊢s σ ∶ Δ → Γ ⊢ T [ σ ] ∶ Se i
conv-Se ⊢T ⊢σ = conv (t[σ] ⊢T ⊢σ) (Se-[] _ ⊢σ)

≈-conv-Se : ∀ {i} → Δ ⊢ T ≈ T′ ∶ Se i → Γ ⊢s σ ∶ Δ → Γ ⊢s σ ≈ σ′ ∶ Δ → Γ ⊢ T [ σ ] ≈ T′ [ σ′ ] ∶ Se i
≈-conv-Se T≈T′ ⊢σ σ≈σ′ = ≈-conv ([]-cong T≈T′ σ≈σ′) (Se-[] _ ⊢σ)

≈-conv-Se′ : ∀ {i} → Δ ⊢ T ≈ T′ ∶ Se i → Γ ⊢s σ ∶ Δ → Γ ⊢ T [ σ ] ≈ T′ [ σ ] ∶ Se i
≈-conv-Se′ T≈T′ ⊢σ = ≈-conv-Se T≈T′ ⊢σ (s-≈-trans (s-≈-sym (I-∘ ⊢σ)) (I-∘ ⊢σ))

[∘]-Se : ∀ {i} → Δ ⊢ T ∶ Se i → Γ ⊢s σ ∶ Δ → Γ′ ⊢s τ ∶ Γ → Γ′ ⊢ T [ σ ] [ τ ] ≈ T [ σ ∘ τ ] ∶ Se i
[∘]-Se ⊢T ⊢σ ⊢τ = ≈-conv (≈-sym ([∘] ⊢τ ⊢σ ⊢T)) (Se-[] _ (s-∘ ⊢τ ⊢σ))

TΓ⊢s-wk∶Γ : ⊢ T ∺ Γ → T ∺ Γ ⊢s wk ∶ Γ
TΓ⊢s-wk∶Γ ⊢TΓ = s-p (s-I ⊢TΓ)

N[wk]≈N : ∀ i →
          ⊢ T ∺ Γ →
          T ∺ Γ ⊢ N [ wk ] ≈ N ∶ Se i
N[wk]≈N _ ⊢TΓ = N-[] _ (TΓ⊢s-wk∶Γ ⊢TΓ)

N[wk][wk]≈N : ∀ i →
          ⊢ S ∺ T ∺ Γ →
          S ∺ T ∺ Γ ⊢ N [ wk ] [ wk ] ≈ N ∶ Se i
N[wk][wk]≈N _ ⊢STΓ@(⊢∷ ⊢TΓ _) = ≈-trans (≈-conv-Se′ (N[wk]≈N _ ⊢TΓ) (TΓ⊢s-wk∶Γ ⊢STΓ)) (N[wk]≈N _ ⊢STΓ)

N[σ]≈N : ∀ {i} →
         Γ ⊢s σ ∶ Δ →
         Γ ⊢ N [ σ ] ≈ N ∶ Se i
N[σ]≈N ⊢σ = N-[] _ ⊢σ

⊢q : ∀ {i} → ⊢ Γ → Γ ⊢s σ ∶ Δ → Δ ⊢ T ∶ Se i → (T [ σ ]) ∺ Γ ⊢s q σ ∶ T ∺ Δ
⊢q ⊢Γ ⊢σ ⊢T = s-, (s-∘ (⊢wk ⊢TσΓ) ⊢σ)
                  ⊢T
                  (conv (vlookup ⊢TσΓ here) ([∘]-Se ⊢T ⊢σ (⊢wk ⊢TσΓ)))
  where ⊢TσΓ = ⊢∷ ⊢Γ (conv-Se ⊢T ⊢σ)