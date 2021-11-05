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

-- Rename these lemmas with more reasonable names
conv-N : Δ ⊢ t ∶ N → Γ ⊢s σ ∶ Δ → Γ ⊢ t [ σ ] ∶ N
conv-N ⊢t ⊢σ = conv (t[σ] ⊢t ⊢σ) (N-[] 0 ⊢σ)

conv-Se : ∀ {i} → Δ ⊢ T ∶ Se i → Γ ⊢s σ ∶ Δ → Γ ⊢ T [ σ ] ∶ Se i
conv-Se ⊢T ⊢σ = conv (t[σ] ⊢T ⊢σ) (Se-[] _ ⊢σ)

≈-conv-Se : ∀ {i} → Δ ⊢ T ≈ T′ ∶ Se i → Γ ⊢s σ ∶ Δ → Γ ⊢s σ ≈ σ′ ∶ Δ → Γ ⊢ T [ σ ] ≈ T′ [ σ′ ] ∶ Se i
≈-conv-Se T≈T′ ⊢σ σ≈σ′ = ≈-conv ([]-cong T≈T′ σ≈σ′) (Se-[] _ ⊢σ)

≈-conv-Se′ : ∀ {i} → Δ ⊢ T ≈ T′ ∶ Se i → Γ ⊢s σ ∶ Δ → Γ ⊢ T [ σ ] ≈ T′ [ σ ] ∶ Se i
≈-conv-Se′ T≈T′ ⊢σ = ≈-conv-Se T≈T′ ⊢σ (s-≈-trans (s-≈-sym (I-∘ ⊢σ)) (I-∘ ⊢σ))

[∘]-Se : ∀ {i} → Δ ⊢ T ∶ Se i → Γ ⊢s σ ∶ Δ → Γ′ ⊢s τ ∶ Γ → Γ′ ⊢ T [ σ ] [ τ ] ≈ T [ σ ∘ τ ] ∶ Se i
[∘]-Se ⊢T ⊢σ ⊢τ = ≈-conv (≈-sym ([∘] ⊢τ ⊢σ ⊢T)) (Se-[] _ (s-∘ ⊢τ ⊢σ))

N[wk]≈N : ∀ i →
          ⊢ T ∺ Γ →
          T ∺ Γ ⊢ N [ wk ] ≈ N ∶ Se i
N[wk]≈N _ ⊢TΓ = N-[] _ (⊢wk ⊢TΓ)

N-[][] : ∀ i →
         Γ′ ⊢s σ ∶ Γ″ →
         Γ ⊢s τ ∶ Γ′ →
         Γ ⊢ N [ σ ] [ τ ] ≈ N ∶ Se i
N-[][] _ ⊢σ ⊢τ = ≈-trans (≈-conv-Se′ (N-[] _ ⊢σ) ⊢τ) (N-[] _ ⊢τ)

N[wk][wk]≈N : ∀ i →
              ⊢ S ∺ T ∺ Γ →
              S ∺ T ∺ Γ ⊢ N [ wk ] [ wk ] ≈ N ∶ Se i
N[wk][wk]≈N _ ⊢STΓ@(⊢∷ ⊢TΓ _) = N-[][] _ (⊢wk ⊢TΓ) (⊢wk ⊢STΓ)

N[σ]≈N[τ] : ∀ i →
            Γ ⊢s σ ∶ Δ →
            Γ ⊢s τ ∶ Δ′ →
            Γ ⊢ N [ σ ] ≈ N [ τ ] ∶ Se i
N[σ]≈N[τ] _ ⊢σ ⊢τ = ≈-trans (N-[] _ ⊢σ) (≈-sym (N-[] _ ⊢τ))

⊢q : ∀ {i} → ⊢ Γ → Γ ⊢s σ ∶ Δ → Δ ⊢ T ∶ Se i → (T [ σ ]) ∺ Γ ⊢s q σ ∶ T ∺ Δ
⊢q ⊢Γ ⊢σ ⊢T = s-, (s-∘ (⊢wk ⊢TσΓ) ⊢σ)
                  ⊢T
                  (conv (vlookup ⊢TσΓ here) ([∘]-Se ⊢T ⊢σ (⊢wk ⊢TσΓ)))
  where ⊢TσΓ = ⊢∷ ⊢Γ (conv-Se ⊢T ⊢σ)

⊢q-N : ⊢ Γ → ⊢ Δ → Γ ⊢s σ ∶ Δ → N ∺ Γ ⊢s q σ ∶ N ∺ Δ
⊢q-N ⊢Γ ⊢Δ ⊢σ = s-, (s-∘ (⊢wk ⊢NΓ) ⊢σ)
                (N-wf 0 ⊢Δ)
                (conv (vlookup ⊢NΓ here) (≈-trans (N[wk]≈N 0 ⊢NΓ) (≈-sym (N-[] 0 (s-∘ (⊢wk ⊢NΓ) ⊢σ)))))
  where ⊢NΓ = ⊢∷ ⊢Γ (N-wf 0 ⊢Γ)

⊢I,t : ∀ {i} → ⊢ Γ → Γ ⊢ T ∶ Se i → Γ ⊢ t ∶ T → Γ ⊢s I , t ∶ T ∺ Γ
⊢I,t ⊢Γ ⊢T ⊢t = s-, (s-I ⊢Γ) ⊢T (conv ⊢t (≈-sym ([I] ⊢T)))
