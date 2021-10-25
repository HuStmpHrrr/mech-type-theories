{-# OPTIONS --without-K --safe #-}

module kMLTT.Statics.Refl where

open import kMLTT.Statics.Full
open import kMLTT.Statics.Misc

≈-refl : Γ ⊢ t ∶ T →
         --------------
         Γ ⊢ t ≈ t ∶ T
≈-refl ⊢t = ≈-trans (≈-sym ([I] ⊢t)) ([I] ⊢t)

s-≈-refl : Γ ⊢s σ ∶ Δ →
           --------------
           Γ ⊢s σ ≈ σ ∶ Δ
s-≈-refl ⊢σ = s-≈-trans (s-≈-sym (I-∘ ⊢σ)) (I-∘ ⊢σ)

-- different proofs by congruences
-- this is a more sensible check
≈-refl′ : Γ ⊢ t ∶ T →
         --------------
         Γ ⊢ t ≈ t ∶ T
≈-refl′ (N-wf i ⊢Γ)        = N-≈ i ⊢Γ
≈-refl′ (Se-wf i ⊢Γ)       = Se-≈ ⊢Γ
≈-refl′ (Π-wf ⊢S ⊢T)       = Π-cong ⊢S (≈-refl′ ⊢S) (≈-refl′ ⊢T)
≈-refl′ (□-wf ⊢T)          = □-cong (≈-refl′ ⊢T)
≈-refl′ (vlookup ⊢Γ T∈Γ)   = v-≈ ⊢Γ T∈Γ
≈-refl′ (ze-I ⊢Γ)          = ze-≈ ⊢Γ
≈-refl′ (su-I ⊢t)          = su-cong (≈-refl′ ⊢t)
≈-refl′ (N-E ⊢T ⊢s ⊢r ⊢t)  = rec-cong (≈-refl′ ⊢T) (≈-refl′ ⊢s) (≈-refl′ ⊢r) (≈-refl′ ⊢t)
≈-refl′ (Λ-I ⊢S ⊢t)        = Λ-cong (≈-refl′ ⊢t)
≈-refl′ (Λ-E ⊢r ⊢s)        = $-cong (≈-refl′ ⊢r) (≈-refl′ ⊢s)
≈-refl′ (□-I ⊢t)           = box-cong (≈-refl′ ⊢t)
≈-refl′ (□-E Ψs ⊢t ⊢++ eq) = unbox-cong Ψs (≈-refl′ ⊢t) ⊢++ eq
≈-refl′ (t[σ] ⊢t ⊢σ)       = []-cong (≈-refl′ ⊢t) (s-≈-refl ⊢σ)
≈-refl′ (cumu ⊢t)          = ≈-cumu (≈-refl′ ⊢t)
≈-refl′ (conv ⊢t S≈T)      = ≈-conv (≈-refl′ ⊢t) S≈T

s-≈-refl′ : Γ ⊢s σ ∶ Δ →
            --------------
            Γ ⊢s σ ≈ σ ∶ Δ
s-≈-refl′ (s-I ⊢Γ) = I-≈ ⊢Γ
s-≈-refl′ (s-p ⊢σ) = p-cong (s-≈-refl′ ⊢σ)
s-≈-refl′ (s-∘ ⊢σ ⊢τ) = ∘-cong (s-≈-refl′ ⊢σ) (s-≈-refl′ ⊢τ)
s-≈-refl′ (s-, ⊢σ ⊢T ⊢t) = ,-cong (s-≈-refl′ ⊢σ) ⊢T (≈-refl ⊢t)
s-≈-refl′ (s-； Ψs ⊢σ ⊢++ eq) = ；-cong Ψs (s-≈-refl′ ⊢σ) ⊢++ eq
s-≈-refl′ (s-conv ⊢σ Δ′≈Δ) = s-conv (s-≈-refl′ ⊢σ) Δ′≈Δ
