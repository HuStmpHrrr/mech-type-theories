{-# OPTIONS --without-K --safe #-}

module kMLTT.Statics.Refl where

open import Lib
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
≈-refl′ (N-wf i ⊢Γ)           = N-≈ i ⊢Γ
≈-refl′ (Se-wf i ⊢Γ)          = Se-≈ ⊢Γ
≈-refl′ (Π-wf ⊢S ⊢T)          = Π-cong ⊢S (≈-refl′ ⊢S) (≈-refl′ ⊢T)
≈-refl′ (□-wf ⊢T)             = □-cong (≈-refl′ ⊢T)
≈-refl′ (vlookup ⊢Γ T∈Γ)      = v-≈ ⊢Γ T∈Γ
≈-refl′ (ze-I ⊢Γ)             = ze-≈ ⊢Γ
≈-refl′ (su-I ⊢t)             = su-cong (≈-refl′ ⊢t)
≈-refl′ (N-E ⊢T ⊢s ⊢r ⊢t)     = rec-cong ⊢T (≈-refl′ ⊢T) (≈-refl′ ⊢s) (≈-refl′ ⊢r) (≈-refl′ ⊢t)
≈-refl′ (Λ-I ⊢S ⊢t)           = Λ-cong ⊢S (≈-refl′ ⊢t)
≈-refl′ (Λ-E ⊢S ⊢T ⊢r ⊢s)     = $-cong ⊢S ⊢T (≈-refl′ ⊢r) (≈-refl′ ⊢s)
≈-refl′ (□-I ⊢t)              = box-cong (≈-refl′ ⊢t)
≈-refl′ (□-E Ψs ⊢T ⊢t ⊢++ eq) = unbox-cong Ψs ⊢T (≈-refl′ ⊢t) ⊢++ eq
≈-refl′ (t[σ] ⊢t ⊢σ)          = []-cong (≈-refl′ ⊢t) (s-≈-refl ⊢σ)
≈-refl′ (cumu ⊢t)             = ≈-cumu (≈-refl′ ⊢t)
≈-refl′ (conv ⊢t S≈T)         = ≈-conv (≈-refl′ ⊢t) S≈T

s-≈-refl′ : Γ ⊢s σ ∶ Δ →
            --------------
            Γ ⊢s σ ≈ σ ∶ Δ
s-≈-refl′ (s-I ⊢Γ)            = I-≈ ⊢Γ
s-≈-refl′ (s-wk ⊢TΓ)          = wk-≈ ⊢TΓ
s-≈-refl′ (s-∘ ⊢σ ⊢τ)         = ∘-cong (s-≈-refl′ ⊢σ) (s-≈-refl′ ⊢τ)
s-≈-refl′ (s-, ⊢σ ⊢T ⊢t)      = ,-cong (s-≈-refl′ ⊢σ) ⊢T (≈-refl ⊢t)
s-≈-refl′ (s-； Ψs ⊢σ ⊢++ eq) = ；-cong Ψs (s-≈-refl′ ⊢σ) ⊢++ eq
s-≈-refl′ (s-conv ⊢σ Δ′≈Δ)    = s-≈-conv (s-≈-refl′ ⊢σ) Δ′≈Δ

≈-Ctx-refl : ⊢ Γ → ⊢ Γ ≈ Γ
≈-Ctx-refl ⊢[]        = []-≈
≈-Ctx-refl (⊢κ ⊢Γ)    = κ-cong (≈-Ctx-refl ⊢Γ)
≈-Ctx-refl (⊢∺ ⊢Γ ⊢T) = ∺-cong (≈-Ctx-refl ⊢Γ) ⊢T ⊢T (≈-refl ⊢T) (≈-refl ⊢T)

∺-cong′ : ∀ {i} → ⊢ Γ → Γ ⊢ T ∶ Se i → Γ ⊢ T′ ∶ Se i → Γ ⊢ T ≈ T′ ∶ Se i → ⊢ T ∺ Γ ≈ T′ ∺ Γ
∺-cong′ ⊢Γ ⊢T ⊢T′ T≈T′ = ∺-cong (≈-Ctx-refl ⊢Γ) ⊢T ⊢T′ T≈T′ T≈T′

；-≡-cong : ∀ {n m} Ψs → Γ ⊢s σ ∶ Δ → ⊢ Ψs ++⁺ Γ → len Ψs ≡ n → n ≡ m → Ψs ++⁺ Γ ⊢s σ ； n ≈ σ ； m ∶ [] ∷⁺ Δ
；-≡-cong Ψs ⊢σ ⊢ΨsΓ eq1 refl = s-≈-refl (s-； Ψs ⊢σ ⊢ΨsΓ eq1)
