{-# OPTIONS --without-K --safe #-}

-- Reflexivity provided well-formedness, a consequence of being PER
module NonCumulative.Statics.Unascribed.Anno.Refl where

open import Lib
open import NonCumulative.Statics.Unascribed.Anno

≈-refl : ∀ {i} →
         Γ ⊢ t ∶[ i ] T →
         --------------
         Γ ⊢ t ≈ t ∶[ i ] T
≈-refl ⊢t = ≈-trans (≈-sym ([I] ⊢t)) ([I] ⊢t)

s-≈-refl : Γ ⊢s σ ∶ Δ →
           --------------
           Γ ⊢s σ ≈ σ ∶ Δ
s-≈-refl ⊢σ = s-≈-trans (s-≈-sym (I-∘ ⊢σ)) (I-∘ ⊢σ)

-- -- Different proofs by congruences, which is a sensible check to ensure the typing and the congruence rules are aligned.
mutual
  ≈-refl′ : ∀ {i} →
            Γ ⊢ t ∶[ i ] T →
            --------------
            Γ ⊢ t ≈ t ∶[ i ] T
  ≈-refl′ (N-wf ⊢Γ)            = ≈-trans (≈-sym (N-[] (s-I ⊢Γ))) (N-[] (s-I ⊢Γ))
  ≈-refl′ (Se-wf i ⊢Γ)         = ≈-trans (≈-sym (Se-[] i (s-I ⊢Γ))) (Se-[] i (s-I ⊢Γ))
  ≈-refl′ (Π-wf ⊢S ⊢T eq)      = Π-cong ⊢S (≈-refl′ ⊢S) (≈-refl′ ⊢T) eq
  ≈-refl′ (vlookup ⊢Γ T∈Γ)     = v-≈ ⊢Γ T∈Γ
  ≈-refl′ (ze-I ⊢Γ)            = ze-≈ ⊢Γ
  ≈-refl′ (su-I ⊢t)            = su-cong (≈-refl′ ⊢t)
  ≈-refl′ (N-E ⊢T ⊢s ⊢r ⊢t)    = rec-cong ⊢T (≈-refl′ ⊢T) (≈-refl′ ⊢s) (≈-refl′ ⊢r) (≈-refl′ ⊢t)
  ≈-refl′ (Λ-I ⊢S ⊢t eq)       = Λ-cong ⊢S (≈-refl′ ⊢t) eq
  ≈-refl′ (Λ-E ⊢S ⊢T ⊢r ⊢s eq) = $-cong ⊢S ⊢T (≈-refl′ ⊢r) (≈-refl′ ⊢s) eq
  ≈-refl′ (t[σ] ⊢t ⊢σ)         = []-cong (≈-refl′ ⊢t) (s-≈-refl′ ⊢σ)
  ≈-refl′ (conv ⊢t S≈T)        = ≈-conv (≈-refl′ ⊢t) S≈T
  ≈-refl′ (Liftt-wf n ⊢T)      = Liftt-cong n (≈-refl′ ⊢T)
  ≈-refl′ (L-I n ⊢t)           = liftt-cong n (≈-refl′ ⊢t)
  ≈-refl′ (L-E n ⊢T ⊢t)        = unlift-cong n ⊢T (≈-refl′ ⊢t)

  s-≈-refl′ : Γ ⊢s σ ∶ Δ →
              --------------
              Γ ⊢s σ ≈ σ ∶ Δ
  s-≈-refl′ (s-I ⊢Γ)            = I-≈ ⊢Γ
  s-≈-refl′ (s-wk ⊢TΓ)          = wk-≈ ⊢TΓ
  s-≈-refl′ (s-∘ ⊢σ ⊢τ)         = ∘-cong (s-≈-refl′ ⊢σ) (s-≈-refl′ ⊢τ)
  s-≈-refl′ (s-, ⊢σ ⊢T ⊢t)      = ,-cong (s-≈-refl′ ⊢σ) ⊢T (≈-refl′ ⊢t)
  s-≈-refl′ (s-conv ⊢σ Δ′≈Δ)    = s-≈-conv (s-≈-refl′ ⊢σ) Δ′≈Δ

≈-Ctx-refl : ⊢ Γ → ⊢ Γ ≈ Γ
≈-Ctx-refl ⊢[]        = []-≈
≈-Ctx-refl (⊢∷ ⊢Γ ⊢T) = ∷-cong (≈-Ctx-refl ⊢Γ) ⊢T ⊢T (≈-refl ⊢T) (≈-refl ⊢T)

∷-cong′ : ∀ {i} → ⊢ Γ → Γ ⊢ T ∶[ 1 + i ] Se i → Γ ⊢ T′ ∶[ 1 + i ] Se i → Γ ⊢ T ≈ T′ ∶[ 1 + i ] Se i → ⊢ T ∷ Γ ≈ T′ ∷ Γ
∷-cong′ ⊢Γ ⊢T ⊢T′ T≈T′ = ∷-cong (≈-Ctx-refl ⊢Γ) ⊢T ⊢T′ T≈T′ T≈T′
