{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Soundness.Universe (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Data.Nat.Properties as ℕₚ

open import kMLTT.Statics.Properties
open import kMLTT.Semantics.Readback
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Soundness.Cumulativity fext
open import kMLTT.Soundness.LogRel
open import kMLTT.Soundness.Realizability fext
open import kMLTT.Soundness.Properties.LogRel fext
open import kMLTT.Soundness.Properties.Substitutions fext

Se-wf′ : ∀ {i} →
         ⊢ Γ →
         ------------------
         Γ ⊩ Se i ∶ Se (suc i)
Se-wf′ {_} {i} ⊢Γ = ⊢Γ , suc (suc i) , helper
  where
    helper : ∀ {Δ σ ρ} →
             Δ ⊢s σ ∶ ⊢Γ ® ρ →
             GluExp _ Δ (Se _) (Se _) σ ρ
    helper σ∼ρ
      with s®⇒⊢s ⊢Γ σ∼ρ
    ...  | ⊢σ   = record
                  { ↘⟦T⟧ = ⟦Se⟧ _
                  ; ↘⟦t⟧ = ⟦Se⟧ _
                  ; T∈𝕌 = U′ ≤-refl
                  ; t∼⟦t⟧ = record
                            { t∶T = t[σ] (Se-wf _ ⊢Γ) ⊢σ
                            ; T≈ = Se-[] _ ⊢σ
                            ; A∈𝕌 = U′ ≤-refl
                            ; rel = Se-[] _ ⊢σ
                            }
                  }

cumu′ : ∀ {i} →
        Γ ⊩ T ∶ Se i →
        ------------------
        Γ ⊩ T ∶ Se (1 + i)
cumu′ {_} {T} (⊢Γ , n , Trel) = ⊢Γ , _ , helper
  where
    helper : ∀ {Δ σ ρ} →
             Δ ⊢s σ ∶ ⊢Γ ® ρ →
             GluExp (suc n) Δ T (Se _) σ ρ
    helper {Δ} {σ} σ∼ρ
      with s®⇒⊢s ⊢Γ σ∼ρ | Trel σ∼ρ
    ...  | ⊢σ
         | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = U i<n _ ; t∼⟦t⟧ = t∼⟦t⟧ } = record
                                                                    { ↘⟦T⟧ = ⟦Se⟧ _
                                                                    ; ↘⟦t⟧ = ↘⟦t⟧
                                                                    ; T∈𝕌 = U′ (s≤s i<n)
                                                                    ; t∼⟦t⟧ = t∼⟦t⟧′
                                                                    }
      where
        open GluU t∼⟦t⟧

        t∼⟦t⟧′ : Δ ⊢ T [ σ ] ∶ Se _ [ σ ] ®[ _ ] _ ∈El U′ (s≤s i<n)
        t∼⟦t⟧′ rewrite Glu-wellfounded-≡ (s≤s i<n) = record
                             { t∶T = conv (cumu (conv t∶T (Se-[] _ ⊢σ))) (≈-sym (Se-[] _ ⊢σ))
                             ; T≈ = lift-⊢≈-Se (Se-[] _ ⊢σ) (s≤s i<n)
                             ; A∈𝕌 = 𝕌-cumu-step _ A∈𝕌
                             ; rel = ®-cumu-step A∈𝕌 (subst (λ f → f _ _ _) (Glu-wellfounded-≡ i<n) rel)
                             }
