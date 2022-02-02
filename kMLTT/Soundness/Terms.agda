{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Soundness.Terms (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Data.Nat.Properties as ℕₚ

open import kMLTT.Statics.Properties
open import kMLTT.Semantics.Readback
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Completeness.Fundamental fext
open import kMLTT.Soundness.Cumulativity fext
open import kMLTT.Soundness.LogRel
open import kMLTT.Soundness.Realizability fext
open import kMLTT.Soundness.Properties.LogRel fext
open import kMLTT.Soundness.Properties.Substitutions fext

conv′ : ∀ {i} →
        Γ ⊩ t ∶ S →
        Γ ⊢ S ≈ T ∶ Se i →
        ------------------
        Γ ⊩ t ∶ T
conv′ {_} {t} {_} {T} (⊢Γ , n , trel) S≈T
  with fundamental-t≈t′ S≈T
...  | ⊨Γ₁ , n₁ , Trel₁       = ⊢Γ , _ , helper
  where
    helper : ∀ {Δ σ ρ} →
             Δ ⊢s σ ∶ ⊢Γ ® ρ →
             GluExp _ Δ t T σ ρ
    helper σ∼ρ
      with fundamental-⊢Γ ⊢Γ | s®⇒⊢s ⊢Γ σ∼ρ | s®⇒⟦⟧ρ ⊢Γ σ∼ρ
    ...  | ⊨Γ | ⊢σ | ρ∈
        with trel σ∼ρ | Trel₁ (⊨-irrel ⊨Γ ⊨Γ₁ ρ∈)
    ...    | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ }
           | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₁ _ }
           , record { ↘⟦t⟧ = ↘⟦T⟧₁ ; ↘⟦t′⟧ = ↘⟦T′⟧₁ ; t≈t′ = T≈T′ }
          rewrite 𝕌-wellfounded-≡-𝕌 _ i<n₁
            with 𝕌-refl (𝕌-sym (𝕌-cumu (<⇒≤ i<n₁) T≈T′)) | 𝕌-cumu (<⇒≤ i<n₁) T≈T′
    ...        | T′∈ | T≈T′′
              rewrite ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₁ = record
                                          { ↘⟦T⟧ = ↘⟦T′⟧₁
                                          ; ↘⟦t⟧ = ↘⟦t⟧
                                          ; T∈𝕌 = T′∈𝕌′
                                          ; t∼⟦t⟧ = ®El-resp-T≈ T′∈𝕌′
                                                    (®El-transport T∈𝕌′ T′∈𝕌′ (𝕌-cumu (m≤n⊔m _ _) T≈T′′) (®El-cumu T∈𝕌 t∼⟦t⟧ (m≤m⊔n _ _)))
                                                    ([]-cong-Se′ (lift-⊢≈-Se S≈T (≤-trans (<⇒≤ i<n₁) (m≤n⊔m n _))) ⊢σ)
                                          }
      where
        T∈𝕌′ = 𝕌-cumu (m≤m⊔n n n₁) T∈𝕌
        T′∈𝕌′ = 𝕌-cumu (m≤n⊔m n n₁) T′∈


t[σ]′ : Δ ⊩ t ∶ T →
        Γ ⊩s σ ∶ Δ →
        ------------------
        Γ ⊩ t [ σ ] ∶ T [ σ ]
t[σ]′ {_} {t} {T} {Γ} {σ} (⊢Δ , n , trel) (⊢Γ₁ , ⊢Δ₁ , σrel₁) = ⊢Γ₁ , _ , helper
  where
    helper : ∀ {Δ δ ρ} →
             Δ ⊢s δ ∶ ⊢Γ₁ ® ρ →
             GluExp _ Δ (t [ σ ]) (T [ σ ]) δ ρ
    helper δ∼ρ
      with s®⇒⊢s ⊢Γ₁ δ∼ρ | σrel₁ δ∼ρ
    ...  | ⊢δ | record { ⟦τ⟧ = ⟦τ⟧ ; ↘⟦τ⟧ = ↘⟦τ⟧ ; τσ∼⟦τ⟧ = τσ∼⟦τ⟧ }
        with trel (s®-irrel ⊢Δ₁ ⊢Δ τσ∼⟦τ⟧)
    ...    | record { ⟦T⟧ = ⟦T⟧ ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ } = record
                                    { ↘⟦T⟧ = ⟦[]⟧ ↘⟦τ⟧ ↘⟦T⟧
                                    ; ↘⟦t⟧ = ⟦[]⟧ ↘⟦τ⟧ ↘⟦t⟧
                                    ; T∈𝕌 = T∈𝕌
                                    ; t∼⟦t⟧ = ®El-resp-≈
                                                  T∈𝕌
                                                  (®El-resp-T≈
                                                        T∈𝕌
                                                        t∼⟦t⟧
                                                  -- where can we get "⊢ σ" , "⊢ t" , and "⊢ T"?
                                                        (≈-sym ([∘]-Se {!!} {!!} ⊢δ)))
                                                  (≈-conv ([∘] ⊢δ {!!} {!⊢t!}) (≈-sym ([∘]-Se {!!} {!!} ⊢δ)))
                                    }
