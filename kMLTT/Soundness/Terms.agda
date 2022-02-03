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
conv′ {_} {t} {_} {T} ⊩t S≈T
  with ⊩t | fundamental-t≈t′ S≈T
...  | record { t∶T = t∶S ; ⊢Γ = ⊢Γ ; lvl = n ; krip = tkrip }
     | ⊨Γ₁ , n₁ , Trel₁                                          = record
                                                                   { t∶T = conv t∶S S≈T
                                                                   ; ⊢Γ = ⊢Γ
                                                                   ; krip = krip
                                                                   }
  where
    krip : ∀ {Δ σ ρ} →
           Δ ⊢s σ ∶ ⊢Γ ® ρ →
           GluExp _ Δ t T σ ρ
    krip σ∼ρ
      with fundamental-⊢Γ ⊢Γ | s®⇒⊢s ⊢Γ σ∼ρ | s®⇒⟦⟧ρ ⊢Γ σ∼ρ
    ...  | ⊨Γ                | ⊢σ            | ρ∈
        with tkrip σ∼ρ | Trel₁ (⊨-irrel ⊨Γ ⊨Γ₁ ρ∈)
    ...    | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ }
           | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₁ _ }
           , record { ↘⟦t⟧ = ↘⟦T⟧₁ ; ↘⟦t′⟧ = ↘⟦T′⟧₁ ; t≈t′ = T≈T′ }
          rewrite 𝕌-wellfounded-≡-𝕌 _ i<n₁
            with 𝕌-refl (𝕌-sym (𝕌-cumu (<⇒≤ i<n₁) T≈T′)) | 𝕌-cumu (<⇒≤ i<n₁) T≈T′
    ...        | T′∈                                      | T≈T′′
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
t[σ]′ {_} {t} {T} {Γ} {σ} ⊩t ⊩σ
  with ⊩t | ⊩σ
...  | record { t∶T = t∶T ; ⊢Γ = ⊢Δ ; lvl = n ; krip = tkrip }
     | record { ⊢τ = ⊢σ ; ⊢Γ = ⊢Γ₁ ; ⊢Γ′ = ⊢Δ₁ ; krip = σkrip₁ }
    with presup-tm t∶T
...    | _ , n′ , ⊢T        = record
                              { t∶T = t[σ] t∶T ⊢σ
                              ; ⊢Γ = ⊢Γ₁
                              ; krip = krip
                              }
  where
    krip : ∀ {Δ δ ρ} →
           Δ ⊢s δ ∶ ⊢Γ₁ ® ρ →
           GluExp _ Δ (t [ σ ]) (T [ σ ]) δ ρ
    krip δ∼ρ
      with s®⇒⊢s ⊢Γ₁ δ∼ρ | σkrip₁ δ∼ρ
    ...  | ⊢δ | record { ⟦τ⟧ = ⟦τ⟧ ; ↘⟦τ⟧ = ↘⟦τ⟧ ; τσ∼⟦τ⟧ = τσ∼⟦τ⟧ }
        with tkrip (s®-irrel ⊢Δ₁ ⊢Δ τσ∼⟦τ⟧)
    ...    | record { ⟦T⟧ = ⟦T⟧ ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ } = record
                                    { ↘⟦T⟧ = ⟦[]⟧ ↘⟦τ⟧ ↘⟦T⟧
                                    ; ↘⟦t⟧ = ⟦[]⟧ ↘⟦τ⟧ ↘⟦t⟧
                                    ; T∈𝕌 = T∈𝕌′
                                    ; t∼⟦t⟧ = ®El-resp-≈
                                                T∈𝕌′
                                                (®El-resp-T≈
                                                     T∈𝕌′
                                                     (®El-cumu T∈𝕌 t∼⟦t⟧ (m≤m⊔n n n′))
                                                     (≈-sym ([∘]-Se (lift-⊢-Se-max′ ⊢T) ⊢σ ⊢δ)))
                                                (≈-conv ([∘] ⊢δ ⊢σ t∶T) (≈-sym ([∘]-Se ⊢T ⊢σ ⊢δ)))
                                    }
      where
        T∈𝕌′ = 𝕌-cumu (m≤m⊔n n n′) T∈𝕌

vlookup′ : ∀ {x} →
           ⊢ Γ →
           x ∶ T ∈! Γ →
           ------------
           Γ ⊩ v x ∶ T
vlookup′ {_} {sub T wk} (⊢∺ ⊢Γ ⊢T) here
  with fundamental-⊢t ⊢T
... | ⊨Γ₁ , n₁ , Trel₁ = record { t∶T = vlookup (⊢∺ ⊢Γ ⊢T) here ; ⊢Γ = ⊢∺ ⊢Γ ⊢T ; lvl = {!!} ; krip = krip }
  where
    krip : ∀ {Δ σ ρ} →
           Δ ⊢s σ ∶ ⊢∺ ⊢Γ ⊢T ® ρ →
           GluExp _ Δ (v 0) (T [ wk ]) σ ρ
    krip σ∼ρ
      with fundamental-⊢Γ ⊢Γ | s®⇒⟦⟧ρ (⊢∺ ⊢Γ ⊢T) σ∼ρ
    ...  | ⊨Γ                | ρ∈ , _
        with σ∼ρ | Trel₁ (⊨-irrel ⊨Γ ⊨Γ₁ ρ∈)
    ...    | record { ⊢σ = ⊢σ ; ⊢T = ⊢T ; ≈pσ = ≈pσ ; ≈v0σ = ≈v0σ ; ↘⟦T⟧ = ↘⟦T⟧ ; T∈𝕌 = T∈𝕌 ; t∼ρ0 = t∼ρ0 ; step = step }
           | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₁ _ }
           , record { ↘⟦t⟧ = ↘⟦T⟧₁ ; ↘⟦t′⟧ = ↘⟦T′⟧₁ ; t≈t′ = T≈T′ }
           rewrite 𝕌-wellfounded-≡-𝕌 _ i<n₁
                 | ⟦⟧-det ↘⟦T′⟧₁ ↘⟦T⟧₁
                 | ⟦⟧-det ↘⟦T⟧₁ ↘⟦T⟧ = record
                { ↘⟦T⟧ = ⟦[]⟧ ⟦wk⟧ ↘⟦T⟧
                ; ↘⟦t⟧ = ⟦v⟧ 0
                ; T∈𝕌 = T≈T′
                ; t∼⟦t⟧ = {!!}
                }
vlookup′ ⊢Γ (there x∈) = {!!}
