{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Semantic judgments for other term related rules
module MLTT.Soundness.Terms (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Lib
open import Data.Nat.Properties as ℕₚ

open import MLTT.Statics.Properties
open import MLTT.Semantics.Properties.PER fext
open import MLTT.Completeness.Fundamental fext
open import MLTT.Soundness.Cumulativity fext
open import MLTT.Soundness.LogRel
open import MLTT.Soundness.ToSyntax fext
open import MLTT.Soundness.Properties.LogRel fext
open import MLTT.Soundness.Properties.Substitutions fext


conv′ : ∀ {i} →
        Γ ⊩ t ∶ S →
        Γ ⊢ S ≈ T ∶ Se i →
        ------------------
        Γ ⊩ t ∶ T
conv′ {_} {t} {_} {T} ⊩t S≈T
  with ⊩t | fundamental-t≈t′ S≈T
...  | record { ⊩Γ = ⊩Γ ; lvl = n ; krip = tkrip }
     | ⊨Γ₁ , n₁ , Trel₁                                          = record { ⊩Γ = ⊩Γ ; krip = krip }
  where
    krip : ∀ {Δ σ ρ} →
           Δ ⊢s σ ∶ ⊩Γ ® ρ →
           GluExp _ Δ t T σ ρ
    krip σ∼ρ
      with s®⇒⊢s ⊩Γ σ∼ρ | s®⇒⟦⟧ρ ⊩Γ σ∼ρ
    ...  | ⊢σ            | ⊨Γ , ρ∈
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
  with ⊩t | ⊩σ | ⊩⇒⊢-ty ⊩t
...  | record { ⊩Γ = ⊩Δ ; lvl = n ; krip = tkrip }
     | record { ⊩Γ = ⊩Γ₁ ; ⊩Γ′ = ⊩Δ₁ ; krip = σkrip₁ }
     | ⊢T
     = record
  { ⊩Γ   = ⊩Γ₁
  ; krip = krip
  }
  where
    ⊢t = ⊩⇒⊢-tm ⊩t
    krip : ∀ {Δ δ ρ} →
           Δ ⊢s δ ∶ ⊩Γ₁ ® ρ →
           GluExp _ Δ (t [ σ ]) (T [ σ ]) δ ρ
    krip δ∼ρ
      with s®⇒⊢s ⊩Γ₁ δ∼ρ | σkrip₁ δ∼ρ
    ...  | ⊢δ | record { ⟦τ⟧ = ⟦τ⟧ ; ↘⟦τ⟧ = ↘⟦τ⟧ ; τσ∼⟦τ⟧ = τσ∼⟦τ⟧ }
        with tkrip (s®-irrel ⊩Δ₁ ⊩Δ τσ∼⟦τ⟧)
    ...    | record { ⟦T⟧ = ⟦T⟧ ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ } = record
                                    { ↘⟦T⟧ = ⟦[]⟧ ↘⟦τ⟧ ↘⟦T⟧
                                    ; ↘⟦t⟧ = ⟦[]⟧ ↘⟦τ⟧ ↘⟦t⟧
                                    ; T∈𝕌 = T∈𝕌
                                    ; t∼⟦t⟧ = ®El-resp-≈
                                                T∈𝕌
                                                (®El-resp-T≈
                                                     T∈𝕌
                                                     t∼⟦t⟧
                                                     (≈-sym ([∘]-Se ⊢T ⊢σ ⊢δ)))
                                                (≈-conv ([∘] ⊢δ ⊢σ ⊢t) (≈-sym ([∘]-Se ⊢T ⊢σ ⊢δ)))
                                    }
      where
        ⊢σ = ⊩s⇒⊢s ⊩σ

vlookup′ : ∀ {x} →
           ⊩ Γ →
           x ∶ T ∈! Γ →
           ------------
           Γ ⊩ v x ∶ T
vlookup′ {_} {sub T wk} (⊩∷ ⊩Γ ⊢T gT) here = record { ⊩Γ = ⊩∷ ⊩Γ ⊢T gT ; krip = krip }
  where
    krip : ∀ {Δ σ ρ} →
           Δ ⊢s σ ∶ ⊩∷ ⊩Γ ⊢T gT ® ρ →
           GluExp _ Δ (v 0) (T [ wk ]) σ ρ
    krip σ∼ρ
        with σ∼ρ
    ...    | record { ⊢σ = ⊢σ ; ≈pσ = ≈pσ ; ≈v0σ = ≈v0σ ; ↘⟦T⟧ = ↘⟦T⟧ ; T∈𝕌 = T∈𝕌 ; t∼ρ0 = t∼ρ0 ; step = step }
          with gT step
    ...      | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; T∈𝕌 = T∈𝕌₁ ; T∼⟦T⟧ = T∼⟦T⟧ }
            rewrite ⟦⟧-det ↘⟦T⟧₁ ↘⟦T⟧ = record
                                        { ↘⟦T⟧ = ⟦[]⟧ ⟦wk⟧ ↘⟦T⟧
                                        ; ↘⟦t⟧ = ⟦v⟧ 0
                                        ; T∈𝕌 = T∈𝕌₁
                                        ; t∼⟦t⟧ = ®El-resp-T≈
                                                     T∈𝕌₁
                                                     (®El-resp-≈ T∈𝕌₁ (®El-irrel T∈𝕌 T∈𝕌₁ T∼⟦T⟧ t∼ρ0) (≈-sym ≈v0σ))
                                                     (≈-sym (≈-trans ([∘]-Se ⊢T (s-wk (⊢∷ (⊩⇒⊢ ⊩Γ) ⊢T)) ⊢σ) ([]-cong-Se″ ⊢T ≈pσ)))
                                        }
vlookup′ {_} {sub T wk} {suc x} (⊩∷ ⊩Γ ⊢S gS) (there x∈)
  with vlookup′ ⊩Γ x∈
...  | ⊩x@record { ⊩Γ = ⊩Γ₁ ; lvl = lvl ; krip = ⊢krip } = record { ⊩Γ = ⊩∷ ⊩Γ ⊢S gS ; krip = krip }
  where
    ⊢T  = ⊩⇒⊢-ty ⊩x
    ⊢x  = ⊩⇒⊢-tm ⊩x
    ⊢Γ  = ⊩⇒⊢ ⊩Γ
    ⊢SΓ = ⊢∷ ⊢Γ ⊢S

    krip : ∀ {Δ σ ρ} →
           Δ ⊢s σ ∶ ⊩∷ ⊩Γ ⊢S gS ® ρ →
           GluExp lvl Δ (v (1 + x)) (T [ wk ]) σ ρ
    krip {Δ} {σ} σ∼ρ
      with σ∼ρ
    ...  | record { ⊢σ = ⊢σ ; pσ = pσ ; ≈pσ = ≈pσ ; step = step }
        with ⊢krip (s®-irrel ⊩Γ ⊩Γ₁ step)
    ...    | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦t⟧ = ⟦v⟧ _ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ } = record
                                        { ↘⟦T⟧ = ⟦[]⟧ ⟦wk⟧ ↘⟦T⟧
                                        ; ↘⟦t⟧ = ⟦v⟧ _
                                        ; T∈𝕌 = T∈𝕌
                                        ; t∼⟦t⟧ = ®El-resp-T≈ T∈𝕌 (®El-resp-≈ T∈𝕌 t∼⟦t⟧ x[pσ]≈suc[x][σ]) (≈-sym T[wk][σ]≈T[pσ])
                                        }
     where
       T[wk][σ]≈T[pσ] = ≈-trans ([∘]-Se ⊢T (s-wk ⊢SΓ) ⊢σ) ([]-cong-Se″ ⊢T ≈pσ)

       x[pσ]≈suc[x][σ] : Δ ⊢ v x [ pσ ] ≈ v (1 + x) [ σ ] ∶ sub T pσ
       x[pσ]≈suc[x][σ] =
         begin
           v x [ pσ ]
         ≈⟨ []-cong (v-≈ ⊢Γ x∈) (s-≈-sym ≈pσ) ⟩
           v x [ p σ ]
         ≈⟨ ≈-conv ([∘] ⊢σ (s-wk ⊢SΓ) ⊢x) ([]-cong-Se″ ⊢T ≈pσ) ⟩
           v x [ wk ] [ σ ]
         ≈⟨ ≈-conv ([]-cong ([wk] ⊢SΓ x∈) (s-≈-refl ⊢σ)) T[wk][σ]≈T[pσ] ⟩
           v (1 + x) [ σ ]
         ∎
         where
           open ER
