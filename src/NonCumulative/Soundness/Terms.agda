{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Semantic judgments for other term related rules
module NonCumulative.Soundness.Terms (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂) where

open import Lib
open import Data.Nat.Properties as ℕₚ

open import NonCumulative.Statics.Ascribed.Misc
open import NonCumulative.Statics.Ascribed.Properties
open import NonCumulative.Statics.Ascribed.Refl
open import NonCumulative.Statics.Ascribed.Presup
open import NonCumulative.Semantics.Properties.PER fext
open import NonCumulative.Completeness.Fundamental fext
open import NonCumulative.Soundness.LogRel
open import NonCumulative.Soundness.ToSyntax fext
open import NonCumulative.Soundness.Properties.LogRel fext
open import NonCumulative.Soundness.Properties.Substitutions fext

conv′ : ∀ {i} →
        Γ ⊩ t ∶[ i ] S →
        Γ ⊢ S ≈ T ∶[ 1 + i ] Se i →
        ------------------
        Γ ⊩ t ∶[ i ] T
conv′ {_} {t} {_} {T} ⊩t S≈T
  with ⊩t | fundamental-t≈t′ S≈T
...  | record { ⊩Γ = ⊩Γ ; krip = tkrip }
     | ⊨Γ₁ , Trel₁ = record { ⊩Γ = ⊩Γ ; krip = krip }
  where
    krip : ∀ {Δ σ ρ} →
           Δ ⊢s σ ∶ ⊩Γ ® ρ →
           GluExp _ Δ t T σ ρ
    krip σ®ρ
      with s®⇒⊢s ⊩Γ σ®ρ | s®⇒⟦⟧ρ ⊩Γ σ®ρ
    ...  | ⊢σ
         | ⊨Γ , ρ∈
        with tkrip σ®ρ | Trel₁ (⊨-irrel ⊨Γ ⊨Γ₁ ρ∈)
    ...    | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ }
           | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₁ _ }
           , record { ⟦t⟧ = ⟦T⟧ ; ⟦t′⟧ = ⟦T⟧′ ; ↘⟦t⟧ = ↘⟦T⟧₁ ; ↘⟦t′⟧ = ↘⟦T′⟧₁ ; t≈t′ = T≈T′ }
          rewrite ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₁
                | 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym i<n₁)) = record
            { ⟦T⟧ = _
            ; ⟦t⟧ = _
            ; ↘⟦T⟧ = ↘⟦T′⟧₁
            ; ↘⟦t⟧ = ↘⟦t⟧
            ; T∈𝕌 = 𝕌-trans (𝕌-sym T≈T′) T≈T′
            ; t∼⟦t⟧ = ®El-transport T∈𝕌 (𝕌-trans (𝕌-sym T≈T′) T≈T′) T≈T′ (®El-resp-T≈ T∈𝕌 t∼⟦t⟧ ([]-cong-Se′ S≈T ⊢σ))
            }

t[σ]′ : ∀ {i} → Δ ⊩ t ∶[ i ] T →
        Γ ⊩s σ ∶ Δ →
        ------------------
        Γ ⊩ t [ σ ] ∶[ i ] T [ σ ]
t[σ]′ {_} {t} {T} {Γ} {σ} {i} ⊩t ⊩σ
  with ⊩t | ⊩σ | ⊩⇒⊢-ty ⊩t
...  | record { ⊩Γ = ⊩Δ ; krip = tkrip }
     | record { ⊩Γ = ⊩Γ₁ ; ⊩Γ′ = ⊩Δ₁ ; krip = σkrip₁ }
     | ⊢T
     = record { ⊩Γ = ⊩Γ₁ ; krip = krip }
  where
    ⊢t = ⊩⇒⊢-tm ⊩t
    krip : ∀ {Δ δ ρ} →
           Δ ⊢s δ ∶ ⊩Γ₁ ® ρ →
           GluExp i Δ (t [ σ ]) (T [ σ ]) δ ρ
    krip δ∼ρ
      with s®⇒⊢s ⊩Γ₁ δ∼ρ | σkrip₁ δ∼ρ
    ...  | ⊢δ | record { ⟦τ⟧ = ⟦τ⟧ ; ↘⟦τ⟧ = ↘⟦τ⟧ ; τσ∼⟦τ⟧ = τσ∼⟦τ⟧ }
        with tkrip (s®-irrel ⊩Δ₁ ⊩Δ τσ∼⟦τ⟧)
    ...    | record { ⟦T⟧ = ⟦T⟧ ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ } = record
        { ⟦T⟧ = _
        ; ⟦t⟧ = _
        ; ↘⟦T⟧ = ⟦[]⟧ ↘⟦τ⟧ ↘⟦T⟧
        ; ↘⟦t⟧ = ⟦[]⟧ ↘⟦τ⟧ ↘⟦t⟧
        ; T∈𝕌 = T∈𝕌
        ; t∼⟦t⟧ = ®El-resp-≈ T∈𝕌 (®El-resp-T≈ T∈𝕌 t∼⟦t⟧ (≈-sym Tσδ≈)) (≈-conv ([∘] ⊢δ ⊢σ ⊢t) (≈-sym Tσδ≈))
        }
      where
        ⊢σ = ⊩s⇒⊢s ⊩σ
        Tσδ≈ = [∘]-Se ⊢T ⊢σ ⊢δ

vlookup′ : ∀ {x i} →
           ⊩ Γ →
           x ∶[ i ] T ∈! Γ →
           ------------
           Γ ⊩ v x ∶[ i ] T
vlookup′ ⊩ΓT@(⊩∷ {T = T} ⊩Γ ⊢T gluT) here = record
  { ⊩Γ = ⊩ΓT
  ; krip = krip
  }
  where
    krip : ∀ {Δ σ ρ} →
            Δ ⊢s σ ∶ ⊩∷ ⊩Γ ⊢T gluT ® ρ →
            GluExp _ Δ (v 0) (T [ wk ]) σ ρ
    krip σ∼ρ
        with σ∼ρ
    ...    | record { ⊢σ = ⊢σ ; ≈pσ = ≈pσ ; ≈v0σ = ≈v0σ ; ↘⟦T⟧ = ↘⟦T⟧ ; T∈𝕌 = T∈𝕌 ; t∼ρ0 = t∼ρ0 ; step = step }
          with gluT step
    ...      | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; T∈𝕌 = T∈𝕌₁ ; T∼⟦T⟧ = T∼⟦T⟧ }
            rewrite ⟦⟧-det ↘⟦T⟧₁ ↘⟦T⟧ = record
                                        { ↘⟦T⟧ = ⟦[]⟧ ⟦wk⟧ ↘⟦T⟧
                                        ; ↘⟦t⟧ = ⟦v⟧ 0
                                        ; T∈𝕌 = T∈𝕌₁
                                        ; t∼⟦t⟧ = ®El-≡ _ _ (®El-resp-T≈ _ (®El-resp-≈ _ t∼ρ0 (≈-sym ≈v0σ))
                                                           (≈-trans ([]-cong-Se (≈-refl ⊢T) (proj₁ (proj₂ (proj₂ (presup-s-≈ ≈pσ)))) (s-≈-sym ≈pσ))
                                                                    (≈-sym ([∘]-Se ⊢T (s-wk (⊩⇒⊢ ⊩ΓT)) ⊢σ)))) refl
                                        }
vlookup′ {_} {sub T wk} {x = suc x} {i = i} (⊩∷ {T = S} ⊩Γ ⊢S gluS) (there x∈Γ)
  with vlookup′ ⊩Γ x∈Γ
...  | ⊩x@record { ⊩Γ = ⊩Γ₁ ; krip = ⊢krip } = record { ⊩Γ = ⊩∷ ⊩Γ ⊢S gluS ; krip = krip }
  where
    ⊢T  = ⊩⇒⊢-ty ⊩x
    ⊢x  = ⊩⇒⊢-tm ⊩x
    ⊢Γ  = ⊩⇒⊢ ⊩Γ
    ⊢SΓ = ⊢∷ ⊢Γ ⊢S

    krip : ∀ {Δ σ ρ} →
           Δ ⊢s σ ∶ ⊩∷ ⊩Γ ⊢S gluS ® ρ →
           GluExp i Δ (v (1 + x)) (T [ wk ]) σ ρ
    krip {Δ} {σ} σ®ρ
      with σ®ρ
    ...  | record { ⊢σ = ⊢σ ; pσ = pσ ; ≈pσ = ≈pσ ; step = step }
        with ⊢krip (s®-irrel ⊩Γ ⊩Γ₁ step)
    ...    | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦t⟧ = ⟦v⟧ _ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ } = record
                                        { ↘⟦T⟧ = ⟦[]⟧ ⟦wk⟧ ↘⟦T⟧
                                        ; ↘⟦t⟧ = ⟦v⟧ _
                                        ; T∈𝕌 = T∈𝕌
                                        ; t∼⟦t⟧ = ®El-resp-T≈ _ (®El-resp-≈ _ t∼⟦t⟧ x[pσ]≈suc[x][σ]) (≈-sym T[wk][σ]≈T[pσ])
                                        }
      where
        T[wk][σ]≈T[pσ] = ≈-trans ([∘]-Se ⊢T (s-wk ⊢SΓ) ⊢σ) ([]-cong-Se‴ ⊢T ≈pσ)

        x[pσ]≈suc[x][σ] : Δ ⊢ v x [ pσ ] ≈ v (1 + x) [ σ ] ∶[ i ] sub T pσ
        x[pσ]≈suc[x][σ] =
          begin
            v x [ pσ ]
          ≈⟨ []-cong (v-≈ ⊢Γ x∈Γ) (s-≈-sym ≈pσ) ⟩
            v x [ p σ ]
          ≈⟨ ≈-conv ([∘] ⊢σ (s-wk ⊢SΓ) ⊢x) ([]-cong-Se‴ ⊢T ≈pσ) ⟩
            v x [ wk ] [ σ ]
          ≈⟨ ≈-conv ([]-cong ([wk] ⊢Γ ⊢S x∈Γ) (s-≈-refl ⊢σ)) T[wk][σ]≈T[pσ] ⟩
            v (1 + x) [ σ ]
          ∎
          where
            open ER