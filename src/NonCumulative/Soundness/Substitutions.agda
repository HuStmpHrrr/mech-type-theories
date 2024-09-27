{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Semantic judgments for substitutions
module NonCumulative.Soundness.Substitutions (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂) where

open import Lib
open import Data.Nat.Properties

open import NonCumulative.Statics.Ascribed.Misc
open import NonCumulative.Statics.Ascribed.Properties
open import NonCumulative.Statics.Ascribed.Presup
open import NonCumulative.Semantics.Properties.PER fext
open import NonCumulative.Soundness.LogRel
open import NonCumulative.Soundness.ToSyntax fext
open import NonCumulative.Soundness.Contexts fext
open import NonCumulative.Soundness.Properties.LogRel fext
open import NonCumulative.Soundness.Properties.Substitutions fext

s-I′ : ⊩ Γ →
       ------------
       Γ ⊩s I ∶ Γ
s-I′ ⊩Γ = record
  { ⊩Γ   = ⊩Γ
  ; ⊩Γ′  = ⊩Γ
  ; krip = helper
  }
  where
    helper : Δ ⊢s σ ∶ ⊩Γ ® ρ → GluSubst Δ I ⊩Γ σ ρ
    helper {ρ = ρ} σ∼ρ = record
      { ⟦τ⟧    = ρ
      ; ↘⟦τ⟧   = ⟦I⟧
      ; τσ∼⟦τ⟧ = s®-resp-s≈ ⊩Γ σ∼ρ (s-≈-sym (I-∘ (s®⇒⊢s ⊩Γ σ∼ρ)))
      }

s-wk′ : ∀ {i} →
        ⊩ (T ↙ i) ∷ Γ →
        ------------------
        (T ↙ i) ∷ Γ ⊩s wk ∶ Γ
s-wk′ ⊩TΓ@(⊩∷ ⊩Γ ⊢T gT) = record
  { ⊩Γ   = ⊩TΓ
  ; ⊩Γ′  = ⊩Γ
  ; krip = helper
  }
  where
    helper : Δ ⊢s σ ∶ ⊩TΓ ® ρ → GluSubst Δ wk ⊩Γ σ ρ
    helper {ρ = ρ} σ∼ρ = record
      { ⟦τ⟧    = drop ρ
      ; ↘⟦τ⟧   = ⟦wk⟧
      ; τσ∼⟦τ⟧ = s®-resp-s≈ ⊩Γ step (s-≈-sym ≈pσ)
      }
      where open Glu∷ σ∼ρ

s-∘′ : Γ ⊩s τ ∶ Γ′ →
       Γ′ ⊩s σ ∶ Γ″ →
       ----------------
       Γ ⊩s σ ∘ τ ∶ Γ″
s-∘′ {_} {τ} {_} {σ} ⊩τ ⊩σ = record
  { ⊩Γ   = ⊩τ.⊩Γ
  ; ⊩Γ′  = ⊩σ.⊩Γ′
  ; krip = helper
  }
  where
    module ⊩τ = _⊩s_∶_ ⊩τ
    module ⊩σ = _⊩s_∶_ ⊩σ
    ⊢τ = ⊩s⇒⊢s ⊩τ
    ⊢σ = ⊩s⇒⊢s ⊩σ
    helper : Δ ⊢s σ′ ∶ ⊩τ.⊩Γ ® ρ → GluSubst Δ (σ ∘ τ) ⊩σ.⊩Γ′ σ′ ρ
    helper {_} {σ′} {ρ} σ′∼ρ = record
      { ⟦τ⟧    = σ.⟦τ⟧
      ; ↘⟦τ⟧  = ⟦∘⟧ τ.↘⟦τ⟧ σ.↘⟦τ⟧
      ; τσ∼⟦τ⟧ = s®-resp-s≈ ⊩σ.⊩Γ′ σ.τσ∼⟦τ⟧ (s-≈-sym (∘-assoc ⊢σ ⊢τ (s®⇒⊢s ⊩τ.⊩Γ σ′∼ρ)))
      }
      where
        module τ = GluSubst (⊩τ.krip σ′∼ρ)
        module σ = GluSubst (⊩σ.krip (s®-irrel ⊩τ.⊩Γ′ ⊩σ.⊩Γ τ.τσ∼⟦τ⟧))

s-,′ : ∀ {i} →
       Γ ⊩s σ ∶ Δ →
       Δ ⊩ T ∶[ 1 + i ] Se i →
       Γ ⊩ t ∶[ i ] T [ σ ] →
       -------------------
       Γ ⊩s (σ , t ∶ T ↙ i) ∶ (T ↙ i) ∷ Δ
s-,′ {_} {σ} {Δ} {T} {t} {i} ⊩σ ⊩T ⊩t = record
  { ⊩Γ   = ⊩σ.⊩Γ
  ; ⊩Γ′  = ⊩TΔ
  ; krip = helper
  }
    where
      module ⊩σ = _⊩s_∶_ ⊩σ
      module ⊩T = _⊩_∶[_]_ ⊩T
      module ⊩t = _⊩_∶[_]_ ⊩t
      ⊢σ  = ⊩s⇒⊢s ⊩σ
      ⊢t  = ⊩⇒⊢-tm ⊩t
      ⊢T  = ⊩⇒⊢-tm ⊩T
      ⊩TΔ = ⊢∷′ ⊩T
      ⊢TΔ = ⊩⇒⊢ ⊩TΔ
      helper : Δ′ ⊢s τ ∶ ⊩σ.⊩Γ ® ρ → GluSubst Δ′ (σ , t ∶ T ↙ i) ⊩TΔ τ ρ
      helper {Δ′} {τ} {ρ} τ∼ρ
        with ⊩σ.krip τ∼ρ
          | ⊩t.krip (s®-irrel ⊩σ.⊩Γ ⊩t.⊩Γ τ∼ρ)
      ...  | στ@record { ⟦τ⟧ = ⟦τ⟧ ; ↘⟦τ⟧ = ↘⟦τ⟧ ; τσ∼⟦τ⟧ = τσ∼⟦τ⟧ }
          | record { ⟦T⟧ = ⟦T⟧ ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ⟦[]⟧ ↘ρ′ ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ }
          rewrite ⟦⟧s-det ↘ρ′ ↘⟦τ⟧
          with s®-irrel ⊩σ.⊩Γ′ ⊩T.⊩Γ τσ∼⟦τ⟧
      ...     | τσ∼⟦τ⟧′
              with ⊩T.krip τσ∼⟦τ⟧′ | s®-cons ⊩TΔ τσ∼⟦τ⟧′
      ...        | record { ↘⟦T⟧ = ⟦Se⟧ .i ; ↘⟦t⟧ = ↘⟦T⟧′ ; T∈𝕌 = U eq _ ; t∼⟦t⟧ = T∼⟦T⟧ } | cons
                rewrite 𝕌-wf-gen _ (λ l<j → <-trans l<j (≤-reflexive (sym eq)))
                      | Glu-wellfounded-≡ (≤-reflexive (sym eq))
                      | ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧ = record
                          { ⟦τ⟧ = ⟦τ⟧ ↦ ⟦t⟧
                          ; ↘⟦τ⟧ = ⟦,⟧ ↘⟦τ⟧ ↘⟦t⟧
                          ; τσ∼⟦τ⟧ = record
                            { ⊢σ = ⊢σtτ
                            ; pσ = ∷.pσ
                            ; v0σ = ∷.v0σ
                            ; ⟦T⟧ = ∷.⟦T⟧
                            ; ≈pσ = ≈pσ
                            ; ≈v0σ = ≈-trans (≈-conv ([]-cong (v-≈ ⊢TΔ here) eq₁) (≈-trans ([∘]-Se ⊢T (s-wk ⊢TΔ) ⊢σtτ) ([]-cong-Se‴ ⊢T ≈pσ))) ∷.≈v0σ
                            ; ↘⟦T⟧ = ∷.↘⟦T⟧
                            ; T∈𝕌 = ∷.T∈𝕌
                            ; t∼ρ0 = ∷.t∼ρ0
                            ; step = ∷.step
                            }
                          }
          where
            module T = GluU T∼⟦T⟧
            ⊢τ   = s®⇒⊢s ⊩σ.⊩Γ τ∼ρ
            ⊢σ,t = s-, ⊢σ ⊢T ⊢t
            ⊢σtτ = s-∘ ⊢τ ⊢σ,t
            module ∷ = Glu∷ (cons (®El-transport T∈𝕌 T.A∈𝕌 T∈𝕌 (®El-resp-T≈ T∈𝕌 t∼⟦t⟧ ([∘]-Se ⊢T ⊢σ ⊢τ))))

            eq₁ = ,-∘ ⊢σ ⊢T ⊢t ⊢τ
            eq₂ = ∘-cong eq₁ (wk-≈ ⊢TΔ)
            ≈pσ = s-≈-trans eq₂ ∷.≈pσ

s-conv′ : Γ ⊩s σ ∶ Δ →
          ⊢ Δ ≈ Δ′ →
          -------------
          Γ ⊩s σ ∶ Δ′
s-conv′ {_} {σ} ⊩σ Δ≈Δ′ = record
  { ⊩Γ   = ⊩σ.⊩Γ
  ; ⊩Γ′  = ⊩Δ′
  ; krip = helper
  }
  where
    module ⊩σ = _⊩s_∶_ ⊩σ
    ⊩Δ′ = ⊩-resp-≈ ⊩σ.⊩Γ′ Δ≈Δ′
    helper : Δ″ ⊢s τ ∶ ⊩σ.⊩Γ ® ρ → GluSubst Δ″ σ ⊩Δ′ τ ρ
    helper {_} {τ} τ∼ρ = record
      { ⟦τ⟧    = ⟦τ⟧
      ; ↘⟦τ⟧   = ↘⟦τ⟧
      ; τσ∼⟦τ⟧ = s®-resp-≈′ ⊩σ.⊩Γ′ ⊩Δ′ τσ∼⟦τ⟧ Δ≈Δ′
      }
      where open GluSubst (⊩σ.krip τ∼ρ)