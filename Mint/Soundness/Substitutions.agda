{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

-- Semantic judgments for substitutions
module Mint.Soundness.Substitutions (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Data.Nat.Properties

open import Mint.Statics.Properties
open import Mint.Semantics.Properties.Domain fext
open import Mint.Semantics.Properties.PER fext
open import Mint.Soundness.Cumulativity fext
open import Mint.Soundness.LogRel
open import Mint.Soundness.ToSyntax fext
open import Mint.Soundness.Contexts fext
open import Mint.Soundness.Properties.LogRel fext
open import Mint.Soundness.Properties.Substitutions fext


s-I′ : ⊩ Γ →
       ------------
       Γ ⊩s I ∶ Γ
s-I′ ⊩Γ = record
  { ⊩Γ   = ⊩Γ
  ; ⊩Γ′  = ⊩Γ
  ; krip = helper
  }
  where helper : Δ ⊢s σ ∶ ⊩Γ ® ρ → GluSubsts Δ I ⊩Γ σ ρ
        helper {ρ = ρ} σ∼ρ = record
          { ⟦τ⟧    = ρ
          ; ↘⟦τ⟧   = ⟦I⟧
          ; τσ∼⟦τ⟧ = s®-resp-s≈ ⊩Γ σ∼ρ (s-≈-sym (I-∘ (s®⇒⊢s ⊩Γ σ∼ρ)))
          }

s-wk′ : ⊩ T ∺ Γ →
        ------------------
        T ∺ Γ ⊩s wk ∶ Γ
s-wk′ ⊩TΓ@(⊩∺ ⊩Γ ⊢T gT) = record
  { ⊩Γ   = ⊩TΓ
  ; ⊩Γ′  = ⊩Γ
  ; krip = helper
  }
  where helper : Δ ⊢s σ ∶ ⊩TΓ ® ρ → GluSubsts Δ wk ⊩Γ σ ρ
        helper {ρ = ρ} σ∼ρ = record
          { ⟦τ⟧    = drop ρ
          ; ↘⟦τ⟧   = ⟦wk⟧
          ; τσ∼⟦τ⟧ = s®-resp-s≈ ⊩Γ step (s-≈-sym ≈pσ)
          }
          where open Glu∺ σ∼ρ

s-∘′ : Γ ⊩s τ ∶ Γ′ →
       Γ′ ⊩s σ ∶ Γ″ →
       ----------------
       Γ ⊩s σ ∘ τ ∶ Γ″
s-∘′ {_} {τ} {_} {σ} ⊩τ ⊩σ = record
  { ⊩Γ   = ⊩τ.⊩Γ
  ; ⊩Γ′  = ⊩σ.⊩Γ′
  ; krip = helper
  }
  where module ⊩τ = _⊩s_∶_ ⊩τ
        module ⊩σ = _⊩s_∶_ ⊩σ
        ⊢τ = ⊩s⇒⊢s ⊩τ
        ⊢σ = ⊩s⇒⊢s ⊩σ
        helper : Δ ⊢s σ′ ∶ ⊩τ.⊩Γ ® ρ → GluSubsts Δ (σ ∘ τ) ⊩σ.⊩Γ′ σ′ ρ
        helper {_} {σ′} {ρ} σ′∼ρ = record
          { ⟦τ⟧    = σ.⟦τ⟧
          ; ↘⟦τ⟧   = ⟦∘⟧ τ.↘⟦τ⟧ σ.↘⟦τ⟧
          ; τσ∼⟦τ⟧ = s®-resp-s≈ ⊩σ.⊩Γ′ σ.τσ∼⟦τ⟧ (s-≈-sym (∘-assoc ⊢σ ⊢τ (s®⇒⊢s ⊩τ.⊩Γ σ′∼ρ)))
          }
          where module τ = GluSubsts (⊩τ.krip σ′∼ρ)
                module σ = GluSubsts (⊩σ.krip (s®-irrel ⊩τ.⊩Γ′ ⊩σ.⊩Γ τ.τσ∼⟦τ⟧))

s-,′ : ∀ {i} →
       Γ ⊩s σ ∶ Δ →
       Δ ⊩ T ∶ Se i →
       Γ ⊩ t ∶ T [ σ ] →
       -------------------
       Γ ⊩s σ , t ∶ T ∺ Δ
s-,′ {_} {σ} {Δ} {T} {t} {i} ⊩σ ⊩T ⊩t = record
  { ⊩Γ   = ⊩σ.⊩Γ
  ; ⊩Γ′  = ⊩TΔ
  ; krip = helper
  }
  where module ⊩σ = _⊩s_∶_ ⊩σ
        module ⊩T = _⊩_∶_ ⊩T
        module ⊩t = _⊩_∶_ ⊩t
        ⊢σ  = ⊩s⇒⊢s ⊩σ
        ⊢t  = ⊩⇒⊢-tm ⊩t
        ⊢T  = ⊩⇒⊢-tm ⊩T
        ⊩TΔ = ⊢∺′ ⊩T
        ⊢TΔ = ⊩⇒⊢ ⊩TΔ
        helper : Δ′ ⊢s τ ∶ ⊩σ.⊩Γ ® ρ → GluSubsts Δ′ (σ , t) ⊩TΔ τ ρ
        helper {Δ′} {τ} {ρ} τ∼ρ
          with ⊩σ.krip τ∼ρ
             | ⊩t.krip (s®-irrel ⊩σ.⊩Γ ⊩t.⊩Γ τ∼ρ)
        ...  | στ@record { ⟦τ⟧ = ⟦τ⟧ ; ↘⟦τ⟧ = ↘⟦τ⟧ ; τσ∼⟦τ⟧ = τσ∼⟦τ⟧ }
             | record { ⟦T⟧ = ⟦T⟧ ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ⟦[]⟧ ↘ρ′ ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ }
             rewrite ⟦⟧s-det ↘ρ′ ↘⟦τ⟧
             with s®-irrel ⊩σ.⊩Γ′ ⊩T.⊩Γ τσ∼⟦τ⟧
        ...     | τσ∼⟦τ⟧′
                with ⊩T.krip τσ∼⟦τ⟧′ | s®-cons ⊩TΔ τσ∼⟦τ⟧′
        ...        | record { ↘⟦T⟧ = ⟦Se⟧ .i ; ↘⟦t⟧ = ↘⟦T⟧′ ; T∈𝕌 = U i<l _ ; t∼⟦t⟧ = T∼⟦T⟧ } | cons
                   rewrite Glu-wellfounded-≡ i<l
                         | ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧ = record
                     { ⟦τ⟧    = ⟦τ⟧ ↦ ⟦t⟧
                     ; ↘⟦τ⟧   = ⟦,⟧ ↘⟦τ⟧ ↘⟦t⟧
                     ; τσ∼⟦τ⟧ = record
                       { ⊢σ   = ⊢σtτ
                       ; pσ   = ∺.pσ
                       ; v0σ  = ∺.v0σ
                       ; ⟦T⟧  = ∺.⟦T⟧
                       ; ≈pσ  = ≈pσ
                       ; ≈v0σ = ≈-trans (≈-conv ([]-cong (v-≈ ⊢TΔ here) eq₁) (≈-trans ([∘]-Se ⊢T (s-wk ⊢TΔ) ⊢σtτ) ([]-cong-Se″ ⊢T ≈pσ))) ∺.≈v0σ
                       ; ↘⟦T⟧ = ∺.↘⟦T⟧
                       ; T∈𝕌  = ∺.T∈𝕌
                       ; t∼ρ0 = ∺.t∼ρ0
                       ; step = ∺.step
                       }
                     }
          where module T = GluU T∼⟦T⟧
                ⊢τ   = s®⇒⊢s ⊩σ.⊩Γ τ∼ρ
                ⊢σ,t = s-, ⊢σ ⊢T ⊢t
                ⊢σtτ = s-∘ ⊢τ ⊢σ,t
                module ∺ = Glu∺ (cons (®El-master T∈𝕌 T.A∈𝕌 T.A∈𝕌 T.rel t∼⟦t⟧ ([∘]-Se ⊢T ⊢σ ⊢τ)))

                eq₁ = ,-∘ ⊢σ ⊢T ⊢t ⊢τ
                eq₂ = ∘-cong eq₁ (wk-≈ ⊢TΔ)
                ≈pσ = s-≈-trans eq₂ ∺.≈pσ

s-；′ : ∀ {n} Ψs →
       Γ ⊩s σ ∶ Δ →
       ⊩ Ψs ++⁺ Γ →
       len Ψs ≡ n →
       -----------------------------
       Ψs ++⁺ Γ ⊩s σ ； n ∶ [] ∷⁺ Δ
s-；′ {_} {σ} {n = n} Ψs ⊩σ ⊩ΨsΓ refl = record
  { ⊩Γ   = ⊩ΨsΓ
  ; ⊩Γ′  = ⊩κ ⊩σ.⊩Γ′
  ; krip = helper
  }
  where module ⊩σ = _⊩s_∶_ ⊩σ
        ⊢ΨsΓ = ⊩⇒⊢ ⊩ΨsΓ
        ⊢σ   = ⊩s⇒⊢s ⊩σ
        helper : Δ′ ⊢s τ ∶ ⊩ΨsΓ ® ρ → GluSubsts Δ′ (σ ； n) (⊩κ ⊩σ.⊩Γ′) τ ρ
        helper {_} {τ} {ρ} τ∼ρ
          with ∥-s®′ Ψs ⊩ΨsΓ τ∼ρ
        ...  | Ψs′ , Δ″ , refl , eql , ⊩Γ₁ , τ∼ρ∥ = record
          { ⟦τ⟧    = ext ⟦τ⟧ (O ρ n)
          ; ↘⟦τ⟧   = ⟦；⟧ ↘⟦τ⟧
          ; τσ∼⟦τ⟧ = record
            { ⊢σ   = s-∘ ⊢τ (s-； Ψs ⊢σ (⊩⇒⊢ ⊩ΨsΓ) refl)
            ; Ψs⁻  = Ψs′
            ; Γ∥   = Δ″
            ; σ∥   = σ ∘ τ ∥ n
            ; Γ≡   = refl
            ; ≈σ∥  = subst (λ x → _ ⊢s σ ∘ τ ∥ x ≈ _ ∘ τ ∥ n ∶ _) (sym (+-identityʳ n)) (s-≈-refl (s-∘ ⊢τ∥ ⊢σ))
            ; O≡   = trans (cong (O τ) (+-identityʳ n)) (s®-resp-O n ⊩ΨsΓ τ∼ρ (length-<-++⁺ Ψs))
            ; len≡ = trans eql (sym (cong (O τ) (+-identityʳ n)))
            ; step = τσ∼⟦τ⟧
            }
          }
          where open GluSubsts (⊩σ.krip (s®-irrel ⊩Γ₁ ⊩σ.⊩Γ τ∼ρ∥))
                ⊢τ  = s®⇒⊢s ⊩ΨsΓ τ∼ρ
                ⊢τ∥ = s®⇒⊢s ⊩Γ₁ τ∼ρ∥


s-conv′ : Γ ⊩s σ ∶ Δ →
          ⊢ Δ ≈ Δ′ →
          -------------
          Γ ⊩s σ ∶ Δ′
s-conv′ {_} {σ} ⊩σ Δ≈Δ′ = record
  { ⊩Γ   = ⊩σ.⊩Γ
  ; ⊩Γ′  = ⊩Δ′
  ; krip = helper
  }
  where module ⊩σ = _⊩s_∶_ ⊩σ
        ⊩Δ′ = ⊩-resp-≈ ⊩σ.⊩Γ′ Δ≈Δ′
        helper : Δ″ ⊢s τ ∶ ⊩σ.⊩Γ ® ρ → GluSubsts Δ″ σ ⊩Δ′ τ ρ
        helper {_} {τ} τ∼ρ = record
          { ⟦τ⟧    = ⟦τ⟧
          ; ↘⟦τ⟧   = ↘⟦τ⟧
          ; τσ∼⟦τ⟧ = s®-resp-≈′ ⊩σ.⊩Γ′ ⊩Δ′ τσ∼⟦τ⟧ Δ≈Δ′
          }
          where open GluSubsts (⊩σ.krip τ∼ρ)
