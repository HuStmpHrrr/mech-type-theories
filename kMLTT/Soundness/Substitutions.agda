{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Soundness.Substitutions (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Data.Nat.Properties

open import kMLTT.Statics.Properties
open import kMLTT.Semantics.Properties.Domain fext
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Soundness.LogRel
open import kMLTT.Soundness.Properties.LogRel fext
open import kMLTT.Soundness.Properties.Substitutions fext
open import kMLTT.Soundness.Cumulativity fext


s-I′ : ⊢ Γ →
       ------------
       Γ ⊩s I ∶ Γ
s-I′ ⊢Γ = record
  { ⊢τ   = s-I ⊢Γ
  ; ⊢Γ   = ⊢Γ
  ; ⊢Γ′  = ⊢Γ
  ; krip = helper
  }
  where helper : Δ ⊢s σ ∶ ⊢Γ ® ρ → GluSubsts Δ I ⊢Γ σ ρ
        helper {ρ = ρ} σ∼ρ = record
          { ⟦τ⟧    = ρ
          ; ↘⟦τ⟧   = ⟦I⟧
          ; τσ∼⟦τ⟧ = s®-resp-s≈ ⊢Γ σ∼ρ (s-≈-sym (I-∘ (s®⇒⊢s ⊢Γ σ∼ρ)))
          }

s-wk′ : ⊢ T ∺ Γ →
        ------------------
        T ∺ Γ ⊩s wk ∶ Γ
s-wk′ ⊢TΓ@(⊢∺ ⊢Γ ⊢T) = record
  { ⊢τ   = s-wk ⊢TΓ
  ; ⊢Γ   = ⊢TΓ
  ; ⊢Γ′  = ⊢Γ
  ; krip = helper
  }
  where helper : Δ ⊢s σ ∶ ⊢∺ ⊢Γ ⊢T ® ρ → GluSubsts Δ wk ⊢Γ σ ρ
        helper {ρ = ρ} σ∼ρ = record
          { ⟦τ⟧    = drop ρ
          ; ↘⟦τ⟧   = ⟦wk⟧
          ; τσ∼⟦τ⟧ = s®-resp-s≈ ⊢Γ step (s-≈-sym ≈pσ)
          }
          where open Glu∺ σ∼ρ

s-∘′ : Γ ⊩s τ ∶ Γ′ →
       Γ′ ⊩s σ ∶ Γ″ →
       ----------------
       Γ ⊩s σ ∘ τ ∶ Γ″
s-∘′ {_} {τ} {_} {σ} ⊩τ ⊩σ = record
  { ⊢τ   = s-∘ ⊩τ.⊢τ ⊩σ.⊢τ
  ; ⊢Γ   = ⊩τ.⊢Γ
  ; ⊢Γ′  = ⊩σ.⊢Γ′
  ; krip = helper
  }
  where module ⊩τ = _⊩s_∶_ ⊩τ
        module ⊩σ = _⊩s_∶_ ⊩σ
        helper : Δ ⊢s σ′ ∶ ⊩τ.⊢Γ ® ρ → GluSubsts Δ (σ ∘ τ) ⊩σ.⊢Γ′ σ′ ρ
        helper {_} {σ′} {ρ} σ′∼ρ = record
          { ⟦τ⟧    = σ.⟦τ⟧
          ; ↘⟦τ⟧   = ⟦∘⟧ τ.↘⟦τ⟧ σ.↘⟦τ⟧
          ; τσ∼⟦τ⟧ = s®-resp-s≈ ⊩σ.⊢Γ′ σ.τσ∼⟦τ⟧ (s-≈-sym (∘-assoc ⊩σ.⊢τ ⊩τ.⊢τ (s®⇒⊢s ⊩τ.⊢Γ σ′∼ρ)))
          }
          where module τ = GluSubsts (⊩τ.krip σ′∼ρ)
                module σ = GluSubsts (⊩σ.krip (s®-irrel ⊩τ.⊢Γ′ ⊩σ.⊢Γ τ.τσ∼⟦τ⟧))

s-,′ : ∀ {i} →
       Γ ⊩s σ ∶ Δ →
       Δ ⊢ T ∶ Se i →
       Γ ⊩ t ∶ T [ σ ] →
       -------------------
       Γ ⊩s σ , t ∶ T ∺ Δ
s-,′ {_} {σ} {_} {T} {t} {i} ⊩σ ⊢T ⊩t = record
  { ⊢τ   = s-, ⊢σ ⊢T ⊢t
  ; ⊢Γ   = ⊩σ.⊢Γ
  ; ⊢Γ′  = ⊢∺ ⊩σ.⊢Γ′ ⊢T
  ; krip = helper
  }
  where module ⊩σ = _⊩s_∶_ ⊩σ
        module ⊩t = _⊩_∶_ ⊩t
        ⊢σ = ⊩σ.⊢τ
        ⊢t = ⊩t.t∶T
        helper : Δ′ ⊢s τ ∶ ⊩σ.⊢Γ ® ρ → GluSubsts Δ′ (σ , t) (⊢∺ ⊩σ.⊢Γ′ ⊢T) τ ρ
        helper {_} {τ} {ρ} τ∼ρ
          with ⊩σ.krip τ∼ρ
             | ⊩t.krip (s®-irrel ⊩σ.⊢Γ ⊩t.⊢Γ τ∼ρ)
        ...  | στ
             | record { ⟦T⟧ = ⟦T⟧ ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ⟦[]⟧ ↘ρ′ ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ }
            rewrite ⟦⟧s-det ↘ρ′ (GluSubsts.↘⟦τ⟧ στ) = record
              { ⟦τ⟧    = σ.⟦τ⟧ ↦ ⟦t⟧
              ; ↘⟦τ⟧   = ⟦,⟧ σ.↘⟦τ⟧ ↘⟦t⟧
              ; τσ∼⟦τ⟧ = record
                { ⊢σ   = s-∘ ⊢τ ⊢σ,t
                ; pσ   = σ ∘ τ
                ; v0σ  = t [ τ ]
                ; ⟦T⟧  = ⟦T⟧
                ; lvl  = max i ⊩t.lvl
                ; ⊢T   = ⊢T′
                ; ≈pσ  = s-≈-trans (p-∘ ⊢σ,t ⊢τ) (∘-cong (s-≈-refl ⊢τ) (p-, ⊢σ ⊢T ⊢t))
                ; ≈v0σ = let open ER
                         in ≈-conv (begin
                                     v 0 [ (σ , t) ∘ τ ] ≈⟨ ≈-conv ([∘] ⊢τ ⊢σ,t (vlookup (⊢∺ ⊩σ.⊢Γ′ ⊢T) here))
                                                                   eq ⟩
                                     v 0 [ σ , t ] [ τ ] ≈⟨ []-cong ([,]-v-ze ⊢σ ⊢T ⊢t) (s-≈-refl ⊢τ) ⟩
                                     t [ τ ]             ∎)
                                   ([∘]-Se ⊢T ⊢σ ⊢τ)
                ; ↘⟦T⟧ = subst (⟦ _ ⟧_↘ _) drop≡ ↘⟦T⟧
                ; T∈𝕌  = T∈𝕌′
                ; t∼ρ0 = ®El-resp-T≈ T∈𝕌′ (®El-cumu T∈𝕌 t∼⟦t⟧ (m≤n⊔m i ⊩t.lvl)) ([∘]-Se ⊢T′ ⊢σ ⊢τ)
                ; step = subst (_ ⊢s _ ∘ _ ∶ _ ®_) drop≡ σ.τσ∼⟦τ⟧
                }
              }
          where module σ = GluSubsts στ
                ⊢τ    = s®⇒⊢s ⊩σ.⊢Γ τ∼ρ
                ⊢σ,t  = s-, ⊢σ ⊢T ⊢t
                drop≡ = sym (drop-↦ σ.⟦τ⟧ ⟦t⟧)
                ⊢T′   = lift-⊢-Se ⊢T (m≤m⊔n i ⊩t.lvl)
                T∈𝕌′  = 𝕌-cumu (m≤n⊔m i ⊩t.lvl) T∈𝕌
                eq    = begin
                  T [ wk ] [ (σ , t) ∘ τ ] ≈⟨ [∘]-Se ⊢T (s-wk (⊢∺ ⊩σ.⊢Γ′ ⊢T)) (s-∘ ⊢τ ⊢σ,t) ⟩
                  T [ p ((σ , t) ∘ τ) ]    ≈⟨ []-cong-Se″ ⊢T (p-∘ ⊢σ,t ⊢τ) ⟩
                  T [ p (σ , t) ∘ τ ]      ≈⟨ []-cong-Se″ ⊢T (∘-cong (s-≈-refl ⊢τ) (p-, ⊢σ ⊢T ⊢t)) ⟩
                  T [ σ ∘ τ ]              ≈˘⟨ [∘]-Se ⊢T ⊢σ ⊢τ ⟩
                  T [ σ ] [ τ ]            ∎
                  where open ER

s-；′ : ∀ {n} Ψs →
       Γ ⊩s σ ∶ Δ →
       ⊢ Ψs ++⁺ Γ →
       len Ψs ≡ n →
       -----------------------------
       Ψs ++⁺ Γ ⊩s σ ； n ∶ [] ∷⁺ Δ
s-；′ {_} {σ} {n = n} Ψs ⊩σ ⊢ΨsΓ refl = record
  { ⊢τ   = s-； Ψs ⊢σ ⊢ΨsΓ refl
  ; ⊢Γ   = ⊢ΨsΓ
  ; ⊢Γ′  = ⊢κ ⊩σ.⊢Γ′
  ; krip = helper
  }
  where module ⊩σ = _⊩s_∶_ ⊩σ
        ⊢σ = ⊩σ.⊢τ
        helper : Δ′ ⊢s τ ∶ ⊢ΨsΓ ® ρ → GluSubsts Δ′ (σ ； n) (⊢κ ⊩σ.⊢Γ′) τ ρ
        helper {_} {τ} {ρ} τ∼ρ
          with ∥-s®′ Ψs ⊢ΨsΓ τ∼ρ
        ...  | Ψs′ , Δ″ , refl , eql , ⊢Γ₁ , τ∼ρ∥ = record
          { ⟦τ⟧    = ext ⟦τ⟧ (O ρ n)
          ; ↘⟦τ⟧   = ⟦；⟧ ↘⟦τ⟧
          ; τσ∼⟦τ⟧ = record
            { ⊢σ   = s-∘ ⊢τ (s-； Ψs ⊢σ ⊢ΨsΓ refl)
            ; Ψs⁻  = Ψs′
            ; Γ∥   = Δ″
            ; σ∥   = σ ∘ τ ∥ n
            ; Γ≡   = refl
            ; ≈σ∥  = subst (λ x → _ ⊢s σ ∘ τ ∥ x ≈ _ ∘ τ ∥ n ∶ _) (sym (+-identityʳ n)) (s-≈-refl (s-∘ ⊢τ∥ ⊢σ))
            ; O≡   = trans (cong (O τ) (+-identityʳ n)) (s®-resp-O n ⊢ΨsΓ τ∼ρ (length-<-++⁺ Ψs))
            ; len≡ = trans eql (sym (cong (O τ) (+-identityʳ n)))
            ; step = τσ∼⟦τ⟧
            }
          }
          where open GluSubsts (⊩σ.krip (s®-irrel ⊢Γ₁ ⊩σ.⊢Γ τ∼ρ∥))
                ⊢τ  = s®⇒⊢s ⊢ΨsΓ τ∼ρ
                ⊢τ∥ = s®⇒⊢s ⊢Γ₁ τ∼ρ∥


s-conv′ : Γ ⊩s σ ∶ Δ →
          ⊢ Δ ≈ Δ′ →
          -------------
          Γ ⊩s σ ∶ Δ′
s-conv′ {_} {σ} ⊩σ Δ≈Δ′
  with presup-⊢≈ Δ≈Δ′
...  | _ , ⊢Δ′ = record
  { ⊢τ   = s-conv ⊩σ.⊢τ Δ≈Δ′
  ; ⊢Γ   = ⊩σ.⊢Γ
  ; ⊢Γ′  = ⊢Δ′
  ; krip = helper
  }
  where module ⊩σ = _⊩s_∶_ ⊩σ
        helper : Δ″ ⊢s τ ∶ ⊩σ.⊢Γ ® ρ → GluSubsts Δ″ σ ⊢Δ′ τ ρ
        helper {_} {τ} τ∼ρ = record
          { ⟦τ⟧    = ⟦τ⟧
          ; ↘⟦τ⟧   = ↘⟦τ⟧
          ; τσ∼⟦τ⟧ = let ⊢Δ′₁ , στ∼ = s®-resp-≈ ⊩σ.⊢Γ′ τσ∼⟦τ⟧ Δ≈Δ′
                     in s®-irrel ⊢Δ′₁ ⊢Δ′ στ∼
          }
          where open GluSubsts (⊩σ.krip τ∼ρ)
