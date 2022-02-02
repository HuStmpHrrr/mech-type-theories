{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Soundness.Substitutions (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib

open import kMLTT.Soundness.LogRel
open import kMLTT.Soundness.Properties.Substitutions fext


s-I′ : ⊢ Γ →
       ------------
       Γ ⊩s I ∶ Γ
s-I′ ⊢Γ = ⊢Γ , ⊢Γ , helper
  where helper : Δ ⊢s σ ∶ ⊢Γ ® ρ → GluSubsts Δ I ⊢Γ σ ρ
        helper {ρ = ρ} σ∼ρ = record
          { ⟦τ⟧    = ρ
          ; ↘⟦τ⟧   = ⟦I⟧
          ; τσ∼⟦τ⟧ = s®-resp-s≈ ⊢Γ σ∼ρ (s-≈-sym (I-∘ {!!}))
          }

s-wk′ : ⊢ T ∺ Γ →
        ------------------
        T ∺ Γ ⊩s wk ∶ Γ
s-wk′ ⊢TΓ@(⊢∺ ⊢Γ ⊢T) = ⊢TΓ , ⊢Γ , helper
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
s-∘′ {_} {τ} {_} {σ} ⊩τ@(⊢Γ , ⊢Γ′ , gτ) ⊩σ@(⊢Γ′₁ , ⊢Γ″ , gσ) = ⊢Γ , ⊢Γ″ , helper
  where helper : Δ ⊢s σ′ ∶ ⊢Γ ® ρ → GluSubsts Δ (σ ∘ τ) ⊢Γ″ σ′ ρ
        helper {_} {σ′} {ρ} σ′∼ρ = record
          { ⟦τ⟧    = σ.⟦τ⟧
          ; ↘⟦τ⟧   = ⟦∘⟧ τ.↘⟦τ⟧ σ.↘⟦τ⟧
          ; τσ∼⟦τ⟧ = s®-resp-s≈ ⊢Γ″ σ.τσ∼⟦τ⟧ (s-≈-sym (∘-assoc {!!} {!!} (s®⇒⊢s ⊢Γ σ′∼ρ)))
          }
          where module τ = GluSubsts (gτ σ′∼ρ)
                module σ = GluSubsts (gσ (s®-irrel ⊢Γ′ ⊢Γ′₁ τ.τσ∼⟦τ⟧))

-- s-,    : ∀ {i} →
--          Γ ⊢s σ ∶ Δ →
--          Δ ⊢ T ∶ Se i →
--          Γ ⊢ t ∶ T [ σ ] →
--          -------------------
--          Γ ⊢s σ , t ∶ T ∺ Δ
-- s-；    : ∀ {n} Ψs →
--          Γ ⊢s σ ∶ Δ →
--          ⊢ Ψs ++⁺ Γ →
--          len Ψs ≡ n →
--          -----------------------------
--          Ψs ++⁺ Γ ⊢s σ ； n ∶ [] ∷⁺ Δ
-- s-conv : Γ ⊢s σ ∶ Δ →
--          ⊢ Δ ≈ Δ′ →
--          -------------
--          Γ ⊢s σ ∶ Δ′
