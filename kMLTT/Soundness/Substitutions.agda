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

s-,′ : ∀ {i} →
       Γ ⊩s σ ∶ Δ →
       Δ ⊩ T ∶ Se i →
       Γ ⊩ t ∶ T [ σ ] →
       -------------------
       Γ ⊩s σ , t ∶ T ∺ Δ
s-,′ {_} {σ} {_} {T} {t} {i} (⊢Γ , ⊢Δ , gσ) ⊩T@(⊢Δ₁ , j , gT) (⊢Γ₁ , k , gt) = ⊢Γ , ⊢∺ ⊢Δ ⊢T , helper
  where ⊢σ = {!!}
        ⊢T = {!!}
        ⊢t = {!!}
        helper : Δ′ ⊢s τ ∶ ⊢Γ ® ρ → GluSubsts Δ′ (σ , t) (⊢∺ ⊢Δ ⊢T) τ ρ
        helper {_} {τ} {ρ} τ∼ρ
          with gσ τ∼ρ
             | gt (s®-irrel ⊢Γ ⊢Γ₁ τ∼ρ)
        ...  | στ
             | record { ⟦T⟧ = ⟦T⟧ ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ⟦[]⟧ ↘ρ′ ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ }
            rewrite ⟦⟧s-det ↘ρ′ (GluSubsts.↘⟦τ⟧ στ) = record
              { ⟦τ⟧    = σ.⟦τ⟧ ↦ ⟦t⟧
              ; ↘⟦τ⟧   = ⟦,⟧ σ.↘⟦τ⟧ ↘⟦t⟧
              ; τσ∼⟦τ⟧ = record
                { ⊢σ   = s-∘ ⊢τ′ ⊢σ,t
                ; pσ   = σ ∘ τ
                ; v0σ  = t [ τ ]
                ; ⟦T⟧  = ⟦T⟧
                ; lvl  = max i k
                ; ⊢T   = ⊢T′
                ; ≈pσ  = s-≈-trans (p-∘ ⊢σ,t ⊢τ′) (∘-cong (s-≈-refl ⊢τ′) (p-, ⊢σ ⊢T ⊢t))
                ; ≈v0σ = let open ER
                         in ≈-conv (begin
                                     v 0 [ (σ , t) ∘ τ ] ≈⟨ ≈-conv ([∘] ⊢τ′ ⊢σ,t (vlookup (⊢∺ ⊢Δ ⊢T) here))
                                                                   eq ⟩
                                     v 0 [ σ , t ] [ τ ] ≈⟨ []-cong ([,]-v-ze ⊢σ ⊢T ⊢t) (s-≈-refl ⊢τ′) ⟩
                                     t [ τ ]             ∎)
                                   ([∘]-Se ⊢T ⊢σ ⊢τ′)
                ; ↘⟦T⟧ = subst (⟦ _ ⟧_↘ _) drop≡ ↘⟦T⟧
                ; T∈𝕌  = T∈𝕌′
                ; t∼ρ0 = ®El-resp-T≈ T∈𝕌′ (®El-cumu T∈𝕌 t∼⟦t⟧ (m≤n⊔m i k)) ([∘]-Se ⊢T′ ⊢σ ⊢τ′)
                ; step = subst (_ ⊢s _ ∘ _ ∶ _ ®_) drop≡ σ.τσ∼⟦τ⟧
                }
              }
          where module σ = GluSubsts στ
                ⊢τ′   = s®⇒⊢s ⊢Γ τ∼ρ
                ⊢σ,t  = s-, ⊢σ ⊢T ⊢t
                drop≡ = sym (drop-↦ σ.⟦τ⟧ ⟦t⟧)
                ⊢T′   = lift-⊢-Se ⊢T (m≤m⊔n i k)
                T∈𝕌′  = 𝕌-cumu (m≤n⊔m i k) T∈𝕌
                eq    = begin
                  T [ wk ] [ (σ , t) ∘ τ ] ≈⟨ [∘]-Se ⊢T (s-wk (⊢∺ ⊢Δ ⊢T)) (s-∘ ⊢τ′ ⊢σ,t) ⟩
                  T [ p ((σ , t) ∘ τ) ] ≈⟨ []-cong-Se″ ⊢T (p-∘ ⊢σ,t ⊢τ′) ⟩
                  T [ p (σ , t) ∘ τ ] ≈⟨ []-cong-Se″ ⊢T (∘-cong (s-≈-refl ⊢τ′) (p-, ⊢σ ⊢T ⊢t)) ⟩
                  T [ σ ∘ τ ] ≈˘⟨ [∘]-Se ⊢T ⊢σ ⊢τ′ ⟩
                  T [ σ ] [ τ ] ∎
                  where open ER

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
