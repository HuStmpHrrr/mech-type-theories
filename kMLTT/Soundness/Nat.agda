{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Soundness.Nat (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Data.Nat.Properties

open import kMLTT.Statics.Properties
open import kMLTT.Soundness.LogRel
open import kMLTT.Soundness.Properties.LogRel fext
open import kMLTT.Soundness.Properties.Substitutions fext


N-wf′ : ∀ i →
        ⊢ Γ →
        -------------
        Γ ⊩ N ∶ Se i
N-wf′ i ⊢Γ = record
  { t∶T  = N-wf i ⊢Γ
  ; ⊢Γ   = ⊢Γ
  ; lvl  = 1 + i
  ; krip = helper
  }
  where helper : Δ ⊢s σ ∶ ⊢Γ ® ρ → GluExp (1 + i) Δ N (Se i) σ ρ
        helper σ∼ρ = record
          { ⟦T⟧   = U i
          ; ⟦t⟧   = N
          ; ↘⟦T⟧  = ⟦Se⟧ i
          ; ↘⟦t⟧  = ⟦N⟧
          ; T∈𝕌   = U′ ≤-refl
          ; t∼⟦t⟧ = record
            { t∶T = t[σ] (N-wf i ⊢Γ) ⊢σ
            ; T≈  = Se-[] i ⊢σ
            ; A∈𝕌 = N
            ; rel = N-[] i ⊢σ
            }
          }
          where ⊢σ = s®⇒⊢s ⊢Γ σ∼ρ


ze-I′ : ⊢ Γ →
        -----------
        Γ ⊩ ze ∶ N
ze-I′ ⊢Γ = record
  { t∶T  = ze-I ⊢Γ
  ; ⊢Γ   = ⊢Γ
  ; lvl  = 0
  ; krip = helper
  }
  where helper : Δ ⊢s σ ∶ ⊢Γ ® ρ → GluExp 0 Δ ze N σ ρ
        helper σ∼ρ = record
          { ⟦T⟧   = N
          ; ⟦t⟧   = ze
          ; ↘⟦T⟧  = ⟦N⟧
          ; ↘⟦t⟧  = ⟦ze⟧
          ; T∈𝕌   = N
          ; t∼⟦t⟧ = ze (ze-[] ⊢σ) , N-[] 0 ⊢σ
          }
          where ⊢σ = s®⇒⊢s ⊢Γ σ∼ρ


su-I′ : Γ ⊩ t ∶ N →
        -------------
        Γ ⊩ su t ∶ N
su-I′ {_} {t} ⊩t = record
  { t∶T  = su-I t∶T
  ; ⊢Γ   = ⊢Γ
  ; lvl  = lvl
  ; krip = helper
  }
  where open _⊩_∶_ ⊩t
        helper : Δ ⊢s σ ∶ ⊢Γ ® ρ → GluExp lvl Δ (su t) N σ ρ
        helper σ∼ρ
          with krip σ∼ρ
        ... | record { ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ⟦N⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = N ; t∼⟦t⟧ = t∼⟦t⟧ , _ }
          = record
          { ⟦T⟧   = N
          ; ⟦t⟧   = su ⟦t⟧
          ; ↘⟦T⟧  = ⟦N⟧
          ; ↘⟦t⟧  = ⟦su⟧ ↘⟦t⟧
          ; T∈𝕌   = N
          ; t∼⟦t⟧ = su (su-[] ⊢σ t∶T) t∼⟦t⟧ , N-[] lvl ⊢σ
          }
          where ⊢σ = s®⇒⊢s ⊢Γ σ∼ρ


-- N-E     : ∀ {i} →
--           N ∺ Γ ⊢ T ∶ Se i →
--           Γ ⊢ s ∶ T [| ze ] →
--           T ∺ N ∺ Γ ⊢ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
--           Γ ⊢ t ∶ N →
--           --------------------------
--           Γ ⊢ rec T s r t ∶ T [| t ]
