{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Semantic judgments for universes
module NonCumulative.Completeness.Universe (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Data.Nat.Properties

open import Lib
open import NonCumulative.Completeness.LogRel

open import NonCumulative.Semantics.Properties.PER fext


Se-≈′ : ∀ i →
        ⊨ Γ →
        ----------------------------------
        Γ ⊨ Se i ≈ Se i ∶[ 2 + i ] Se (1 + i)
Se-≈′ i ⊨Γ = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 ------------------------------------------------------------
                 Σ (RelTyp _ (Se (1 + i)) ρ (Se (1 + i)) ρ′)
                 λ rel → RelExp (Se i) ρ (Se i) ρ′ (El _ (RelTyp.T≈T′ rel))
        helper ρ≈ρ′ = record
          { ↘⟦T⟧  = ⟦Se⟧ _
          ; ↘⟦T′⟧ = ⟦Se⟧ _
          ; T≈T′  = U′
          }
          , record
          { ↘⟦t⟧  = ⟦Se⟧ _
          ; ↘⟦t′⟧ = ⟦Se⟧ _
          ; t≈t′  = U′
          }

Se-[]′ : ∀ i →
         Γ ⊨s σ ∶ Δ →
         ----------------------------------
         Γ ⊨ Se i [ σ ] ≈ Se i ∶[ 2 + i ] Se (1 + i)
Se-[]′ {_} {σ} i (⊨Γ , ⊨Δ , ⊨σ) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 -----------------------------------------------------------------
                 Σ (RelTyp _ (Se (1 + i)) ρ (Se (1 + i)) ρ′)
                 λ rel → RelExp (Se i [ σ ]) ρ (Se i) ρ′ (El _ (RelTyp.T≈T′ rel))
        helper ρ≈ρ′ = record
          { ↘⟦T⟧   = ⟦Se⟧ _
          ; ↘⟦T′⟧ = ⟦Se⟧ _
          ; T≈T′  = U′
          }
          , record
          { ↘⟦t⟧   = ⟦[]⟧ ↘⟦σ⟧ (⟦Se⟧ _)
          ; ↘⟦t′⟧ = ⟦Se⟧ _
          ; t≈t′  = U′
          }
          where open RelSubst (⊨σ ρ≈ρ′)
