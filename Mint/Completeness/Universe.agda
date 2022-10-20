{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

-- Semantic judgments for universes
module Mint.Completeness.Universe (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Data.Nat.Properties

open import Lib
open import Mint.Completeness.LogRel

open import Mint.Semantics.Properties.PER fext


Se-≈′ : ∀ i →
        ⊨ Γ →
        ----------------------------------
        Γ ⊨ Se i ≈ Se i ∶ Se (1 + i)
Se-≈′ i ⊨Γ = ⊨Γ , _ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 ------------------------------------------------------------
                 Σ (RelTyp _ (Se (suc i)) ρ (Se (suc i)) ρ′)
                 λ rel → RelExp (Se i) ρ (Se i) ρ′ (El _ (RelTyp.T≈T′ rel))
        helper ρ≈ρ′ = record
          { ↘⟦T⟧  = ⟦Se⟧ _
          ; ↘⟦T′⟧ = ⟦Se⟧ _
          ; T≈T′  = U′ ≤-refl
          }
          , record
          { ↘⟦t⟧  = ⟦Se⟧ _
          ; ↘⟦t′⟧ = ⟦Se⟧ _
          ; t≈t′  = PERDef.U ≤-refl refl
          }

Se-[]′ : ∀ i →
         Γ ⊨s σ ∶ Δ →
         ----------------------------------
         Γ ⊨ Se i [ σ ] ≈ Se i ∶ Se (1 + i)
Se-[]′ {_} {σ} i (⊨Γ , ⊨Δ , ⊨σ) = ⊨Γ , _ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 -----------------------------------------------------------------
                 Σ (RelTyp _ (Se (suc i)) ρ (Se (suc i)) ρ′)
                 λ rel → RelExp (Se i [ σ ]) ρ (Se i) ρ′ (El _ (RelTyp.T≈T′ rel))
        helper ρ≈ρ′ = record
          { ↘⟦T⟧   = ⟦Se⟧ _
          ; ↘⟦T′⟧ = ⟦Se⟧ _
          ; T≈T′  = U′ ≤-refl
          }
          , record
          { ↘⟦t⟧   = ⟦[]⟧ ↘⟦σ⟧ (⟦Se⟧ _)
          ; ↘⟦t′⟧ = ⟦Se⟧ _
          ; t≈t′  = PERDef.U ≤-refl refl
          }
          where open RelSubsts (⊨σ ρ≈ρ′)


≈-cumu′ : ∀ {i} →
          Γ ⊨ T ≈ T′ ∶ Se i →
          -----------------------
          Γ ⊨ T ≈ T′ ∶ Se (1 + i)
≈-cumu′ {_} {T} {T′} {i} (⊨Γ , _ , T≈T′) = ⊨Γ , _ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 --------------------------------------------------
                 Σ (RelTyp _ (Se (suc i)) ρ (Se (suc i)) ρ′)
                 λ rel → RelExp T ρ T′ ρ′ (El _ (RelTyp.T≈T′ rel))
        helper {ρ} {ρ′} ρ≈ρ′
          with T≈T′ ρ≈ρ′
        ...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<j _ }
             , record { ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
             rewrite 𝕌-wellfounded-≡-𝕌 _ i<j = record
                                                { ↘⟦T⟧  = ⟦Se⟧ _
                                                ; ↘⟦T′⟧ = ⟦Se⟧ _
                                                ; T≈T′  = U′ ≤-refl
                                                }
                                              , rel
          where rel : RelExp T ρ T′ ρ′ (El (suc (suc i)) (U′ ≤-refl))
                rel
                  rewrite 𝕌-wellfounded-≡-𝕌 (suc (suc i)) ≤-refl = record
                                                                    { ↘⟦t⟧  = ↘⟦t⟧
                                                                    ; ↘⟦t′⟧ = ↘⟦t′⟧
                                                                    ; t≈t′  = 𝕌-cumu-step _ t≈t′
                                                                    }
