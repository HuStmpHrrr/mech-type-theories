{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Completeness.Universe (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Data.Nat.Properties

open import Lib
open import kMLTT.Completeness.LogRel

open import kMLTT.Semantics.Properties.PER fext


Se-[]′ : ∀ i →
         Γ ⊨s σ ∶ Δ →
         ----------------------------------
         Γ ⊨ Se i [ σ ] ≈ Se i ∶ Se (1 + i)
Se-[]′ {_} {σ} i (⊨Γ , ⊨Δ , ⊨σ) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp (Se (suc i)) ρ (Se (suc i)) ρ′) (λ rel → RelExp (Se i [ σ ]) ρ (Se i) ρ′ (El∞ (RelTyp.T≈T′ rel)))
        helper ρ≈ρ′ = record
          { ⟦T⟧   = U (suc i)
          ; ⟦T′⟧  = U (suc i)
          ; ↘⟦T⟧  = ⟦Se⟧ _
          ; ↘⟦T′⟧ = ⟦Se⟧ _
          ; T≈T′  = suc (suc i) , U′ ≤-refl
          }
          , record
          { ⟦t⟧   = U i
          ; ⟦t′⟧  = U i
          ; ↘⟦t⟧  = ⟦[]⟧ ↘⟦σ⟧ (⟦Se⟧ _)
          ; ↘⟦t′⟧ = ⟦Se⟧ _
          ; t≈t′  = PERDef.U ≤-refl refl
          }
          where open RelSubsts (⊨σ ρ≈ρ′)


≈-cumu′ : ∀ {i} →
          Γ ⊨ T ≈ T′ ∶ Se i →
          -----------------------
          Γ ⊨ T ≈ T′ ∶ Se (1 + i)
≈-cumu′ {_} {T} {T′} {i} (⊨Γ , T≈T′) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp (Se (suc i)) ρ (Se (suc i)) ρ′) (λ rel → RelExp T ρ T′ ρ′ (El∞ (RelTyp.T≈T′ rel)))
        helper {ρ} {ρ′} ρ≈ρ′
          with T≈T′ ρ≈ρ′
        ...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = _ , U i<j _ }
             , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
             rewrite 𝕌-wellfounded-≡-𝕌 _ i<j = record
          { ⟦T⟧   = U (1 + i)
          ; ⟦T′⟧  = U (1 + i)
          ; ↘⟦T⟧  = ⟦Se⟧ _
          ; ↘⟦T′⟧ = ⟦Se⟧ _
          ; T≈T′  = suc (1 + i) , U′ ≤-refl
          }
          , rel
          where rel : RelExp T ρ T′ ρ′ (El (suc (suc i)) (U′ ≤-refl))
                rel
                  rewrite 𝕌-wellfounded-≡-𝕌 (suc (suc i)) ≤-refl = record
                  { ⟦t⟧   = ⟦t⟧
                  ; ⟦t′⟧  = ⟦t′⟧
                  ; ↘⟦t⟧  = ↘⟦t⟧
                  ; ↘⟦t′⟧ = ↘⟦t′⟧
                  ; t≈t′  = 𝕌-cumu-step _ t≈t′
                  }
