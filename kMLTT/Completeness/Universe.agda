{-# OPTIONS --without-K --safe #-}

open import Level using ()
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
Se-[]′ {_} {σ} i (⊨Γ , ⊨Δ , ⊨σ) = (⊨Γ , λ ρ≈ρ′ → record
                                                   { ⟦T⟧   = U (suc i)
                                                   ; ⟦T′⟧  = U (suc i)
                                                   ; ↘⟦T⟧  = ⟦Se⟧ _
                                                   ; ↘⟦T′⟧ = ⟦Se⟧ _
                                                   ; T≈T′  = suc (suc i) , U′ ≤-refl
                                                   ; nat   = λ κ → ⟦Se⟧ _
                                                   ; nat′  = λ κ → ⟦Se⟧ _
                                                   })
                                , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → RelExp (Se i [ σ ]) ρ (Se i) ρ′ (El∞ (suc (suc i) , U′ ≤-refl))
        helper ρ≈ρ′ = record
          { ⟦t⟧   = U i
          ; ⟦t′⟧  = U i
          ; ↘⟦t⟧  = ⟦[]⟧ ↘⟦σ⟧ (⟦Se⟧ _)
          ; ↘⟦t′⟧ = ⟦Se⟧ _
          ; t≈t′  = PERDef.U ≤-refl refl
          ; nat   = λ κ → ⟦[]⟧ (nat κ) (⟦Se⟧ _)
          ; nat′  = λ κ → ⟦Se⟧ _
          }
          where open RelSubsts (⊨σ ρ≈ρ′)


≈-cumu′ : ∀ {i} →
          Γ ⊨ T ≈ T′ ∶ Se i →
          -----------------------
          Γ ⊨ T ≈ T′ ∶ Se (1 + i)
≈-cumu′ {_} {T} {T′} {i} ((⊨Γ , ⊨Se) , T≈T′) = (⊨Γ , λ ρ≈ρ′ → record
                                                                { ⟦T⟧   = U (1 + _)
                                                                ; ⟦T′⟧  = U (1 + _)
                                                                ; ↘⟦T⟧  = ⟦Se⟧ _
                                                                ; ↘⟦T′⟧ = ⟦Se⟧ _
                                                                ; T≈T′  = suc (1 + _) , U′ ≤-refl
                                                                ; nat   = λ κ → ⟦Se⟧ _
                                                                ; nat′  = λ κ → ⟦Se⟧ _
                                                                })
                                             , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → RelExp T ρ T′ ρ′ (El∞ (suc (suc i) , U′ ≤-refl))
        helper ρ≈ρ′
          with ⊨Se ρ≈ρ′ | T≈T′ ρ≈ρ′
        ...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = _ , U i<j _ }
             | record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ ; nat = nat ; nat′ = nat′ }
             rewrite 𝕌-wellfounded-≡-𝕌 _ i<j
                   | 𝕌-wellfounded-≡-𝕌 (suc (suc i)) ≤-refl = record
          { ⟦t⟧   = ⟦t⟧
          ; ⟦t′⟧  = ⟦t′⟧
          ; ↘⟦t⟧  = ↘⟦t⟧
          ; ↘⟦t′⟧ = ↘⟦t′⟧
          ; t≈t′  = 𝕌-cumu-step _ t≈t′
          ; nat   = nat
          ; nat′  = nat′
          }
