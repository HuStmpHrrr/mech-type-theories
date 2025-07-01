{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Semantic judgments for contexts
module NonCumulative.Ascribed.Soundness.Contexts (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂) where

open import Lib
open import Data.Nat.Properties as ℕₚ

open import NonCumulative.Ascribed.Statics.Properties as Sta
open import NonCumulative.Ascribed.Semantics.Properties.PER fext
open import NonCumulative.Ascribed.Soundness.LogRel
open import NonCumulative.Ascribed.Soundness.ToSyntax fext
open import NonCumulative.Ascribed.Soundness.Properties.LogRel fext


⊢[]′ : ⊩ []
⊢[]′ = ⊩[]

⊢∷′-helper : ∀ {i}
             (⊩T : Γ ⊩ T ∶[ 1 + i ] Se i) →
             Δ ⊢s σ ∶ _⊩_∶[_]_.⊩Γ ⊩T ® ρ →
             GluTyp i Δ T σ ρ
⊢∷′-helper {i = i} record { krip = krip } σ∼ρ
  with krip σ∼ρ
...  | record { ⟦t⟧ = ⟦T⟧ ; ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦T⟧ ; T∈𝕌 = U eq _ ; t∼⟦t⟧ = T∼⟦T⟧ }
     rewrite 𝕌-wf-gen _ (λ l<j → <-trans l<j (≤-reflexive (sym eq)))
          |  Glu-wellfounded-≡ (≤-reflexive (sym eq)) = record
     { ⟦T⟧   = ⟦T⟧
     ; ↘⟦T⟧  = ↘⟦T⟧
     ; T∈𝕌   = A∈𝕌
     ; T∼⟦T⟧ = rel
     }
  where open GluU T∼⟦T⟧


⊢∷′ : ∀ {i} →
      Γ ⊩ T ∶[ 1 + i ] Se i →
      --------------
      ⊩ (T ↙ i) ∷ Γ
⊢∷′ {_} {T} ⊩T = ⊩∷ ⊩Γ (⊩⇒⊢-tm ⊩T) (⊢∷′-helper ⊩T)
  where open _⊩_∶[_]_ ⊩T