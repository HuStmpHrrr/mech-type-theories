{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Soundness.Contexts (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
-- open import Data.Nat.Properties as ℕₚ
-- open import Data.List.Properties as Lₚ

open import kMLTT.Statics.Properties as Sta
-- open import kMLTT.Semantics.Properties.Domain fext
-- open import kMLTT.Semantics.Properties.Evaluation fext
-- open import kMLTT.Semantics.Properties.PER fext
-- open import kMLTT.Semantics.Readback
-- open import kMLTT.Completeness.LogRel
-- open import kMLTT.Completeness.Fundamental fext
open import kMLTT.Soundness.LogRel
-- open import kMLTT.Soundness.Cumulativity fext
open import kMLTT.Soundness.Properties.LogRel fext
-- open import kMLTT.Soundness.Properties.Mt fext
-- open import kMLTT.Soundness.Realizability fext


⊢[]′ : ⊩ [] ∷ []
⊢[]′ = ⊩[]

⊢κ′ : ⊩ Γ →
      ----------
      ⊩ [] ∷⁺ Γ
⊢κ′ = ⊩κ

⊢∺′ : ∀ {i} →
      Γ ⊩ T ∶ Se i →
      --------------
      ⊩ T ∺ Γ
⊢∺′ {_} {T} ⊩T = ⊩∺ ⊩Γ t∶T helper
  where open _⊩_∶_ ⊩T
        helper : Δ ⊢s σ ∶ ⊩Γ ® ρ → GluTyp _ Δ T σ ρ
        helper σ∼ρ
          with krip σ∼ρ
        ...  | record { ⟦t⟧ = ⟦T⟧ ; ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦T⟧ ; T∈𝕌 = U i<l _ ; t∼⟦t⟧ = T∼⟦T⟧ }
             rewrite Glu-wellfounded-≡ i<l = record
             { ⟦T⟧   = ⟦T⟧
             ; ↘⟦T⟧  = ↘⟦T⟧
             ; T∈𝕌   = A∈𝕌
             ; T∼⟦T⟧ = rel
             }
          where open GluU T∼⟦T⟧
