{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Soundness.Contexts (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib

open import kMLTT.Statics.Properties as Sta
open import kMLTT.Soundness.LogRel
open import kMLTT.Soundness.ToSyntax fext
open import kMLTT.Soundness.Properties.LogRel fext


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
⊢∺′ {_} {T} ⊩T = ⊩∺ ⊩Γ (⊩⇒⊢-tm ⊩T) helper
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
