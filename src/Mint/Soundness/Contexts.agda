{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

-- Semantic judgments for context stacks
module Mint.Soundness.Contexts (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib

open import Mint.Statics.Properties as Sta
open import Mint.Soundness.LogRel
open import Mint.Soundness.ToSyntax fext
open import Mint.Soundness.Properties.LogRel fext


⊢[]′ : ⊩ [] ∷ []
⊢[]′ = ⊩[]

⊢κ′ : ⊩ Γ →
      ----------
      ⊩ [] ∷⁺ Γ
⊢κ′ = ⊩κ

⊢∺′-helper : ∀ {i}
             (⊩T : Γ ⊩ T ∶ Se i) →
             Δ ⊢s σ ∶ _⊩_∶_.⊩Γ ⊩T ® ρ →
             GluTyp i Δ T σ ρ
⊢∺′-helper record { krip = krip } σ∼ρ
  with krip σ∼ρ
...  | record { ⟦t⟧ = ⟦T⟧ ; ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦T⟧ ; T∈𝕌 = U i<l _ ; t∼⟦t⟧ = T∼⟦T⟧ }
     rewrite Glu-wellfounded-≡ i<l = record
     { ⟦T⟧   = ⟦T⟧
     ; ↘⟦T⟧  = ↘⟦T⟧
     ; T∈𝕌   = A∈𝕌
     ; T∼⟦T⟧ = rel
     }
  where open GluU T∼⟦T⟧


⊢∺′ : ∀ {i} →
      Γ ⊩ T ∶ Se i →
      --------------
      ⊩ T ∺ Γ
⊢∺′ {_} {T} ⊩T = ⊩∺ ⊩Γ (⊩⇒⊢-tm ⊩T) (⊢∺′-helper ⊩T)
  where open _⊩_∶_ ⊩T
