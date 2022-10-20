{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

-- Going from the gluing model to the syntax
module Mint.Soundness.ToSyntax (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib

open import Mint.Statics.Properties as Sta
open import Mint.Semantics.Properties.PER fext
open import Mint.Completeness.Fundamental fext
open import Mint.Soundness.LogRel
open import Mint.Soundness.Properties.LogRel fext
open import Mint.Soundness.Properties.Substitutions fext


⊩⇒⊢-both : (⊩t : Γ ⊩ t ∶ T) →
           ----------------------
           Γ ⊢ T ∶ Se (_⊩_∶_.lvl ⊩t) × Γ ⊢ t ∶ T
⊩⇒⊢-both ⊩t
  with InitEnvs-related (fundamental-⊢Γ (⊩⇒⊢ (_⊩_∶_.⊩Γ ⊩t)))
...  | _ , _ , ρ∈ , _ = ⊢T , conv ([I]-inv (®El⇒tm T∈𝕌 t∼⟦t⟧)) ([I] ⊢T)
  where open _⊩_∶_ ⊩t
        open GluExp (krip (InitEnvs⇒s®I ⊩Γ ρ∈))
        ⊢T = [I]-inv (®El⇒ty T∈𝕌 t∼⟦t⟧)

⊩⇒⊢-tm : Γ ⊩ t ∶ T →
         ------------
         Γ ⊢ t ∶ T
⊩⇒⊢-tm ⊩t = proj₂ (⊩⇒⊢-both ⊩t)

⊩⇒⊢-ty : (⊩t : Γ ⊩ t ∶ T) →
         ------------
         Γ ⊢ T ∶ Se (_⊩_∶_.lvl ⊩t)
⊩⇒⊢-ty ⊩t = proj₁ (⊩⇒⊢-both ⊩t)

⊩s⇒⊢s : Γ ⊩s σ ∶ Δ →
        ------------
        Γ ⊢s σ ∶ Δ
⊩s⇒⊢s ⊩σ
  with InitEnvs-related (fundamental-⊢Γ (⊩⇒⊢ (_⊩s_∶_.⊩Γ ⊩σ)))
...  | _ , _ , ρ∈ , _ = ∘I-inv′ (s®⇒⊢s ⊩Γ′ τσ∼⟦τ⟧)
  where open _⊩s_∶_ ⊩σ
        open GluSubsts (krip (InitEnvs⇒s®I ⊩Γ ρ∈))
