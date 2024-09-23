{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Going from the gluing model to the syntax
module NonCumulative.Soundness.ToSyntax (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂) where

open import Lib

open import NonCumulative.Statics.Ascribed.Properties as Sta
open import NonCumulative.Semantics.Properties.PER fext
open import NonCumulative.Completeness.Fundamental fext
open import NonCumulative.Soundness.LogRel
open import NonCumulative.Soundness.Properties.LogRel fext
open import NonCumulative.Soundness.Properties.Substitutions fext


⊩⇒⊢-both : ∀ {i} → (⊩t : Γ ⊩ t ∶[ i ] T) →
           ----------------------
           Γ ⊢ T ∶[ 1 + i ] Se i × Γ ⊢ t ∶[ i ] T
⊩⇒⊢-both ⊩t
  with InitEnvs-related (fundamental-⊢Γ (⊩⇒⊢ (_⊩_∶[_]_.⊩Γ ⊩t)))
...  | _ , _ , ρ∈ , _ = ⊢T , conv ([I]-inv (®El⇒tm T∈𝕌 t∼⟦t⟧)) ([I] ⊢T)
                        where open _⊩_∶[_]_ ⊩t
                              open GluExp (krip (InitEnvs⇒s®I ⊩Γ ρ∈))
                              ⊢T = [I]-inv (®El⇒ty T∈𝕌 t∼⟦t⟧)

⊩⇒⊢-tm : ∀ { i } →
         Γ ⊩ t ∶[ i ] T →
         ------------
         Γ ⊢ t ∶[ i ] T
⊩⇒⊢-tm ⊩t = proj₂ (⊩⇒⊢-both ⊩t)

⊩⇒⊢-ty : ∀ { i } →
        (⊩t : Γ ⊩ t ∶[ i ] T) →
         ------------
         Γ ⊢ T ∶[ 1 + i ] Se i
⊩⇒⊢-ty ⊩t = proj₁ (⊩⇒⊢-both ⊩t)

⊩s⇒⊢s : Γ ⊩s σ ∶ Δ →
        ------------
        Γ ⊢s σ ∶ Δ
⊩s⇒⊢s ⊩σ
  with InitEnvs-related (fundamental-⊢Γ (⊩⇒⊢ (_⊩s_∶_.⊩Γ ⊩σ)))
...  | _ , _ , ρ∈ , _ = ∘I-inv′ (s®⇒⊢s ⊩Γ′ τσ∼⟦τ⟧)
  where open _⊩s_∶_ ⊩σ
        open GluSubst (krip (InitEnvs⇒s®I ⊩Γ ρ∈))