{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Soundness.ToSyntax (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib

open import kMLTT.Statics.Properties as Sta
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Completeness.Fundamental fext
open import kMLTT.Soundness.LogRel
open import kMLTT.Soundness.Properties.LogRel fext
open import kMLTT.Soundness.Properties.Substitutions fext


⊩⇒⊢-tm : Γ ⊩ t ∶ T →
         ------------
         Γ ⊢ t ∶ T
⊩⇒⊢-tm ⊩t
  with InitEnvs-related (fundamental-⊢Γ (⊩⇒⊢ (_⊩_∶_.⊩Γ ⊩t)))
...  | _ , _ , ρ∈ , _ = conv ([I]-inv (®El⇒tm T∈𝕌 t∼⟦t⟧)) ([I] ([I]-inv (®El⇒ty T∈𝕌 t∼⟦t⟧)))
  where open _⊩_∶_ ⊩t
        open GluExp (krip (InitEnvs⇒s®I ⊩Γ ρ∈))


⊩s⇒⊢s : Γ ⊩s σ ∶ Δ →
        ------------
        Γ ⊢s σ ∶ Δ
⊩s⇒⊢s ⊩σ
  with InitEnvs-related (fundamental-⊢Γ (⊩⇒⊢ (_⊩s_∶_.⊩Γ ⊩σ)))
...  | _ , _ , ρ∈ , _ = ∘I-inv′ (s®⇒⊢s ⊩Γ′ τσ∼⟦τ⟧)
  where open _⊩s_∶_ ⊩σ
        open GluSubsts (krip (InitEnvs⇒s®I ⊩Γ ρ∈))
