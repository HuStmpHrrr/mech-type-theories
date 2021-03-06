{-# OPTIONS --without-K --safe #-}

module PTT.StaticsProps where

open import Lib
open import PTT.Statics

mutual
  ty⇒env-wf : Γ ⊢ t ∶ T →
              ------------
              ⊢ Γ
  ty⇒env-wf (N-wf _ ⊢Γ)     = ⊢Γ
  ty⇒env-wf (Se-wf ⊢Γ _)    = ⊢Γ
  ty⇒env-wf (Π-wf ⊢S _ _ _) = ty⇒env-wf ⊢S
  ty⇒env-wf (vlookup ⊢Γ _)  = ⊢Γ
  ty⇒env-wf (ze-I ⊢Γ)       = ⊢Γ
  ty⇒env-wf (su-I t)        = ty⇒env-wf t
  ty⇒env-wf (N-E ⊢Π _ _ _)  = ty⇒env-wf ⊢Π
  ty⇒env-wf (Λ-I t) with ty⇒env-wf t
  ... | ⊢∷ ⊢Γ _             = ⊢Γ
  ty⇒env-wf (Λ-E r _)       = ty⇒env-wf r
  ty⇒env-wf (t[σ] _ σ)      = tys⇒env-wf σ
  ty⇒env-wf (conv t _)      = ty⇒env-wf t

  tys⇒env-wf : Γ ⊢s σ ∶ Δ →
              ------------
              ⊢ Γ
  tys⇒env-wf (S-↑ ⊢Γ)  = ⊢Γ
  tys⇒env-wf (S-I ⊢Γ)  = ⊢Γ
  tys⇒env-wf (S-∘ σ _) = tys⇒env-wf σ
  tys⇒env-wf (S-, σ _) = tys⇒env-wf σ
