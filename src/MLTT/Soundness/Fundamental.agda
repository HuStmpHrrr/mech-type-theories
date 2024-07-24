{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Proof of the fundamental theorem of soundness
module MLTT.Soundness.Fundamental (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Lib
open import Data.Nat.Properties as ℕₚ

open import MLTT.Statics.Properties
open import MLTT.Soundness.LogRel
open import MLTT.Soundness.Typing as S hiding (⊢_; _⊢_∶_; _⊢s_∶_)
open import MLTT.Soundness.Equiv
open import MLTT.Soundness.Contexts fext
open import MLTT.Soundness.Nat fext
open import MLTT.Soundness.Pi fext
open import MLTT.Soundness.Substitutions fext
open import MLTT.Soundness.Terms fext
open import MLTT.Soundness.Universe fext

mutual
  fundamental-⊢⇒⊩′ : S.⊢ Γ →
                     -------
                     ⊩ Γ
  fundamental-⊢⇒⊩′ ⊢[]        = ⊢[]′
  fundamental-⊢⇒⊩′ (⊢∷ ⊢Γ ⊢T) = ⊢∷′ (fundamental-⊢t⇒⊩t′ ⊢T)

  fundamental-⊢t⇒⊩t′ : Γ S.⊢ t ∶ T →
                       -------------
                       Γ ⊩ t ∶ T
  fundamental-⊢t⇒⊩t′ (N-wf i ⊢Γ)            = N-wf′ i (fundamental-⊢⇒⊩′ ⊢Γ)
  fundamental-⊢t⇒⊩t′ (Se-wf i ⊢Γ)           = Se-wf′ (fundamental-⊢⇒⊩′ ⊢Γ)
  fundamental-⊢t⇒⊩t′ (Π-wf ⊢S ⊢T)           = Π-wf′ (fundamental-⊢t⇒⊩t′ ⊢S) (fundamental-⊢t⇒⊩t′ ⊢T)
  fundamental-⊢t⇒⊩t′ (vlookup ⊢Γ x∈)        = vlookup′ (fundamental-⊢⇒⊩′ ⊢Γ) x∈
  fundamental-⊢t⇒⊩t′ (ze-I ⊢Γ)              = ze-I′ (fundamental-⊢⇒⊩′ ⊢Γ)
  fundamental-⊢t⇒⊩t′ (su-I ⊢t)              = su-I′ (fundamental-⊢t⇒⊩t′ ⊢t)
  fundamental-⊢t⇒⊩t′ (N-E ⊢T ⊢s ⊢w ⊢t)      = N-E′ (fundamental-⊢t⇒⊩t′ ⊢T) (fundamental-⊢t⇒⊩t′ ⊢s) (fundamental-⊢t⇒⊩t′ ⊢w) (fundamental-⊢t⇒⊩t′ ⊢t)
  fundamental-⊢t⇒⊩t′ (Λ-I ⊢t)               = Λ-I′ (fundamental-⊢t⇒⊩t′ ⊢t)
  fundamental-⊢t⇒⊩t′ (Λ-E ⊢T ⊢w ⊢s)         = Λ-E′ (fundamental-⊢t⇒⊩t′ ⊢T) (fundamental-⊢t⇒⊩t′ ⊢w) (fundamental-⊢t⇒⊩t′ ⊢s)
  fundamental-⊢t⇒⊩t′ (t[σ] ⊢t ⊢σ)           = t[σ]′ (fundamental-⊢t⇒⊩t′ ⊢t) (fundamental-⊢s⇒⊩s′ ⊢σ)
  fundamental-⊢t⇒⊩t′ (cumu ⊢t)              = cumu′ (fundamental-⊢t⇒⊩t′ ⊢t)
  fundamental-⊢t⇒⊩t′ (conv ⊢t T′≈T)         = conv′ (fundamental-⊢t⇒⊩t′ ⊢t) T′≈T

  fundamental-⊢s⇒⊩s′ : Γ S.⊢s σ ∶ Δ →
                       ---------------
                       Γ ⊩s σ ∶ Δ
  fundamental-⊢s⇒⊩s′ (s-I ⊢Γ)             = s-I′ (fundamental-⊢⇒⊩′ ⊢Γ)
  fundamental-⊢s⇒⊩s′ (s-wk ⊢Γ)            = s-wk′ (fundamental-⊢⇒⊩′ ⊢Γ)
  fundamental-⊢s⇒⊩s′ (s-∘ ⊢τ ⊢σ)          = s-∘′ (fundamental-⊢s⇒⊩s′ ⊢τ) (fundamental-⊢s⇒⊩s′ ⊢σ)
  fundamental-⊢s⇒⊩s′ (s-, ⊢σ ⊢T ⊢t)       = s-,′ (fundamental-⊢s⇒⊩s′ ⊢σ) (fundamental-⊢t⇒⊩t′ ⊢T) (fundamental-⊢t⇒⊩t′ ⊢t)
  fundamental-⊢s⇒⊩s′ (s-conv ⊢σ Δ′≈Δ)     = s-conv′ (fundamental-⊢s⇒⊩s′ ⊢σ) Δ′≈Δ


fundamental-⊢⇒⊩ : ⊢ Γ →
                  -------
                  ⊩ Γ
fundamental-⊢⇒⊩ ⊢Γ = fundamental-⊢⇒⊩′ (C⇒S-⊢ ⊢Γ)


fundamental-⊢t⇒⊩t : Γ ⊢ t ∶ T →
                    -------------
                    Γ ⊩ t ∶ T
fundamental-⊢t⇒⊩t ⊢t = fundamental-⊢t⇒⊩t′ (C⇒S-tm ⊢t)


fundamental-⊢s⇒⊩s : Γ ⊢s σ ∶ Δ →
                    ---------------
                    Γ ⊩s σ ∶ Δ
fundamental-⊢s⇒⊩s ⊢σ = fundamental-⊢s⇒⊩s′ (C⇒S-s ⊢σ)
