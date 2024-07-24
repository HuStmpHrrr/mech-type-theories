{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

-- Proof of the fundamental theorem of soundness
module Mint.Soundness.Fundamental (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Data.Nat.Properties as ℕₚ

open import Mint.Statics.Properties
open import Mint.Soundness.LogRel
open import Mint.Soundness.Typing as S hiding (⊢_; _⊢_∶_; _⊢s_∶_)
open import Mint.Soundness.Equiv
open import Mint.Soundness.Contexts fext
open import Mint.Soundness.Box fext
open import Mint.Soundness.Nat fext
open import Mint.Soundness.Pi fext
open import Mint.Soundness.Substitutions fext
open import Mint.Soundness.Terms fext
open import Mint.Soundness.Universe fext

mutual
  fundamental-⊢⇒⊩′ : S.⊢ Γ →
                     -------
                     ⊩ Γ
  fundamental-⊢⇒⊩′ ⊢[]        = ⊢[]′
  fundamental-⊢⇒⊩′ (⊢κ ⊢Γ)    = ⊢κ′ (fundamental-⊢⇒⊩′ ⊢Γ)
  fundamental-⊢⇒⊩′ (⊢∺ ⊢Γ ⊢T) = ⊢∺′ (fundamental-⊢t⇒⊩t′ ⊢T)

  fundamental-⊢t⇒⊩t′ : Γ S.⊢ t ∶ T →
                       -------------
                       Γ ⊩ t ∶ T
  fundamental-⊢t⇒⊩t′ (N-wf i ⊢Γ)            = N-wf′ i (fundamental-⊢⇒⊩′ ⊢Γ)
  fundamental-⊢t⇒⊩t′ (Se-wf i ⊢Γ)           = Se-wf′ (fundamental-⊢⇒⊩′ ⊢Γ)
  fundamental-⊢t⇒⊩t′ (Π-wf ⊢S ⊢T)           = Π-wf′ (fundamental-⊢t⇒⊩t′ ⊢S) (fundamental-⊢t⇒⊩t′ ⊢T)
  fundamental-⊢t⇒⊩t′ (□-wf ⊢T)              = □-wf′ (fundamental-⊢t⇒⊩t′ ⊢T)
  fundamental-⊢t⇒⊩t′ (vlookup ⊢Γ x∈)        = vlookup′ (fundamental-⊢⇒⊩′ ⊢Γ) x∈
  fundamental-⊢t⇒⊩t′ (ze-I ⊢Γ)              = ze-I′ (fundamental-⊢⇒⊩′ ⊢Γ)
  fundamental-⊢t⇒⊩t′ (su-I ⊢t)              = su-I′ (fundamental-⊢t⇒⊩t′ ⊢t)
  fundamental-⊢t⇒⊩t′ (N-E ⊢T ⊢s ⊢r ⊢t)      = N-E′ (fundamental-⊢t⇒⊩t′ ⊢T) (fundamental-⊢t⇒⊩t′ ⊢s) (fundamental-⊢t⇒⊩t′ ⊢r) (fundamental-⊢t⇒⊩t′ ⊢t)
  fundamental-⊢t⇒⊩t′ (Λ-I ⊢t)               = Λ-I′ (fundamental-⊢t⇒⊩t′ ⊢t)
  fundamental-⊢t⇒⊩t′ (Λ-E ⊢T ⊢r ⊢s)         = Λ-E′ (fundamental-⊢t⇒⊩t′ ⊢T) (fundamental-⊢t⇒⊩t′ ⊢r) (fundamental-⊢t⇒⊩t′ ⊢s)
  fundamental-⊢t⇒⊩t′ (□-I ⊢t)               = □-I′ (fundamental-⊢t⇒⊩t′ ⊢t)
  fundamental-⊢t⇒⊩t′ (□-E Ψs ⊢T ⊢t ⊢ΨsΓ eq) = □-E′ Ψs (fundamental-⊢t⇒⊩t′ ⊢T) (fundamental-⊢t⇒⊩t′ ⊢t) (fundamental-⊢⇒⊩′ ⊢ΨsΓ) eq
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
  fundamental-⊢s⇒⊩s′ (s-； Ψs ⊢σ ⊢ΨsΓ eq) = s-；′ Ψs (fundamental-⊢s⇒⊩s′ ⊢σ) (fundamental-⊢⇒⊩′ ⊢ΨsΓ) eq
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
