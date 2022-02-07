{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Soundness.Fundamental (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Data.Nat.Properties as ℕₚ

open import kMLTT.Statics.Properties
open import kMLTT.Soundness.LogRel
open import kMLTT.Soundness.Contexts fext
open import kMLTT.Soundness.Box fext
open import kMLTT.Soundness.Nat fext
open import kMLTT.Soundness.Pi fext
open import kMLTT.Soundness.Substitutions fext
open import kMLTT.Soundness.Terms fext
open import kMLTT.Soundness.Universe fext

mutual
  fundamental-⊢⇒⊩ : ⊢ Γ → ⊩ Γ
  fundamental-⊢⇒⊩ ⊢[] = ⊢[]′
  fundamental-⊢⇒⊩ (⊢κ ⊢Γ) = ⊢κ′ (fundamental-⊢⇒⊩ ⊢Γ)
  fundamental-⊢⇒⊩ (⊢∺ ⊢Γ ⊢T) = ⊢∺′ (fundamental-⊢t⇒⊩t ⊢T)

  fundamental-⊢t⇒⊩t : Γ ⊢ t ∶ T → Γ ⊩ t ∶ T
  fundamental-⊢t⇒⊩t (N-wf i ⊢Γ) = N-wf′ i (fundamental-⊢⇒⊩ ⊢Γ)
  fundamental-⊢t⇒⊩t (Se-wf i ⊢Γ) = Se-wf′ (fundamental-⊢⇒⊩ ⊢Γ)
  fundamental-⊢t⇒⊩t (Π-wf ⊢S ⊢T) = Π-wf′ (fundamental-⊢t⇒⊩t ⊢S) (fundamental-⊢t⇒⊩t ⊢T)
  fundamental-⊢t⇒⊩t (□-wf ⊢T) = □-wf′ (fundamental-⊢t⇒⊩t ⊢T)
  fundamental-⊢t⇒⊩t (vlookup ⊢Γ x∈) = vlookup′ (fundamental-⊢⇒⊩ ⊢Γ) x∈
  fundamental-⊢t⇒⊩t (ze-I ⊢Γ) = ze-I′ (fundamental-⊢⇒⊩ ⊢Γ)
  fundamental-⊢t⇒⊩t (su-I ⊢t) = su-I′ (fundamental-⊢t⇒⊩t ⊢t)
  fundamental-⊢t⇒⊩t (N-E ⊢T ⊢s ⊢r ⊢t) = N-E′ (fundamental-⊢t⇒⊩t ⊢T) (fundamental-⊢t⇒⊩t ⊢s) (fundamental-⊢t⇒⊩t ⊢r) (fundamental-⊢t⇒⊩t ⊢t)
  fundamental-⊢t⇒⊩t (Λ-I ⊢S ⊢t) = Λ-I′ (fundamental-⊢t⇒⊩t ⊢S) (fundamental-⊢t⇒⊩t ⊢t)
  fundamental-⊢t⇒⊩t (Λ-E ⊢r ⊢s) = Λ-E′ {!!} (fundamental-⊢t⇒⊩t ⊢r) (fundamental-⊢t⇒⊩t ⊢s)
  fundamental-⊢t⇒⊩t (□-I ⊢t) = □-I′ (fundamental-⊢t⇒⊩t ⊢t)
  fundamental-⊢t⇒⊩t (□-E Ψs ⊢t ⊢ΨsΓ eq) = □-E′ Ψs {!!} (fundamental-⊢t⇒⊩t ⊢t) (fundamental-⊢⇒⊩ ⊢ΨsΓ) eq
  fundamental-⊢t⇒⊩t (t[σ] ⊢t ⊢σ) = t[σ]′ (fundamental-⊢t⇒⊩t ⊢t) (fundamental-⊢s⇒⊩s ⊢σ)
  fundamental-⊢t⇒⊩t (cumu ⊢t) = cumu′ (fundamental-⊢t⇒⊩t ⊢t)
  fundamental-⊢t⇒⊩t (conv ⊢t T′≈T) = conv′ (fundamental-⊢t⇒⊩t ⊢t) T′≈T

  fundamental-⊢s⇒⊩s : Γ ⊢s σ ∶ Δ → Γ ⊩s σ ∶ Δ
  fundamental-⊢s⇒⊩s (s-I ⊢Γ) = s-I′ (fundamental-⊢⇒⊩ ⊢Γ)
  fundamental-⊢s⇒⊩s (s-wk ⊢Γ) = s-wk′ (fundamental-⊢⇒⊩ ⊢Γ)
  fundamental-⊢s⇒⊩s (s-∘ ⊢τ ⊢σ) = s-∘′ (fundamental-⊢s⇒⊩s ⊢τ) (fundamental-⊢s⇒⊩s ⊢σ)
  fundamental-⊢s⇒⊩s (s-, ⊢σ ⊢T ⊢t) = s-,′ (fundamental-⊢s⇒⊩s ⊢σ) (fundamental-⊢t⇒⊩t ⊢T) (fundamental-⊢t⇒⊩t ⊢t)
  fundamental-⊢s⇒⊩s (s-； Ψs ⊢σ ⊢ΨsΓ eq) = s-；′ Ψs (fundamental-⊢s⇒⊩s ⊢σ) (fundamental-⊢⇒⊩ ⊢ΨsΓ) eq
  fundamental-⊢s⇒⊩s (s-conv ⊢σ Δ′≈Δ) = s-conv′ (fundamental-⊢s⇒⊩s ⊢σ) Δ′≈Δ
