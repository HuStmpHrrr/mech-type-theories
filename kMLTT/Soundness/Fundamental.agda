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
  fundamental-⊢Γ : ⊢ Γ → ⊩ Γ
  fundamental-⊢Γ ⊢[] = ⊢[]′
  fundamental-⊢Γ (⊢κ ⊢Γ) = ⊢κ′ (fundamental-⊢Γ ⊢Γ)
  fundamental-⊢Γ (⊢∺ ⊢Γ ⊢T) = ⊢∺′ (fundamental-⊢t ⊢T)

  fundamental-⊢t : Γ ⊢ t ∶ T → Γ ⊩ t ∶ T
  fundamental-⊢t (N-wf i ⊢Γ) = N-wf′ i (fundamental-⊢Γ ⊢Γ)
  fundamental-⊢t (Se-wf i ⊢Γ) = Se-wf′ (fundamental-⊢Γ ⊢Γ)
  fundamental-⊢t (Π-wf ⊢S ⊢T) = Π-wf′ (fundamental-⊢t ⊢S) (fundamental-⊢t ⊢T)
  fundamental-⊢t (□-wf ⊢T) = □-wf′ (fundamental-⊢t ⊢T)
  fundamental-⊢t (vlookup ⊢Γ x∈) = vlookup′ (fundamental-⊢Γ ⊢Γ) x∈
  fundamental-⊢t (ze-I ⊢Γ) = ze-I′ (fundamental-⊢Γ ⊢Γ)
  fundamental-⊢t (su-I ⊢t) = su-I′ (fundamental-⊢t ⊢t)
  fundamental-⊢t (N-E ⊢T ⊢s ⊢r ⊢t) = N-E′ (fundamental-⊢t ⊢T) (fundamental-⊢t ⊢s) (fundamental-⊢t ⊢r) (fundamental-⊢t ⊢t)
  fundamental-⊢t (Λ-I ⊢S ⊢t) = Λ-I′ (fundamental-⊢t ⊢S) (fundamental-⊢t ⊢t)
  fundamental-⊢t (Λ-E ⊢r ⊢s) = Λ-E′ {!!} (fundamental-⊢t ⊢r) (fundamental-⊢t ⊢s)
  fundamental-⊢t (□-I ⊢t) = □-I′ (fundamental-⊢t ⊢t)
  fundamental-⊢t (□-E Ψs ⊢t ⊢ΨsΓ eq) = □-E′ Ψs {!!} (fundamental-⊢t ⊢t) (fundamental-⊢Γ ⊢ΨsΓ) eq
  fundamental-⊢t (t[σ] ⊢t ⊢σ) = t[σ]′ (fundamental-⊢t ⊢t) (fundamental-⊢σ ⊢σ)
  fundamental-⊢t (cumu ⊢t) = cumu′ (fundamental-⊢t ⊢t)
  fundamental-⊢t (conv ⊢t T′≈T) = conv′ (fundamental-⊢t ⊢t) T′≈T

  fundamental-⊢σ : Γ ⊢s σ ∶ Δ → Γ ⊩s σ ∶ Δ
  fundamental-⊢σ (s-I ⊢Γ) = s-I′ (fundamental-⊢Γ ⊢Γ)
  fundamental-⊢σ (s-wk ⊢Γ) = s-wk′ (fundamental-⊢Γ ⊢Γ)
  fundamental-⊢σ (s-∘ ⊢τ ⊢σ) = s-∘′ (fundamental-⊢σ ⊢τ) (fundamental-⊢σ ⊢σ)
  fundamental-⊢σ (s-, ⊢σ ⊢T ⊢t) = s-,′ (fundamental-⊢σ ⊢σ) (fundamental-⊢t ⊢T) (fundamental-⊢t ⊢t)
  fundamental-⊢σ (s-； Ψs ⊢σ ⊢ΨsΓ eq) = s-；′ Ψs (fundamental-⊢σ ⊢σ) (fundamental-⊢Γ ⊢ΨsΓ) eq
  fundamental-⊢σ (s-conv ⊢σ Δ′≈Δ) = s-conv′ (fundamental-⊢σ ⊢σ) Δ′≈Δ
