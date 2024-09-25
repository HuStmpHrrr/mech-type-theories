{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Proof of the fundamental theorem of soundness
module NonCumulative.Soundness.Fundamental (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂) where

open import Lib
open import Data.Nat.Properties as ℕₚ

open import NonCumulative.Statics.Ascribed.Properties
open import NonCumulative.Soundness.LogRel
open import NonCumulative.Soundness.Contexts fext
open import NonCumulative.Soundness.Nat fext
open import NonCumulative.Soundness.Pi fext
open import NonCumulative.Soundness.Substitutions fext
open import NonCumulative.Soundness.Terms fext
open import NonCumulative.Soundness.Universe fext


mutual
  fundamental-⊢⇒⊩′ : ⊢ Γ →
                     -------
                     ⊩ Γ
  fundamental-⊢⇒⊩′ ⊢[] = ⊢[]′
  fundamental-⊢⇒⊩′ (⊢∷ ⊢Γ ⊢T) = ⊢∷′ (fundamental-⊢t⇒⊩t′ ⊢T)

  fundamental-⊢t⇒⊩t′ : ∀ {i} → Γ ⊢ t ∶[ i ] T →
                       -------------
                       Γ ⊩ t ∶[ i ] T
  fundamental-⊢t⇒⊩t′ (N-wf ⊢Γ) = N-wf′ (fundamental-⊢⇒⊩′ ⊢Γ)
  fundamental-⊢t⇒⊩t′ (Se-wf i ⊢Γ) = Se-wf′ (fundamental-⊢⇒⊩′ ⊢Γ)
  fundamental-⊢t⇒⊩t′ (Liftt-wf j ⊢S) = Liftt-wf′ (fundamental-⊢t⇒⊩t′ ⊢S)
  fundamental-⊢t⇒⊩t′ (Π-wf {i = j} {j = k} {k = i} ⊢S ⊢T i≡maxjk) = Π-wf′ i≡maxjk (fundamental-⊢t⇒⊩t′ ⊢S) (fundamental-⊢t⇒⊩t′ ⊢T)
  fundamental-⊢t⇒⊩t′ (vlookup {x = n} ⊢Γ ∈Γ) = vlookup′ (fundamental-⊢⇒⊩′ ⊢Γ) ∈Γ
  fundamental-⊢t⇒⊩t′ (ze-I ⊢Γ) = ze-I′ (fundamental-⊢⇒⊩′ ⊢Γ)
  fundamental-⊢t⇒⊩t′ (su-I ⊢t) = su-I′ (fundamental-⊢t⇒⊩t′ ⊢t)
  fundamental-⊢t⇒⊩t′ (N-E ⊢T ⊢s ⊢r ⊢t) = N-E′ (fundamental-⊢t⇒⊩t′ ⊢T) (fundamental-⊢t⇒⊩t′ ⊢s) (fundamental-⊢t⇒⊩t′ ⊢r) (fundamental-⊢t⇒⊩t′ ⊢t)
  fundamental-⊢t⇒⊩t′ (Λ-I {i = k} ⊢S ⊢t i=maxjk) = Λ-I′ i=maxjk (fundamental-⊢t⇒⊩t′ ⊢t)
  fundamental-⊢t⇒⊩t′ (Λ-E {i = j} {j = k} {k = i} ⊢S ⊢T ⊢r ⊢s i≡maxjk) = Λ-E′ i≡maxjk (fundamental-⊢t⇒⊩t′ ⊢T) (fundamental-⊢t⇒⊩t′ ⊢r) (fundamental-⊢t⇒⊩t′ ⊢s)
  fundamental-⊢t⇒⊩t′ (L-I j ⊢t) = L-I′ (fundamental-⊢t⇒⊩t′ ⊢t)
  fundamental-⊢t⇒⊩t′ (L-E j ⊢T ⊢t) = L-E′ (fundamental-⊢t⇒⊩t′ ⊢T) (fundamental-⊢t⇒⊩t′ ⊢t)
  fundamental-⊢t⇒⊩t′ (t[σ] ⊢t ⊢σ) = t[σ]′ (fundamental-⊢t⇒⊩t′ ⊢t) (fundamental-⊢s⇒⊩s′ ⊢σ)
  fundamental-⊢t⇒⊩t′ (conv ⊢t S≈T) = conv′ (fundamental-⊢t⇒⊩t′ ⊢t) S≈T

  fundamental-⊢s⇒⊩s′ : Γ ⊢s σ ∶ Δ →
                       ---------------
                       Γ ⊩s σ ∶ Δ
  fundamental-⊢s⇒⊩s′ (s-I ⊢Γ) = s-I′ (fundamental-⊢⇒⊩′ ⊢Γ)
  fundamental-⊢s⇒⊩s′ (s-wk ⊢TΓ) = s-wk′ (fundamental-⊢⇒⊩′ ⊢TΓ)
  fundamental-⊢s⇒⊩s′ (s-∘ ⊢τ ⊢σ) = s-∘′ (fundamental-⊢s⇒⊩s′ ⊢τ) (fundamental-⊢s⇒⊩s′ ⊢σ)
  fundamental-⊢s⇒⊩s′ (s-, ⊢σ ⊢T ⊢t) = s-,′ (fundamental-⊢s⇒⊩s′ ⊢σ) (fundamental-⊢t⇒⊩t′ ⊢T) (fundamental-⊢t⇒⊩t′ ⊢t)
  fundamental-⊢s⇒⊩s′ (s-conv ⊢σ Γ≈Δ) = s-conv′ (fundamental-⊢s⇒⊩s′ ⊢σ) Γ≈Δ