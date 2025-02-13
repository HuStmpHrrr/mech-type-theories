{-# OPTIONS --without-K --safe #-}

module NonCumulative.Statics.Equivalence.AIEquivalence where

open import Lib

open import NonCumulative.Statics.Ascribed.Full as A
open import NonCumulative.Statics.Equivalence.FullAI as AI

mutual
  AI⇒A-⊢ : AI.⊢ Γ →
           -------
           A.⊢ Γ 
  AI⇒A-⊢ ⊢[] = ⊢[]
  AI⇒A-⊢ (⊢∷ ⊢Γ ⊢T) = ⊢∷ (AI⇒A-⊢ ⊢Γ) (AI⇒A-tm ⊢T)

  AI⇒A-⊢≈ : AI.⊢ Γ ≈ Δ →
            -------
            A.⊢ Γ ≈ Δ
  AI⇒A-⊢≈ []-≈ = {!   !}
  AI⇒A-⊢≈ (∷-cong x x₁ Γ≈Δ x₂ x₃ x₄ x₅) = {!   !}

  AI⇒A-tm : ∀ {i} →
            Γ AI.⊢ t ∶[ i ] T →
            -------------
            Γ A.⊢ t ∶[ i ] T
  AI⇒A-tm ⊢t = {!   !}

  AI⇒A-s : Γ AI.⊢s σ ∶ Δ →
           -------------
           Γ A.⊢s σ ∶ Δ
  AI⇒A-s ⊢σ = {!   !}

  AI⇒A-≈ : ∀ {i} →
          Γ AI.⊢ t ≈ s ∶[ i ] T →
          -------------
          Γ A.⊢ t ≈ s ∶[ i ] T
  AI⇒A-≈ t≈s = {!   !}

  AI⇒A-s≈ : Γ AI.⊢s σ ≈ τ ∶ Δ →
           -------------
           Γ A.⊢s σ ≈ τ ∶ Δ
  AI⇒A-s≈ σ≈τ = {!   !}

mutual
  A⇒AI-⊢ : A.⊢ Γ →
           -------
           AI.⊢ Γ 
  A⇒AI-⊢ ⊢[] = ⊢[]
  A⇒AI-⊢ (⊢∷ ⊢Γ ⊢T) = ⊢∷ (A⇒AI-⊢ ⊢Γ) (A⇒AI-tm ⊢T)

  A⇒AI-⊢≈ : A.⊢ Γ ≈ Δ →
            -------
            AI.⊢ Γ ≈ Δ
  A⇒AI-⊢≈ []-≈ = {!   !}
  A⇒AI-⊢≈ (∷-cong Γ≈Δ x₂ x₃ x₄ x₅) = ∷-cong {!   !} {!   !} {!   !} {!   !} {!   !} {!   !} {!   !}

  A⇒AI-tm : ∀ {i} →
            Γ A.⊢ t ∶[ i ] T →
            -------------
            Γ AI.⊢ t ∶[ i ] T
  A⇒AI-tm ⊢t = {!   !}

  A⇒AI-s : Γ A.⊢s σ ∶ Δ →
           -------------
           Γ AI.⊢s σ ∶ Δ
  A⇒AI-s ⊢σ = {!   !}

  A⇒AI-≈ : ∀ {i} →
          Γ A.⊢ t ≈ s ∶[ i ] T →
          -------------
          Γ AI.⊢ t ≈ s ∶[ i ] T
  A⇒AI-≈ t≈s = {!   !}

  A⇒AI-s≈ : Γ A.⊢s σ ≈ τ ∶ Δ →
           -------------
           Γ AI.⊢s σ ≈ τ ∶ Δ
  A⇒AI-s≈ σ≈τ = {!   !}