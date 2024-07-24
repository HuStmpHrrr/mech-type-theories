{-# OPTIONS --without-K --safe #-}

-- Properties of evaluation that do not rely on functional extensionality
module Mint.Semantics.Properties.NoFunExt.Evaluation where

open import Lib

open import Mint.Statics.Syntax
import Mint.Statics.Properties.Ops as Sₚ
open import Mint.Semantics.Domain
open import Mint.Semantics.Properties.NoFunExt.Domain
open import Mint.Semantics.Evaluation

O-⟦⟧s : ∀ n → ⟦ σ ⟧s ρ ↘ ρ′ → O ρ (O σ n) ≡ O ρ′ n
O-⟦⟧s n ⟦I⟧
  rewrite Sₚ.O-I n          = refl
O-⟦⟧s n ⟦wk⟧
  rewrite Sₚ.O-wk n         = sym (O-drop n _)
O-⟦⟧s n (⟦,⟧ {σ} {_} {ρ′} {t} {a} ↘ρ′ ↘a)
  rewrite Sₚ.O-, n σ t
  rewrite O-↦ n ρ′ a        = O-⟦⟧s n ↘ρ′
O-⟦⟧s zero (⟦；⟧ ↘ρ′)       = refl
O-⟦⟧s (suc n) (⟦；⟧ {σ} {ρ} {ρ′} {m} ↘ρ′)
  rewrite O-ρ-+ ρ m (O σ n) = cong (O ρ m +_) (O-⟦⟧s n ↘ρ′)
O-⟦⟧s n (⟦∘⟧ {δ} {_} {_} {σ} ↘ρ′ ↘ρ″)
  rewrite Sₚ.O-∘ n σ δ
        | O-⟦⟧s (O σ n) ↘ρ′ = O-⟦⟧s n ↘ρ″
