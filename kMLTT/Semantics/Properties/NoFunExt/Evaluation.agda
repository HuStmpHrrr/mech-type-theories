{-# OPTIONS --without-K --safe #-}

module kMLTT.Semantics.Properties.NoFunExt.Evaluation where

open import Lib

open import kMLTT.Statics.Syntax
import kMLTT.Statics.Properties.Ops as Sₚ
open import kMLTT.Semantics.Domain
open import kMLTT.Semantics.Properties.NoFunExt.Domain
open import kMLTT.Semantics.Evaluation

L-⟦⟧s : ∀ n → ⟦ σ ⟧s ρ ↘ ρ′ → L ρ (L σ n) ≡ L ρ′ n
L-⟦⟧s n ⟦I⟧
  rewrite Sₚ.L-I n          = refl
L-⟦⟧s n (⟦p⟧ {σ} {_} {ρ′} ↘ρ′)
  rewrite Sₚ.L-p n σ
        | L-drop n ρ′       = L-⟦⟧s n ↘ρ′
L-⟦⟧s n (⟦,⟧ {σ} {_} {ρ′} {t} {a} ↘ρ′ ↘a)
  rewrite Sₚ.L-, n σ t
  rewrite L-↦ n ρ′ a        = L-⟦⟧s n ↘ρ′
L-⟦⟧s zero (⟦；⟧ ↘ρ′)       = refl
L-⟦⟧s (suc n) (⟦；⟧ {σ} {ρ} {ρ′} {m} ↘ρ′)
  rewrite L-ρ-+ ρ m (L σ n) = cong (L ρ m +_) (L-⟦⟧s n ↘ρ′)
L-⟦⟧s n (⟦∘⟧ {δ} {_} {_} {σ} ↘ρ′ ↘ρ″)
  rewrite Sₚ.L-∘ n σ δ
        | L-⟦⟧s (L σ n) ↘ρ′ = L-⟦⟧s n ↘ρ″
