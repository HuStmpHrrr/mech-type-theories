{-# OPTIONS --without-K --safe #-}

module STLCSubst.Semantics.Substitutions where

open import STLCSubst.Statics
open import STLCSubst.Semantics.Definitions
open import STLCSubst.Semantics.PER


⊨id : Γ ⊨s id ≈ id ∶ Γ
⊨id {_} {_} {ϕ} ⊢ϕ ρ≈ρ′ = record
  { ↘⟦σ⟧  = λ x → ⟦v⟧ (ϕ x)
  ; ↘⟦σ⟧′ = ⟦v⟧
  ; ↘⟦τ⟧  = λ x → ⟦v⟧ (ϕ x)
  ; ↘⟦τ⟧′ = ⟦v⟧
  ; σ≈σ′  = λ {_} {T} T∈Γ → ⟦⟧≈refl T (ρ≈ρ′ (⊢ϕ T∈Γ))
  ; σ≈τ   = λ T∈Γ → ρ≈ρ′ (⊢ϕ T∈Γ)
  ; τ≈τ′  = λ {_} {T} T∈Γ → ⟦⟧≈refl′ T (ρ≈ρ′ (⊢ϕ T∈Γ))
  }

Wk-sem : Γ ⊢w ψ ∶ Δ → Γ ⊨s conv ψ ∶ Δ
Wk-sem {_} {ψ} ⊢ψ {_} {ϕ} ⊢ϕ ρ≈ρ′ = record
  { ↘⟦σ⟧  = λ x → ⟦v⟧ (ϕ (ψ x))
  ; ↘⟦σ⟧′ = λ x → ⟦v⟧ (ψ x)
  ; ↘⟦τ⟧  = λ x → ⟦v⟧ (ϕ (ψ x))
  ; ↘⟦τ⟧′ = λ x → ⟦v⟧ (ψ x)
  ; σ≈σ′  = λ {_} {T} T∈Δ → ⟦⟧≈refl T (ρ≈ρ′ (⊢ϕ (⊢ψ T∈Δ)))
  ; σ≈τ   = λ T∈Δ → ρ≈ρ′ (⊢ϕ (⊢ψ T∈Δ))
  ; τ≈τ′  = λ {_} {T} T∈Δ → ⟦⟧≈refl′ T (ρ≈ρ′ (⊢ϕ (⊢ψ T∈Δ)))
  }
