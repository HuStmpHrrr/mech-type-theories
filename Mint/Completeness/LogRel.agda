{-# OPTIONS --without-K --safe #-}

-- Definitions of semantic judgments for completeness
module Mint.Completeness.LogRel where

open import Lib
open import Mint.Semantics.Domain public
open import Mint.Semantics.Evaluation public
open import Mint.Semantics.PER public


record RelExp t ρ t′ ρ′ (R : Ty) : Set where
  field
    ⟦t⟧   : D
    ⟦t′⟧  : D
    ↘⟦t⟧  : ⟦ t ⟧ ρ ↘ ⟦t⟧
    ↘⟦t′⟧ : ⟦ t′ ⟧ ρ′ ↘ ⟦t′⟧
    t≈t′  : ⟦t⟧ ≈ ⟦t′⟧ ∈ R

infix 4 _⊨_≈_∶_ _⊨_∶_ _⊨s_≈_∶_ _⊨s_∶_

-- Two terms are related if their evaluations are related by the evaluation of their type.
_⊨_≈_∶_ : Ctxs → Exp → Exp → Typ → Set
Γ ⊨ t ≈ t′ ∶ T = Σ (⊨ Γ) λ ⊨Γ → ∃ λ i → ∀ {ρ ρ′} (ρ≈ρ′ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ) → Σ (RelTyp i T ρ T ρ′) λ rel → let open RelTyp rel in RelExp t ρ t′ ρ′ (El _ T≈T′)

_⊨_∶_ : Ctxs → Exp → Typ → Set
Γ ⊨ t ∶ T = Γ ⊨ t ≈ t ∶ T


record RelSubsts σ ρ δ ρ′ (R : Evs) : Set where
  field
    ⟦σ⟧  : Envs
    ⟦δ⟧  : Envs
    ↘⟦σ⟧ : ⟦ σ ⟧s ρ ↘ ⟦σ⟧
    ↘⟦δ⟧ : ⟦ δ ⟧s ρ′ ↘ ⟦δ⟧
    σ≈δ  : ⟦σ⟧ ≈ ⟦δ⟧ ∈ R

-- Two substitutions are related if their evaluations are related.
_⊨s_≈_∶_ : Ctxs → Substs → Substs → Ctxs → Set
Γ ⊨s σ ≈ σ′ ∶ Δ = Σ (⊨ Γ) λ ⊨Γ → Σ (⊨ Δ) λ ⊨Δ → ∀ {ρ ρ′} (ρ≈ρ′ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ) → RelSubsts σ ρ σ′ ρ′ ⟦ ⊨Δ ⟧ρ

_⊨s_∶_ : Ctxs → Substs → Ctxs → Set
Γ ⊨s σ ∶ Δ = Γ ⊨s σ ≈ σ ∶ Δ

RelExp⇒RepTyp : ∀ {i} → RelExp T ρ T′ ρ′ (𝕌 i) → RelTyp i T ρ T′ ρ′
RelExp⇒RepTyp rel = record
  { ⟦T⟧   = ⟦t⟧
  ; ⟦T′⟧  = ⟦t′⟧
  ; ↘⟦T⟧  = ↘⟦t⟧
  ; ↘⟦T′⟧ = ↘⟦t′⟧
  ; T≈T′  = t≈t′
  }
  where open RelExp rel
