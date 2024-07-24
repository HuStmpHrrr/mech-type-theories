{-# OPTIONS --without-K --safe #-}

-- Definitions of semantic judgments for completeness
module NonCumulative.Completeness.LogRel where

open import Lib
open import NonCumulative.Semantics.Domain public
open import NonCumulative.Semantics.Evaluation public
open import NonCumulative.Semantics.PER public


record RelExp t ρ t′ ρ′ (R : Ty) : Set where
  field
    ⟦t⟧   : D
    ⟦t′⟧  : D
    ↘⟦t⟧  : ⟦ t ⟧ ρ ↘ ⟦t⟧
    ↘⟦t′⟧ : ⟦ t′ ⟧ ρ′ ↘ ⟦t′⟧
    t≈t′  : ⟦t⟧ ≈ ⟦t′⟧ ∈ R

infix 4 _⊨_≈_∶[_]_ _⊨_∶[_]_ _⊨s_≈_∶_ _⊨s_∶_

-- Two terms are related if their evaluations are related by the evaluation of their type.
_⊨_≈_∶[_]_ : Ctx → Exp → Exp → ℕ → Typ → Set
Γ ⊨ t ≈ t′ ∶[ i ] T = Σ (⊨ Γ) λ ⊨Γ → ∀ {ρ ρ′} (ρ≈ρ′ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ) → Σ (RelTyp i T ρ T ρ′) λ rel → let open RelTyp rel in RelExp t ρ t′ ρ′ (El _ T≈T′)

_⊨_∶[_]_ : Ctx → Exp → ℕ → Typ → Set
Γ ⊨ t ∶[ i ] T = Γ ⊨ t ≈ t ∶[ i ] T


record RelSubst σ ρ δ ρ′ (R : Ev) : Set where
  field
    ⟦σ⟧  : Env
    ⟦δ⟧  : Env
    ↘⟦σ⟧ : ⟦ σ ⟧s ρ ↘ ⟦σ⟧
    ↘⟦δ⟧ : ⟦ δ ⟧s ρ′ ↘ ⟦δ⟧
    σ≈δ  : ⟦σ⟧ ≈ ⟦δ⟧ ∈ R

-- Two substitutions are related if their evaluations are related.
_⊨s_≈_∶_ : Ctx → Subst → Subst → Ctx → Set
Γ ⊨s σ ≈ σ′ ∶ Δ = Σ (⊨ Γ) λ ⊨Γ → Σ (⊨ Δ) λ ⊨Δ → ∀ {ρ ρ′} (ρ≈ρ′ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ) → RelSubst σ ρ σ′ ρ′ ⟦ ⊨Δ ⟧ρ

_⊨s_∶_ : Ctx → Subst → Ctx → Set
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
