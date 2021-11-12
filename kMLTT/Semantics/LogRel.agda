{-# OPTIONS --without-K --safe #-}

module kMLTT.Semantics.LogRel where

open import Lib
open import kMLTT.Semantics.Domain
open import kMLTT.Semantics.Evaluation
open import kMLTT.Semantics.PER

record RelTyp T ρ T′ ρ′ : Set where
  field
    ⟦T⟧   : D
    ⟦T′⟧  : D
    ↘⟦T⟧  : ⟦ T ⟧ ρ ↘ ⟦T⟧
    ↘⟦T′⟧ : ⟦ T′ ⟧ ρ′ ↘ ⟦T′⟧
    T≈T′  : ⟦T⟧ ≈ ⟦T′⟧ ∈ 𝕌∞
    nat   : ∀ (κ : UnMoT) → ⟦ T ⟧ ρ [ κ ] ↘ ⟦T⟧ [ κ ]
    nat′  : ∀ (κ : UnMoT) → ⟦ T′ ⟧ ρ′ [ κ ] ↘ ⟦T′⟧ [ κ ]

infix 4 ⊨_≈_ ⊨_ _⊨_ _⊨_∶_ _⊨s_∶_ _⊨_≈_∶_ _⊨s_≈_∶_
mutual
  data ⊨_≈_ : Ctxs → Ctxs → Set where
    []-≈   : ⊨ [] ∷ [] ≈ [] ∷ []
    κ-cong : ⊨ Γ ≈ Δ →
             -------------------
             ⊨ [] ∷⁺ Γ ≈ [] ∷⁺ Δ
    ∷-cong : (Γ≈Δ : ⊨ Γ ≈ Δ) →
             (∀ {ρ ρ′} → ρ ≈ ρ′ ∈ ⟦ Γ≈Δ ⟧ρ → RelTyp T ρ T′ ρ′) →
             ----------------
             ⊨ T ∺ Γ ≈ T′ ∺ Δ

  ⟦_⟧ρ : ⊨ Γ ≈ Δ → Evs
  ⟦ []-≈ ⟧ρ ρ ρ′           = ⊤
  ⟦ κ-cong Γ≈Δ ⟧ρ ρ ρ′     = (ρ ∥ 1 ≈ ρ′ ∥ 1 ∈ ⟦ Γ≈Δ ⟧ρ) × proj₁ (ρ 0) ≡ proj₁ (ρ′ 0)
  ⟦ ∷-cong Γ≈Δ rel ⟧ρ ρ ρ′ = Σ (drop ρ ≈ drop ρ′ ∈ ⟦ Γ≈Δ ⟧ρ) λ ρ≈ρ′ → let open RelTyp (rel ρ≈ρ′) in lookup ρ 0 ≈ lookup ρ′ 0 ∈ El∞ T≈T′

⊨_ : Ctxs → Set
⊨ Γ = ⊨ Γ ≈ Γ

_⊨_ : Ctxs → Typ → Set
Γ ⊨ T = Σ (⊨ Γ) λ ⊨Γ → ∀ {ρ ρ′} → ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → RelTyp T ρ T ρ′

record RelExp (t : Exp) ρ t ρ′ (R : Ty) : Set where
  field
    ⟦t⟧   : D
    ⟦t′⟧  : D
    ↘⟦t⟧  : ⟦ t ⟧ ρ ↘ ⟦t⟧
    ↘⟦t′⟧ : ⟦ t′ ⟧ ρ′ ↘ ⟦t′⟧
    t≈t′  : ⟦t⟧ ≈ ⟦t′⟧ ∈ R
    nat   : ∀ (κ : UnMoT) → ⟦ t ⟧ ρ [ κ ] ↘ ⟦t⟧ [ κ ]
    nat′  : ∀ (κ : UnMoT) → ⟦ t′ ⟧ ρ′ [ κ ] ↘ ⟦t′⟧ [ κ ]


_⊨_≈_∶_ : Ctxs → Exp → Exp → Typ → Set
Γ ⊨ t ≈ t′ ∶ T = Σ (Γ ⊨ T) λ (⊨Γ , rel) → ∀ {ρ ρ′} (ρ≈ρ′ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ) → let open RelTyp (rel ρ≈ρ′) in RelExp t ρ t′ ρ′ (El∞ T≈T′)

_⊨_∶_ : Ctxs → Exp → Typ → Set
Γ ⊨ t ∶ T = Γ ⊨ t ≈ t ∶ T


record RelSubsts σ ρ δ ρ′ (R : Evs) : Set where
  field
    ⟦σ⟧  : Envs
    ⟦δ⟧  : Envs
    ↘⟦σ⟧ : ⟦ σ ⟧s ρ ↘ ⟦σ⟧
    ↘⟦δ⟧ : ⟦ δ ⟧s ρ′ ↘ ⟦δ⟧
    σ≈δ  : ⟦σ⟧ ≈ ⟦δ⟧ ∈ R
    nat  : ∀ (κ : UnMoT) → ⟦ σ ⟧s ρ [ κ ] ↘ ⟦σ⟧ [ κ ]
    nat′ : ∀ (κ : UnMoT) → ⟦ δ ⟧s ρ′ [ κ ] ↘ ⟦δ⟧ [ κ ]


_⊨s_≈_∶_ : Ctxs → Substs → Substs → Ctxs → Set
Γ ⊨s σ ≈ σ′ ∶ Δ = Σ (⊨ Γ) λ ⊨Γ → Σ (⊨ Δ) λ ⊨Δ → ∀ {ρ ρ′} (ρ≈ρ′ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ) → RelSubsts σ ρ σ′ ρ′ ⟦ ⊨Δ ⟧ρ

_⊨s_∶_ : Ctxs → Substs → Ctxs → Set
Γ ⊨s σ ∶ Δ = Γ ⊨s σ ≈ σ ∶ Δ
