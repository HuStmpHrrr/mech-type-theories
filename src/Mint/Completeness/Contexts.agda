{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

-- Semantic judgments for context stacks
module Mint.Completeness.Contexts (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Mint.Completeness.LogRel

open import Mint.Semantics.Properties.PER fext


[]-≈′ : ⊨ [] ∷ [] ≈ [] ∷ []
[]-≈′ = []-≈


κ-cong′ : ⊨ Γ ≈ Δ →
          -------------------
          ⊨ [] ∷⁺ Γ ≈ [] ∷⁺ Δ
κ-cong′ = κ-cong

-- ∺-cong-helper is separately defined to be used in Mint.Completeness.Substitutions
∺-cong-helper : ∀ {i} →
                Γ ⊨ T ≈ T′ ∶ Se i →
                (Γ≈Δ : ⊨ Γ ≈ Δ) →
                ρ ≈ ρ′ ∈ ⟦ Γ≈Δ ⟧ρ →
                RelTyp i T ρ T′ ρ′
∺-cong-helper (⊨Γ₁ , i , T≈T′) Γ≈Δ ρ≈ρ′
  with ρ≈ρ′₁ ← ⟦⟧ρ-one-sided Γ≈Δ ⊨Γ₁ ρ≈ρ′
     with T≈T′ ρ≈ρ′₁
...     | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U j<i _ }
        , res
        rewrite 𝕌-wellfounded-≡-𝕌 _ j<i = RelExp⇒RepTyp res


∺-cong′ : ∀ {i} →
          ⊨ Γ ≈ Δ →
          Γ ⊨ T ≈ T′ ∶ Se i →
          ----------------
          ⊨ T ∺ Γ ≈ T′ ∺ Δ
∺-cong′ {T = T} {T′} Γ≈Δ ⊨T = ∺-cong Γ≈Δ (∺-cong-helper ⊨T Γ≈Δ)
