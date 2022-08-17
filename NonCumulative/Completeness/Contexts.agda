{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Semantic judgments for context stacks
module NonCumulative.Completeness.Contexts (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Lib
open import Data.Nat.Properties
open import NonCumulative.Completeness.LogRel

open import NonCumulative.Semantics.Properties.PER fext


[]-≈′ : ⊨ [] ≈ []
[]-≈′ = []-≈


-- ∷-cong-helper is separately defined to be used in NonCumulative.Completeness.Substitutions
∷-cong-helper : ∀ {i} →
                Γ ⊨ T ≈ T′ ∶[ 1 + i ] Se i →
                (Γ≈Δ : ⊨ Γ ≈ Δ) →
                ρ ≈ ρ′ ∈ ⟦ Γ≈Δ ⟧ρ →
                RelTyp i T ρ T′ ρ′
∷-cong-helper {i = i} (⊨Γ₁ , T≈T′) Γ≈Δ ρ≈ρ′
  with ρ≈ρ′₁ ← ⟦⟧ρ-one-sided Γ≈Δ ⊨Γ₁ ρ≈ρ′
     with T≈T′ ρ≈ρ′₁
...     | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U eq _ }
        , res
        rewrite 𝕌-wellfounded-≡-𝕌 (1 + i) (≤-reflexive (sym eq)) = RelExp⇒RepTyp res


∷-cong′ : ∀ {i} →
          ⊨ Γ ≈ Δ →
          Γ ⊨ T ≈ T′ ∶[ 1 + i ] Se i →
          ----------------------------
          ⊨ (T ↙ i) ∷ Γ ≈ (T′ ↙ i) ∷ Δ
∷-cong′ {T = T} {T′} Γ≈Δ ⊨T = ∷-cong Γ≈Δ (∷-cong-helper ⊨T Γ≈Δ) refl
