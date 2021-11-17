{-# OPTIONS --without-K --safe #-}

open import Level using ()
open import Axiom.Extensionality.Propositional

module kMLTT.Completeness.Contexts (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import kMLTT.Completeness.LogRel

open import kMLTT.Semantics.Properties.PER fext


[]-≈′ : ⊨ [] ∷ [] ≈ [] ∷ []
[]-≈′ = []-≈


κ-cong′ : ⊨ Γ ≈ Δ →
          -------------------
          ⊨ [] ∷⁺ Γ ≈ [] ∷⁺ Δ
κ-cong′ = κ-cong


∷-cong′ : ∀ {i} →
          ⊨ Γ ≈ Δ →
          Γ ⊨ T ≈ T′ ∶ Se i →
          ----------------
          ⊨ T ∺ Γ ≈ T′ ∺ Δ
∷-cong′ {T = T} {T′} Γ≈Δ (⊨Γ , T≈T′) = ∷-cong Γ≈Δ helper
  where helper : ρ ≈ ρ′ ∈ ⟦ Γ≈Δ ⟧ρ → RelTyp T ρ T′ ρ′
        helper ρ≈ρ′
          with ⟦⟧ρ-one-sided Γ≈Δ ⊨Γ ρ≈ρ′
        ...  | ρ≈ρ′₁
             with T≈T′ ρ≈ρ′₁
        ... | record { ↘⟦T⟧ = ⟦Se⟧ ._ ; ↘⟦T′⟧ = ⟦Se⟧ ._ ; T≈T′ = i , U j<i eq }
            , res
            rewrite 𝕌-wellfounded-≡-𝕌 _ j<i = RelExp⇒RepTyp′ res
