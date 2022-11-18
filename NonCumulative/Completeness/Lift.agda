{-# OPTIONS --without-K --safe #-}

open import Level hiding (_⊔_)
open import Axiom.Extensionality.Propositional

-- Semantic judgments for Nat
module NonCumulative.Completeness.Lift (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Data.Nat.Properties

open import Lib
open import NonCumulative.Completeness.LogRel

open import NonCumulative.Semantics.Properties.PER fext


Liftt-cong′ : ∀ {i} n →
              Γ ⊨ T ≈ T′ ∶[ 1 + i ] Se i →
              ----------------------------------------------------
              Γ ⊨ Liftt n (T ↙ i) ≈ Liftt n (T′ ↙ i) ∶[ 1 + n + i ] Se (n + i)
Liftt-cong′ {_} {T} {T′} {i} n (⊨Γ , T≈T′) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 Σ (RelTyp (1 + n + i) (Se (n + i)) ρ (Se (n + i)) ρ′)
                   (λ rel → RelExp (Liftt n (T ↙ i)) ρ (Liftt n (T′ ↙ i)) ρ′ (El (1 + n + i) (RelTyp.T≈T′ rel)))
        helper ρ≈ρ′
          with T≈T′ ρ≈ρ′
        ... | record { ↘⟦T⟧ = ⟦Se⟧ .i ; ↘⟦T′⟧ = ⟦Se⟧ .i ; T≈T′ = U eq _ }
            , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
            rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym eq))
            = record
              { ⟦T⟧   = U (n + i)
              ; ⟦T′⟧  = U (n + i)
              ; ↘⟦T⟧  = ⟦Se⟧ _
              ; ↘⟦T′⟧ = ⟦Se⟧ _
              ; T≈T′  = U refl refl
              }
            , record
              { ⟦t⟧   = Li n i ⟦t⟧
              ; ⟦t′⟧  = Li n i ⟦t′⟧
              ; ↘⟦t⟧  = ⟦Liftt⟧ ↘⟦t⟧
              ; ↘⟦t′⟧ = ⟦Liftt⟧ ↘⟦t′⟧
              ; t≈t′  = L refl
                          (subst (_ ≈ _ ∈_) (sym (𝕌-≡-gen _ (λ l<k → ≤-trans (Li≤ refl l<k) (≤-reflexive refl)))) t≈t′)
                          refl refl
              }

liftt-cong′ : ∀ {i} n →
              Γ ⊨ t ≈ t′ ∶[ i ] T →
              ------------------------------------
              Γ ⊨ liftt n t ≈ liftt n t′ ∶[ n + i ] Liftt n (T ↙ i)
liftt-cong′ {_} {t} {t′} {T} {i} n (⊨Γ , t≈t′) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 Σ (RelTyp (n + i) (Liftt n (T ↙ i)) ρ (Liftt n (T ↙ i)) ρ′)
                 (λ rel → RelExp (liftt n t) ρ (liftt n t′) ρ′ (El (n + i) (RelTyp.T≈T′ rel)))
        helper ρ≈ρ′
          with t≈t′ ρ≈ρ′
        ... | record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
            , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
            = record
              { ⟦T⟧   = Li n i ⟦T⟧
              ; ⟦T′⟧  = Li n i ⟦T′⟧
              ; ↘⟦T⟧  = ⟦Liftt⟧ ↘⟦T⟧
              ; ↘⟦T′⟧ = ⟦Liftt⟧ ↘⟦T′⟧
              ; T≈T′  = L refl (proj₁ (helper′ (λ l<k → Li≤ refl l<k))) refl refl
              }
            , record
              { ⟦t⟧   = li n ⟦t⟧
              ; ⟦t′⟧  = li n ⟦t′⟧
              ; ↘⟦t⟧  = ⟦liftt⟧ ↘⟦t⟧
              ; ↘⟦t′⟧ = ⟦liftt⟧ ↘⟦t′⟧
              ; t≈t′  = record
                { ua    = ⟦t⟧
                ; ub    = ⟦t′⟧
                ; ↘ua   = li↘
                ; ↘ub   = li↘
                ; ua≈ub = proj₂ (helper′ (λ l<k → Li≤ refl l<k))
                }
              }
          where helper′ : (f : ∀ {j} → j < i → j < n + i) →
                          Σ (⟦T⟧ ≈ ⟦T′⟧ ∈ PERDef.𝕌 i (λ j<i → 𝕌-wellfounded _ (f j<i)))
                            λ R → (⟦t⟧ ≈ ⟦t′⟧ ∈ PERDef.El i (λ j<i → 𝕌-wellfounded _ (f j<i)) R)
                helper′ f
                  rewrite 𝕌-wf-gen _ f = T≈T′ , t≈t′


unlift-cong′ : ∀ {i} n →
               Γ ⊨ T ∶[ 1 + i ] Se i →
               Γ ⊨ t ≈ t′ ∶[ n + i ] Liftt n (T ↙ i) →
               --------------------
               Γ ⊨ unlift t ≈ unlift t′ ∶[ i ] T
unlift-cong′ {_} {T} {t} {t′} {i} n (⊨Γ , Trel) (⊨Γ₁ , t≈t′) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 Σ (RelTyp i T ρ T ρ′)
                   (λ rel → RelExp (unlift t) ρ (unlift t′) ρ′ (El i (RelTyp.T≈T′ rel)))
        helper ρ≈ρ′
          with t≈t′ (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ′)
        ... | record { ↘⟦T⟧ = ⟦Liftt⟧ ↘⟦T⟧ ; ↘⟦T′⟧ = ⟦Liftt⟧ ↘⟦T′⟧ ; T≈T′ = L eq T≈T′ _ _ }
            , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
            rewrite 𝕌-wf-gen i (λ l<k → Li≤ {j = n} eq l<k)
            = record
              { ⟦T⟧   = _
              ; ⟦T′⟧  = _
              ; ↘⟦T⟧  = ↘⟦T⟧
              ; ↘⟦T′⟧ = ↘⟦T′⟧
              ; T≈T′  = T≈T′
              }
            , record
              { ⟦t⟧   = ua
              ; ⟦t′⟧  = ub
              ; ↘⟦t⟧  = ⟦unlift⟧ ↘⟦t⟧ ↘ua
              ; ↘⟦t′⟧ = ⟦unlift⟧ ↘⟦t′⟧ ↘ub
              ; t≈t′  = ua≈ub
              }
          where open Unli t≈t′


-- Liftt-[]   : ∀ {i} n →
--              Γ ⊨s σ ∶ Δ →
--              Δ ⊨ T ∶[ 1 + i ] Se i →
--              ----------------------------------------------------
--              Γ ⊨ Liftt n (T ↙ i) [ σ ] ≈ Liftt n (T [ σ ] ↙ i) ∶[ 1 + n + i ] Se (n + i)

-- liftt-[]   : ∀ {i} n →
--              Γ ⊨s σ ∶ Δ →
--              Δ ⊨ T ∶[ suc i ] Se i →
--              Δ ⊨ t ∶[ i ] T →
--              --------------------------------------
--              Γ ⊨ liftt n t [ σ ] ≈ liftt n (t [ σ ]) ∶[ n + i ] Liftt n (T ↙ i) [ σ ]
-- unlift-[]  : ∀ {i} n →
--              Δ ⊨ T ∶[ suc i ] Se i →
--              Γ ⊨s σ ∶ Δ →
--              Δ ⊨ t ∶[ n + i ] Liftt n (T ↙ i) →
--              ---------------------------------------
--              Γ ⊨ unlift t [ σ ] ≈ unlift (t [ σ ]) ∶[ i ] T [ σ ]

-- L-β        : ∀ {i} n →
--              Γ ⊨ t ∶[ i ] T →
--              -----------------------------
--              Γ ⊨ unlift (liftt n t) ≈ t ∶[ i ] T
-- L-η        : ∀ {i} n →
--              Γ ⊨ T ∶[ suc i ] Se i →
--              Γ ⊨ t ∶[ n + i ] Liftt n (T ↙ i) →
--              -----------------------------
--              Γ ⊨ t ≈ liftt n (unlift t) ∶[ n + i ] Liftt n (T ↙ i)
