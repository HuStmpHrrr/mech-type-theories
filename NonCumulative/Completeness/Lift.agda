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
        ...  | record { ↘⟦T⟧ = ⟦Se⟧ .i ; ↘⟦T′⟧ = ⟦Se⟧ .i ; T≈T′ = U eq _ }
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
        ...  | record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
             , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
             = record
               { ⟦T⟧   = Li n i ⟦T⟧
               ; ⟦T′⟧  = Li n i ⟦T′⟧
               ; ↘⟦T⟧  = ⟦Liftt⟧ ↘⟦T⟧
               ; ↘⟦T′⟧ = ⟦Liftt⟧ ↘⟦T′⟧
               ; T≈T′  = proj₁ Lb
               }
             , record
               { ⟦t⟧   = li n ⟦t⟧
               ; ⟦t′⟧  = li n ⟦t′⟧
               ; ↘⟦t⟧  = ⟦liftt⟧ ↘⟦t⟧
               ; ↘⟦t′⟧ = ⟦liftt⟧ ↘⟦t′⟧
               ; t≈t′  = proj₂ Lb
               }
          where li-rel : li n ⟦t⟧ ≈ li n ⟦t′⟧ ∈ Unli (El i T≈T′)
                li-rel = record
                  { ua    = ⟦t⟧
                  ; ub    = ⟦t′⟧
                  ; ↘ua   = li↘
                  ; ↘ub   = li↘
                  ; ua≈ub = t≈t′
                  }

                Lb = L-bundle T≈T′ li-rel refl


unlift-cong′ : ∀ {i} n →
               Γ ⊨ t ≈ t′ ∶[ n + i ] Liftt n (T ↙ i) →
               --------------------
               Γ ⊨ unlift t ≈ unlift t′ ∶[ i ] T
unlift-cong′ {_} {t} {t′} {T} {i} n (⊨Γ , t≈t′) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 Σ (RelTyp i T ρ T ρ′)
                   (λ rel → RelExp (unlift t) ρ (unlift t′) ρ′ (El i (RelTyp.T≈T′ rel)))
        helper ρ≈ρ′
          with t≈t′ ρ≈ρ′
        ...  | record { ↘⟦T⟧ = ⟦Liftt⟧ ↘⟦T⟧ ; ↘⟦T′⟧ = ⟦Liftt⟧ ↘⟦T′⟧ ; T≈T′ = L eq T≈T′ _ _ }
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


Liftt-[]′ : ∀ {i} n →
            Γ ⊨s σ ∶ Δ →
            Δ ⊨ T ∶[ 1 + i ] Se i →
            ----------------------------------------------------
            Γ ⊨ Liftt n (T ↙ i) [ σ ] ≈ Liftt n (T [ σ ] ↙ i) ∶[ 1 + n + i ] Se (n + i)
Liftt-[]′ {_} {σ} {_} {T} {i} n (⊨Γ , ⊨Δ , ⊨σ) (⊨Δ₁ , ⊨T) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 Σ (RelTyp (1 + n + i) (Se (n + i)) ρ (Se (n + i)) ρ′)
                   (λ rel → RelExp (Liftt n (T ↙ i) [ σ ]) ρ (Liftt n (T [ σ ] ↙ i)) ρ′ (El (1 + n + i) (RelTyp.T≈T′ rel)))
        helper ρ≈ρ′
          with ⊨σ ρ≈ρ′
        ...  | record { ⟦σ⟧ = ⟦σ⟧ ; ⟦δ⟧ = ⟦δ⟧ ; ↘⟦σ⟧ = ↘⟦σ⟧ ; ↘⟦δ⟧ = ↘⟦δ⟧ ; σ≈δ = σ≈δ }
             with ⊨T (⊨-irrel ⊨Δ ⊨Δ₁ σ≈δ)
        ...     | record { ↘⟦T⟧ = ⟦Se⟧ .i ; ↘⟦T′⟧ = ⟦Se⟧ .i ; T≈T′ = U eq _ }
                , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
                rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym eq))
                = record
                  { ⟦T⟧   = U (n + i)
                  ; ⟦T′⟧  = U (n + i)
                  ; ↘⟦T⟧  = ⟦Se⟧ (n + i)
                  ; ↘⟦T′⟧ = ⟦Se⟧ (n + i)
                  ; T≈T′  = U refl refl
                  }
                , record
                  { ⟦t⟧   = Li n i ⟦t⟧
                  ; ⟦t′⟧  = Li n i ⟦t′⟧
                  ; ↘⟦t⟧  = ⟦[]⟧ ↘⟦σ⟧ (⟦Liftt⟧ ↘⟦t⟧)
                  ; ↘⟦t′⟧ = ⟦Liftt⟧ (⟦[]⟧ ↘⟦δ⟧ ↘⟦t′⟧)
                  ; t≈t′  = subst (Li _ _ _ ≈ Li _ _ _ ∈_) (sym (𝕌-≡-gen _ (λ lt → (≤-trans lt (≤-reflexive refl))))) (L-𝕌 t≈t′ refl)
                  }


liftt-[]′ : ∀ {i} n →
            Γ ⊨s σ ∶ Δ →
            Δ ⊨ t ∶[ i ] T →
            --------------------------------------
            Γ ⊨ liftt n t [ σ ] ≈ liftt n (t [ σ ]) ∶[ n + i ] Liftt n (T ↙ i) [ σ ]
liftt-[]′ {_} {σ} {_} {t} {T} {i} n (⊨Γ , ⊨Δ , ⊨σ) (⊨Δ₂ , ⊨t) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 Σ (RelTyp (n + i) (Liftt n (T ↙ i) [ σ ]) ρ (Liftt n (T ↙ i) [ σ ]) ρ′)
                 (λ rel → RelExp (liftt n t [ σ ]) ρ (liftt n (t [ σ ])) ρ′ (El (n + i) (RelTyp.T≈T′ rel)))
        helper ρ≈ρ′
          with ⊨σ ρ≈ρ′
        ...  | record { ⟦σ⟧ = ⟦σ⟧ ; ⟦δ⟧ = ⟦δ⟧ ; ↘⟦σ⟧ = ↘⟦σ⟧ ; ↘⟦δ⟧ = ↘⟦δ⟧ ; σ≈δ = σ≈δ }
             with ⊨t (⊨-irrel ⊨Δ ⊨Δ₂ σ≈δ)
        ...     | record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
                , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
                = record
                  { ⟦T⟧   = Li n i ⟦T⟧
                  ; ⟦T′⟧  = Li n i ⟦T′⟧
                  ; ↘⟦T⟧  = ⟦[]⟧ ↘⟦σ⟧ (⟦Liftt⟧ ↘⟦T⟧)
                  ; ↘⟦T′⟧ = ⟦[]⟧ ↘⟦δ⟧ (⟦Liftt⟧ ↘⟦T′⟧)
                  ; T≈T′  = proj₁ Lb
                  }
                , record
                  { ⟦t⟧   = li n ⟦t⟧
                  ; ⟦t′⟧  = li n ⟦t′⟧
                  ; ↘⟦t⟧  = ⟦[]⟧ ↘⟦σ⟧ (⟦liftt⟧ ↘⟦t⟧)
                  ; ↘⟦t′⟧ = ⟦liftt⟧ (⟦[]⟧ ↘⟦δ⟧ ↘⟦t′⟧)
                  ; t≈t′  = proj₂ Lb
                  }
          where li-rel : li n ⟦t⟧ ≈ li n ⟦t′⟧ ∈ Unli (El i T≈T′)
                li-rel = record
                  { ua    = ⟦t⟧
                  ; ub    = ⟦t′⟧
                  ; ↘ua   = li↘
                  ; ↘ub   = li↘
                  ; ua≈ub = t≈t′
                  }

                Lb = L-bundle T≈T′ li-rel refl


unlift-[]′ : ∀ {i} n →
             Γ ⊨s σ ∶ Δ →
             Δ ⊨ t ∶[ n + i ] Liftt n (T ↙ i) →
             ---------------------------------------
             Γ ⊨ unlift t [ σ ] ≈ unlift (t [ σ ]) ∶[ i ] T [ σ ]
unlift-[]′ {_} {σ} {_} {t} {T} {i} n (⊨Γ , ⊨Δ , ⊨σ) (⊨Δ₂ , ⊨t) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 Σ (RelTyp i (T [ σ ]) ρ (T [ σ ]) ρ′)
                   (λ rel → RelExp (unlift t [ σ ]) ρ (unlift (t [ σ ])) ρ′ (El i (RelTyp.T≈T′ rel)))
        helper ρ≈ρ′
          with ⊨σ ρ≈ρ′
        ...  | record { ⟦σ⟧ = ⟦σ⟧ ; ⟦δ⟧ = ⟦δ⟧ ; ↘⟦σ⟧ = ↘⟦σ⟧ ; ↘⟦δ⟧ = ↘⟦δ⟧ ; σ≈δ = σ≈δ }
             with ⊨t (⊨-irrel ⊨Δ ⊨Δ₂ σ≈δ)
        ...     | record { ↘⟦T⟧ = ⟦Liftt⟧ ↘⟦T⟧ ; ↘⟦T′⟧ = ⟦Liftt⟧ ↘⟦T′⟧ ; T≈T′ = L eq T≈T′ _ _ }
                , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
                rewrite 𝕌-wf-gen i (λ l<k → Li≤ {j = n} eq l<k)
                = record
                  { ⟦T⟧   = _
                  ; ⟦T′⟧  = _
                  ; ↘⟦T⟧  = ⟦[]⟧ ↘⟦σ⟧ ↘⟦T⟧
                  ; ↘⟦T′⟧ = ⟦[]⟧ ↘⟦δ⟧ ↘⟦T′⟧
                  ; T≈T′  = T≈T′
                  }
                , record
                  { ⟦t⟧   = ua
                  ; ⟦t′⟧  = ub
                  ; ↘⟦t⟧  = ⟦[]⟧ ↘⟦σ⟧ (⟦unlift⟧ ↘⟦t⟧ ↘ua)
                  ; ↘⟦t′⟧ = ⟦unlift⟧ (⟦[]⟧ ↘⟦δ⟧ ↘⟦t′⟧) ↘ub
                  ; t≈t′  = ua≈ub
                  }
          where open Unli t≈t′


L-β′ : ∀ {i} n →
       Γ ⊨ t ∶[ i ] T →
       -----------------------------
       Γ ⊨ unlift (liftt n t) ≈ t ∶[ i ] T
L-β′ {_} {t} {T} {i} n (⊨Γ , ⊨t) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 Σ (RelTyp i T ρ T ρ′)
                   (λ rel → RelExp (unlift (liftt n t)) ρ t ρ′ (El i (RelTyp.T≈T′ rel)))
        helper ρ≈ρ′
          with ⊨t ρ≈ρ′
        ...  | Trel
             , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
             = Trel
             , record
               { ⟦t⟧   = ⟦t⟧
               ; ⟦t′⟧  = ⟦t′⟧
               ; ↘⟦t⟧  = ⟦unlift⟧ (⟦liftt⟧ ↘⟦t⟧) li↘
               ; ↘⟦t′⟧ = ↘⟦t′⟧
               ; t≈t′  = t≈t′
               }


L-η′ : ∀ {i} n →
       Γ ⊨ t ∶[ n + i ] Liftt n (T ↙ i) →
       -----------------------------
       Γ ⊨ t ≈ liftt n (unlift t) ∶[ n + i ] Liftt n (T ↙ i)
L-η′ {_} {t} {T} {i} n (⊨Γ , ⊨t) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 Σ (RelTyp (n + i) (Liftt n (T ↙ i)) ρ (Liftt n (T ↙ i)) ρ′)
                   (λ rel → RelExp t ρ (liftt n (unlift t)) ρ′ (El (n + i) (RelTyp.T≈T′ rel)))
        helper ρ≈ρ′
          with ⊨t ρ≈ρ′
        ... | record { ↘⟦T⟧ = ⟦Liftt⟧ ↘⟦T⟧ ; ↘⟦T′⟧ = ⟦Liftt⟧ ↘⟦T′⟧ ; T≈T′ = L eq T≈T′ _ _ }
            , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
            rewrite 𝕌-wf-gen i (λ l<k → Li≤ {j = n} eq l<k)
            = record
              { ⟦T⟧   = Li n i _
              ; ⟦T′⟧  = Li n i _
              ; ↘⟦T⟧  = ⟦Liftt⟧ ↘⟦T⟧
              ; ↘⟦T′⟧ = ⟦Liftt⟧ ↘⟦T′⟧
              ; T≈T′  = proj₁ Lb
              }
            , record
              { ⟦t⟧   = ⟦t⟧
              ; ⟦t′⟧  = li n ub
              ; ↘⟦t⟧  = ↘⟦t⟧
              ; ↘⟦t′⟧ = ⟦liftt⟧ (⟦unlift⟧ ↘⟦t′⟧ ↘ub)
              ; t≈t′  = proj₂ Lb
              }
          where open Unli t≈t′
                li-rel : ⟦t⟧ ≈ li n ub ∈ Unli (El i T≈T′)
                li-rel = record
                  { ua    = ua
                  ; ub    = ub
                  ; ↘ua   = ↘ua
                  ; ↘ub   = li↘
                  ; ua≈ub = ua≈ub
                  }

                Lb = L-bundle T≈T′ li-rel eq
