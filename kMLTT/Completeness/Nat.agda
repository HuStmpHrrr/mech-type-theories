{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Completeness.Nat (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Data.Nat.Properties

open import Lib
open import kMLTT.Completeness.LogRel

open import kMLTT.Semantics.Properties.Domain fext
open import kMLTT.Semantics.Properties.PER fext


N-[]′ : ∀ i →
        Γ ⊨s σ ∶ Δ →
        -----------------------
        Γ ⊨ N [ σ ] ≈ N ∶ Se i
N-[]′ {_} {σ} i (⊨Γ , ⊨Δ , ⊨σ) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp (Se i) ρ (Se i) ρ′) (λ rel → RelExp (N [ σ ]) ρ N ρ′ (El∞ (RelTyp.T≈T′ rel)))
        helper ρ≈ρ′ = record
                        { ⟦T⟧   = U i
                        ; ⟦T′⟧  = U i
                        ; ↘⟦T⟧  = ⟦Se⟧ _
                        ; ↘⟦T′⟧ = ⟦Se⟧ _
                        ; T≈T′  = -, U′ ≤-refl
                        }
                    , record
                        { ⟦t⟧   = N
                        ; ⟦t′⟧  = N
                        ; ↘⟦t⟧  = ⟦[]⟧ σ.↘⟦σ⟧ ⟦N⟧
                        ; ↘⟦t′⟧ = ⟦N⟧
                        ; t≈t′  = PERDef.N
                        }
          where module σ = RelSubsts (⊨σ ρ≈ρ′)


ze-[]′ : Γ ⊨s σ ∶ Δ →
         ----------------------
         Γ ⊨ ze [ σ ] ≈ ze ∶ N
ze-[]′ {_} {σ} (⊨Γ , ⊨Δ , ⊨σ) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp N ρ N ρ′) (λ rel → RelExp (ze [ σ ]) ρ ze ρ′ (El∞ (RelTyp.T≈T′ rel)))
        helper ρ≈ρ′ = record
                        { ⟦T⟧   = N
                        ; ⟦T′⟧  = N
                        ; ↘⟦T⟧  = ⟦N⟧
                        ; ↘⟦T′⟧ = ⟦N⟧
                        ; T≈T′  = 0 , N
                        }
                    , record
                        { ⟦t⟧   = ze
                        ; ⟦t′⟧  = ze
                        ; ↘⟦t⟧  = ⟦[]⟧ σ.↘⟦σ⟧ ⟦ze⟧
                        ; ↘⟦t′⟧ = ⟦ze⟧
                        ; t≈t′  = ze
                        }
          where module σ = RelSubsts (⊨σ ρ≈ρ′)


su-[]′ : Γ ⊨s σ ∶ Δ →
         Δ ⊨ t ∶ N →
         ----------------------------------
         Γ ⊨ su t [ σ ] ≈ su (t [ σ ]) ∶ N
su-[]′ {_} {σ} {_} {t} (⊨Γ , ⊨Δ , ⊨σ) (⊨Δ₁ , ⊨t) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp N ρ N ρ′) (λ rel → RelExp (su t [ σ ]) ρ (su (t [ σ ])) ρ′ (El∞ (RelTyp.T≈T′ rel)))
        helper {ρ} {ρ′} ρ≈ρ′ = help
          where module σ = RelSubsts (⊨σ ρ≈ρ′)
                help : Σ (RelTyp N ρ N ρ′) (λ rel → RelExp (su t [ σ ]) ρ (su (t [ σ ])) ρ′ (El∞ (RelTyp.T≈T′ rel)))
                help
                  with ⊨t (⊨-irrel ⊨Δ ⊨Δ₁ σ.σ≈δ)
                ...  | record { ↘⟦T⟧ = ⟦N⟧ ; ↘⟦T′⟧ = ⟦N⟧ ; T≈T′ = _ , N }
                     , re = record
                              { ⟦T⟧   = N
                              ; ⟦T′⟧  = N
                              ; ↘⟦T⟧  = ⟦N⟧
                              ; ↘⟦T′⟧ = ⟦N⟧
                              ; T≈T′  = 0 , N
                              }
                          , record
                              { ⟦t⟧   = su re.⟦t⟧
                              ; ⟦t′⟧  = su re.⟦t′⟧
                              ; ↘⟦t⟧  = ⟦[]⟧ σ.↘⟦σ⟧ (⟦su⟧ re.↘⟦t⟧)
                              ; ↘⟦t′⟧ = ⟦su⟧ (⟦[]⟧ σ.↘⟦δ⟧ re.↘⟦t′⟧)
                              ; t≈t′  = su re.t≈t′
                              }
                  where module re = RelExp re

-- rec-[]     : ∀ {i} →
--              Γ ⊨s σ ∶ Δ →
--              N ∺ Δ ⊨ T ∶ Se i →
--              Δ ⊨ s ∶ T [| ze ] →
--              T ∺ N ∺ Δ ⊨ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
--              Δ ⊨ t ∶ N →
--              -----------------------------------------------------------------------------------------------
--              Γ ⊨ rec T s r t [ σ ] ≈ rec (T [ q σ ]) (s [ σ ]) (r [ q (q σ) ]) (t [ σ ]) ∶ T [ σ , t [ σ ] ]
-- ze-≈       : ⊨ Γ →
--              ----------------
--              Γ ⊨ ze ≈ ze ∶ N
-- su-cong    : Γ ⊨ t ≈ t′ ∶ N →
--              --------- ------------
--              Γ ⊨ su t ≈ su t′ ∶ N
-- rec-cong   : ∀ {i} →
--              N ∺ Γ ⊨ T ≈ T′ ∶ Se i →
--              Γ ⊨ s ≈ s′ ∶ T [ I , ze ] →
--              T ∺ N ∺ Γ ⊨ r ≈ r′ ∶ T [ (wk ∘ wk) , su (v 1) ] →
--              Γ ⊨ t ≈ t′ ∶ N →
--              --------------------------------------------
--              Γ ⊨ rec T s r t ≈ rec T′ s′ r′ t′ ∶ T [| t ]
-- rec-β-ze   : ∀ {i} →
--              N ∺ Γ ⊨ T ∶ Se i →
--              Γ ⊨ s ∶ T [| ze ] →
--              T ∺ N ∺ Γ ⊨ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
--              ---------------------------------------------
--              Γ ⊨ rec T s r ze ≈ s ∶ T [| ze ]
-- rec-β-su   : ∀ {i} →
--              N ∺ Γ ⊨ T ∶ Se i →
--              Γ ⊨ s ∶ T [| ze ] →
--              T ∺ N ∺ Γ ⊨ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
--              Γ ⊨ t ∶ N →
--              -----------------------------------------------------------------
--              Γ ⊨ rec T s r (su t) ≈ r [ (I , t) , rec T s r t ] ∶ T [| su t ]
