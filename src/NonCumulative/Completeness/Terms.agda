{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Semantic judgments for other term related rules
module NonCumulative.Completeness.Terms (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Lib
open import Data.Nat.Properties
open import NonCumulative.Completeness.LogRel

open import NonCumulative.Semantics.Properties.PER fext


⊨-lookup-gen : ∀ {x i j}
               (Γ≈Δ : ⊨ Γ ≈ Δ) →
               x ∶[ i ] T ∈! Γ →
               x ∶[ j ] T′ ∈! Δ →
               ρ ≈ ρ′ ∈ ⟦ Γ≈Δ ⟧ρ →
               -----------------------------------------------------------
               Σ (RelTyp i T ρ T′ ρ′)
               λ rel → RelExp (v x) ρ (v x) ρ′ (El _ (RelTyp.T≈T′ rel))
⊨-lookup-gen (∷-cong _ rel refl) here here (ρ≈ρ′ , ρ0≈ρ′0)
  = record
      { RelTyp (rel ρ≈ρ′)
      ; ↘⟦T⟧  = ⟦[]⟧ ⟦wk⟧ ↘⟦T⟧
      ; ↘⟦T′⟧ = ⟦[]⟧ ⟦wk⟧ ↘⟦T′⟧
      }
  , record
      { ↘⟦t⟧  = ⟦v⟧ 0
      ; ↘⟦t′⟧ = ⟦v⟧ 0
      ; t≈t′  = ρ0≈ρ′0
      }
  where open RelTyp (rel ρ≈ρ′)
⊨-lookup-gen (∷-cong Γ≈Δ rel refl) (there T∈Γ) (there T′∈Δ) (ρ≈ρ′ , ρ0≈ρ′0)
  with rT , record { ↘⟦t⟧ = ⟦v⟧ _ ; ↘⟦t′⟧ = ⟦v⟧ _ ; t≈t′ = t≈t′ } ← ⊨-lookup-gen Γ≈Δ T∈Γ T′∈Δ ρ≈ρ′
  = record
  { RelTyp rT
  ; ↘⟦T⟧  = ⟦[]⟧ ⟦wk⟧ ↘⟦T⟧
  ; ↘⟦T′⟧ = ⟦[]⟧ ⟦wk⟧ ↘⟦T′⟧ }
  , record
  { ↘⟦t⟧  = ⟦v⟧ _
  ; ↘⟦t′⟧ = ⟦v⟧ _
  ; t≈t′  = t≈t′
  }
  where open RelTyp rT


⊨-lookup : ∀ {x i}
           (⊨Γ : ⊨ Γ) →
           x ∶[ i ] T ∈! Γ →
           ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
           -------------------------------------------------------
           Σ (RelTyp i T ρ T ρ′)
           λ rel → RelExp (v x) ρ (v x) ρ′ (El _ (RelTyp.T≈T′ rel))
⊨-lookup ⊨Γ T∈Γ = ⊨-lookup-gen ⊨Γ T∈Γ T∈Γ


v-≈′ : ∀ {x i} →
       ⊨ Γ →
       x ∶[ i ] T ∈! Γ →
       -------------------
       Γ ⊨ v x ≈ v x ∶[ i ] T
v-≈′ ⊨Γ T∈Γ = ⊨Γ , ⊨-lookup ⊨Γ T∈Γ


-- This judgment is slightly more difficult than it appears to be. The difficulty
-- comes from the asymmetry of σ and σ′. Though they are given as equivalent in the
-- premise, in the conclusion, only σ is used. That implies that for two related ρ and
-- ρ′, we must derive ⟦ T[σ] ⟧(ρ) ≈ ⟦ T[σ] ⟧(ρ′) which evaluates to ⟦ T ⟧(⟦ σ ⟧(ρ)) ≈ ⟦ T ⟧(⟦ σ ⟧(ρ′)).
-- To arrive at this conclusion, we must first show ⟦ σ ⟧(ρ) ≈ ⟦ σ ⟧(ρ′). This is
-- achieved by the followin chain of transitivity:
--
-- ⟦ σ ⟧(ρ)  ≈ ⟦ σ′ ⟧(ρ)         ρ ≈ ρ due to PER properties
-- ⟦ σ′ ⟧(ρ) ≈ ⟦ σ ⟧(ρ′)         ρ′ ≈ ρ due to symmetry
--
-- Hence we conclude ⟦ σ ⟧(ρ) ≈ ⟦ σ ⟧(ρ′). Then we conclude the goal by applying some
-- proof-irrelevant lemmas to handle the proof relevance nature and arrive at our goal.
--
-- This pattern frequently shows up in other lemmas that has asymmetry.
[]-cong′ : ∀ {i} →
           Δ ⊨ t ≈ t′ ∶[ i ] T →
           Γ ⊨s σ ≈ σ′ ∶ Δ →
           ---------------------------------
           Γ ⊨ t [ σ ] ≈ t′ [ σ′ ] ∶[ i ] T [ σ ]
[]-cong′ {_} {t} {t′} {T} {_} {σ} {σ′} (⊨Δ , t≈t′) (⊨Γ , ⊨Δ₁ , σ≈σ′) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 ----------------------------------------------------------------------
                 Σ (RelTyp _ (T [ σ ]) ρ (T [ σ ]) ρ′)
                 λ rel → RelExp (t [ σ ]) ρ (t′ [ σ′ ]) ρ′ (El _ (RelTyp.T≈T′ rel))
        helper {ρ} {ρ′} ρ≈ρ′
          with ρ≈ρ ← ⟦⟧ρ-refl ⊨Γ ⊨Γ ρ≈ρ′
             | ρ′≈ρ ← ⟦⟧ρ-sym′ ⊨Γ ρ≈ρ′
             with σ≈σ′ ρ≈ρ
                | σ≈σ′ ρ′≈ρ
                | σ≈σ′ ρ≈ρ′
        ...     | record { ⟦σ⟧ = ⟦σ⟧  ; ↘⟦σ⟧ = ↘⟦σ⟧  ; ↘⟦δ⟧ = ↘⟦σ′⟧  ; σ≈δ = ⟦σ≈σ′⟧ }
                | record { ⟦σ⟧ = ⟦σ⟧′ ; ↘⟦σ⟧ = ↘⟦σ⟧′ ; ↘⟦δ⟧ = ↘⟦σ′⟧′ ; σ≈δ = ⟦σ≈σ′⟧₁ }
                | record { ⟦σ⟧ = ⟦σ⟧″ ; ↘⟦σ⟧ = ↘⟦σ⟧″ ; ↘⟦δ⟧ = ↘⟦σ′⟧″ ; σ≈δ = ⟦σ≈σ′⟧₂ }
                rewrite ⟦⟧s-det ↘⟦σ′⟧ ↘⟦σ′⟧′
                      | ⟦⟧s-det ↘⟦σ⟧″ ↘⟦σ⟧
                with σ≈σ ← ⟦⟧ρ-trans′ ⊨Δ₁ ⟦σ≈σ′⟧ (⟦⟧ρ-sym′ ⊨Δ₁ ⟦σ≈σ′⟧₁) = help
          where help : Σ (RelTyp _ (T [ σ ]) ρ (T [ σ ]) ρ′)
                       λ rel → RelExp (t [ σ ]) ρ (t′ [ σ′ ]) ρ′ (El _ (RelTyp.T≈T′ rel))
                help
                  with t≈t′ (⊨-irrel ⊨Δ₁ ⊨Δ σ≈σ)
                     | t≈t′ (⊨-irrel ⊨Δ₁ ⊨Δ ⟦σ≈σ′⟧₂)
                ...  | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ } , _
                     | record { ↘⟦T⟧ = ↘⟦T⟧′ ; T≈T′ = T≈T′₁ } , re
                    rewrite ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧ = record
                                                  { ↘⟦T⟧  = ⟦[]⟧ ↘⟦σ⟧ ↘⟦T⟧
                                                  ; ↘⟦T′⟧ = ⟦[]⟧ ↘⟦σ⟧′ ↘⟦T′⟧
                                                  ; T≈T′  = T≈T′
                                                  }
                                              , record
                                                  { ↘⟦t⟧  = ⟦[]⟧ ↘⟦σ⟧ ↘⟦t⟧
                                                  ; ↘⟦t′⟧ = ⟦[]⟧ ↘⟦σ′⟧″ ↘⟦t′⟧
                                                  ; t≈t′  = El-one-sided T≈T′₁ T≈T′ re.t≈t′
                                                  }
                  where module re = RelExp re
                        open re


[I]′ : ∀ {i} →
       Γ ⊨ t ∶[ i ] T →
       --------------------
       Γ ⊨ t [ I ] ≈ t ∶[ i ] T
[I]′ {_} {t} {T} (⊨Γ , ⊨t) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 -----------------------------------------------------------
                 Σ (RelTyp _ T ρ T ρ′)
                 λ rel → RelExp (t [ I ]) ρ t ρ′ (El _ (RelTyp.T≈T′ rel))
        helper ρ≈ρ′
          with rt , re ← ⊨t ρ≈ρ′ = rt
                                 , record
                                     { RelExp re
                                     ; ↘⟦t⟧  = ⟦[]⟧ ⟦I⟧ ↘⟦t⟧
                                     }
          where open RelExp re


[wk]′ : ∀ {x i j} →
        ⊨ (S ↙ j) ∷ Γ →
        x ∶[ i ] T ∈! Γ →
        -----------------------------------------------
        (S ↙ j) ∷ Γ ⊨ v x [ wk ] ≈ v (1 + x) ∶[ i ] T [ wk ]
[wk]′ {S} {_} {T} {x} ⊨SΓ@(∷-cong ⊨Γ _ _) T∈Γ = ⊨SΓ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨SΓ ⟧ρ →
                 -------------------------------------------------------------------------
                 Σ (RelTyp _ (T [ wk ]) ρ (sub T wk) ρ′)
                 λ rel → RelExp (v x [ wk ]) ρ (v (1 + x)) ρ′ (El _ (RelTyp.T≈T′ rel))
        helper {ρ} {ρ′} (ρ≈ρ′ , ρ0≈ρ′0)
          with ⊨-lookup ⊨Γ T∈Γ ρ≈ρ′
        ...  | rt
             , record { ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ⟦v⟧ _ ; t≈t′ = t≈t′ }
             = record
                 { RelTyp rt
                 ; ↘⟦T⟧  = ⟦[]⟧ ⟦wk⟧ ↘⟦T⟧
                 ; ↘⟦T′⟧ = ⟦[]⟧ ⟦wk⟧ ↘⟦T′⟧
                 }
             , record
                 { ↘⟦t⟧  = ⟦[]⟧ ⟦wk⟧ ↘⟦t⟧
                 ; ↘⟦t′⟧ = ⟦v⟧ _
                 ; t≈t′  = t≈t′
                 }
          where open RelTyp rt


[∘]′ : ∀ {i} →
       Γ ⊨s τ ∶ Γ′ →
       Γ′ ⊨s σ ∶ Γ″ →
       Γ″ ⊨ t ∶[ i ] T →
       ---------------------------------------------
       Γ ⊨ t [ σ ∘ τ ] ≈ t [ σ ] [ τ ] ∶[ i ] T [ σ ∘ τ ]
[∘]′ {_} {τ} {_} {σ} {_} {t} {T} (⊨Γ , ⊨Γ′ , ⊨τ) (⊨Γ′₁ , ⊨Γ″ , ⊨σ) (⊨Γ″₁ , ⊨t) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 ----------------------------------------------------------------
                 Σ (RelTyp _ (T [ σ ∘ τ ]) ρ (T [ σ ∘ τ ]) ρ′)
                 λ rel → RelExp (t [ σ ∘ τ ]) ρ (t [ σ ] [ τ ]) ρ′ (El _ (RelTyp.T≈T′ rel))
        helper ρ≈ρ′ = record
                        { rt
                        ; ↘⟦T⟧  = ⟦[]⟧ (⟦∘⟧ τ.↘⟦σ⟧ σ.↘⟦σ⟧) rt.↘⟦T⟧
                        ; ↘⟦T′⟧ = ⟦[]⟧ (⟦∘⟧ τ.↘⟦δ⟧ σ.↘⟦δ⟧) rt.↘⟦T′⟧
                        }
                    , record
                        { re
                        ; ↘⟦t⟧  = ⟦[]⟧ (⟦∘⟧ τ.↘⟦σ⟧ σ.↘⟦σ⟧) re.↘⟦t⟧
                        ; ↘⟦t′⟧ = ⟦[]⟧ τ.↘⟦δ⟧ (⟦[]⟧ σ.↘⟦δ⟧ re.↘⟦t′⟧)
                        }
          where module τ = RelSubst (⊨τ ρ≈ρ′)
                module σ = RelSubst (⊨σ (⊨-irrel ⊨Γ′ ⊨Γ′₁ τ.σ≈δ))
                ⊨tρ = ⊨t (⊨-irrel ⊨Γ″ ⊨Γ″₁ σ.σ≈δ)
                rt = proj₁ ⊨tρ
                re = proj₂ ⊨tρ
                module rt = RelTyp rt
                module re = RelExp re


[,]-v-ze′ : ∀ {i} →
            Γ ⊨s σ ∶ Δ →
            Δ ⊨ S ∶[ 1 + i ] Se i →
            Γ ⊨ s ∶[ i ] (S [ σ ]) →
            --------------------------------
            Γ ⊨ v 0 [ σ , s ∶ S ↙ i ] ≈ s ∶[ i ] S [ σ ]
[,]-v-ze′ {_} {σ} {_} {S} {s} (⊨Γ , ⊨Δ , ⊨σ) (⊨Δ₁ , ⊨S) (⊨Γ₁ , ⊨s) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 ----------------------------------------------------------------
                 Σ (RelTyp _ (S [ σ ]) ρ (S [ σ ]) ρ′)
                 λ rel → RelExp (v 0 [ σ , s ∶ S ↙ _ ]) ρ s ρ′ (El _ (RelTyp.T≈T′ rel))
        helper {ρ} {ρ′} ρ≈ρ′ = help
          where module σ = RelSubst (⊨σ ρ≈ρ′)
                help : Σ (RelTyp _ (S [ σ ]) ρ (S [ σ ]) ρ′)
                       λ rel → RelExp (v 0 [ σ , s ∶ S ↙ _ ]) ρ s ρ′ (El _ (RelTyp.T≈T′ rel))
                help
                  with ⊨S (⊨-irrel ⊨Δ ⊨Δ₁ σ.σ≈δ)
                     | ⊨s (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ′)
                ...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U _ _ }
                     , record { ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
                     | record { ↘⟦T⟧ = ⟦[]⟧ ↘⟦σ⟧ ↘⟦T⟧ ; ↘⟦T′⟧ = ⟦[]⟧ ↘⟦σ⟧′ ↘⟦T⟧′ ; T≈T′ = T≈T′ }
                     , re
                     rewrite ⟦⟧s-det ↘⟦σ⟧ σ.↘⟦σ⟧
                           | ⟦⟧s-det ↘⟦σ⟧′ σ.↘⟦δ⟧
                           | ⟦⟧-det ↘⟦t⟧ ↘⟦T⟧
                           | ⟦⟧-det ↘⟦t′⟧ ↘⟦T⟧′ = record
                                                    { ↘⟦T⟧  = ⟦[]⟧ σ.↘⟦σ⟧ ↘⟦T⟧
                                                    ; ↘⟦T′⟧ = ⟦[]⟧ σ.↘⟦δ⟧ ↘⟦T⟧′
                                                    ; T≈T′  = T≈T′
                                                    }
                                                , record
                                                    { re
                                                    ; ↘⟦t⟧  = ⟦[]⟧ (⟦,⟧ σ.↘⟦σ⟧ re.↘⟦t⟧) (⟦v⟧ 0)
                                                    }
                  where module re = RelExp re


[,]-v-su′ : ∀ {i j x} →
            Γ ⊨s σ ∶ Δ →
            Δ ⊨ S ∶[ 1 + i ] Se i →
            Γ ⊨ s ∶[ i ] S [ σ ] →
            x ∶[ j ] T ∈! Δ →
            ---------------------------------------------
            Γ ⊨ v (1 + x) [ σ , s ∶ S ↙ i ] ≈ v x [ σ ] ∶[ j ] T [ σ ]
[,]-v-su′ {_} {σ} {_} {S} {s} {T} {_} {_} {x} (⊨Γ , ⊨Δ , ⊨σ) (⊨Δ₁ , ⊨S) (⊨Γ₁ , ⊨s) T∈Δ = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 --------------------------------------------------------------------------------
                 Σ (RelTyp _ (T [ σ ]) ρ (T [ σ ]) ρ′)
                 λ rel → RelExp (v (1 + x) [ σ , s ∶ S ↙ _ ]) ρ (v x [ σ ]) ρ′ (El _ (RelTyp.T≈T′ rel))
        helper {ρ} {ρ′} ρ≈ρ′ = help
          where module σ = RelSubst (⊨σ ρ≈ρ′)
                module re = RelExp (proj₂ (⊨s (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ′)))
                help : Σ (RelTyp _ (T [ σ ]) ρ (T [ σ ]) ρ′)
                       λ rel → RelExp (v (1 + x) [ σ , s ∶ S ↙ _ ]) ρ (v x [ σ ]) ρ′ (El _ (RelTyp.T≈T′ rel))
                help
                  with ⊨-lookup ⊨Δ T∈Δ σ.σ≈δ
                ...  | rt′
                     , record { ↘⟦t⟧ = ⟦v⟧ _ ; ↘⟦t′⟧ = ⟦v⟧ _ ; t≈t′ = t≈t′ }
                     = record
                         { rt′
                         ; ↘⟦T⟧  = ⟦[]⟧ σ.↘⟦σ⟧ rt′.↘⟦T⟧
                         ; ↘⟦T′⟧ = ⟦[]⟧ σ.↘⟦δ⟧ rt′.↘⟦T′⟧
                         }
                     , record
                         { ↘⟦t⟧  = ⟦[]⟧ (⟦,⟧ σ.↘⟦σ⟧ re.↘⟦t⟧) (⟦v⟧ _)
                         ; ↘⟦t′⟧ = ⟦[]⟧ σ.↘⟦δ⟧ (⟦v⟧ _)
                         ; t≈t′  = t≈t′
                         }
                     where module rt′ = RelTyp rt′


≈-conv′ : ∀ {i} →
          Γ ⊨ s ≈ t ∶[ i ] S →
          Γ ⊨ S ≈ T ∶[ 1 + i ] Se i →
          --------------------
          Γ ⊨ s ≈ t ∶[ i ] T
≈-conv′ {_} {s} {t} {S} {T} (⊨Γ , s≈t) (⊨Γ₁ , S≈T) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 -------------------------------------------------
                 Σ (RelTyp _ T ρ T ρ′)
                 λ rel → RelExp s ρ t ρ′ (El _ (RelTyp.T≈T′ rel))
        helper ρ≈ρ′
          with S≈T (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ′)
             | S≈T (⟦⟧ρ-refl ⊨Γ ⊨Γ₁ ρ≈ρ′)
             | s≈t ρ≈ρ′
        ...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U eq _ }
             , record { ↘⟦t⟧ = ↘⟦S⟧ ; ↘⟦t′⟧ = ↘⟦T⟧ ; t≈t′ = ⟦S≈T⟧ }
             | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U eq′ _ }
             , record { ↘⟦t⟧ = ↘⟦S⟧′ ; ↘⟦t′⟧ = ↘⟦T⟧′ ; t≈t′ = ⟦S≈T⟧′ }
             | record { ↘⟦T⟧ = ↘⟦S⟧″ ; ↘⟦T′⟧ = ↘⟦T⟧″ ; T≈T′ = T≈T′ }
             , re
            rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym eq′))
                  | 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym eq))
                  | ⟦⟧-det ↘⟦S⟧′ ↘⟦S⟧
                  | ⟦⟧-det ↘⟦S⟧″ ↘⟦S⟧ = record
                                          { ↘⟦T⟧  = ↘⟦T⟧′
                                          ; ↘⟦T′⟧ = ↘⟦T⟧
                                          ; T≈T′  = 𝕌-trans (𝕌-sym ⟦S≈T⟧′) ⟦S≈T⟧
                                          }
                                      , record
                                          { RelExp re
                                          ; t≈t′  = El-one-sided′ ⟦S≈T⟧ (𝕌-trans (𝕌-sym ⟦S≈T⟧′) ⟦S≈T⟧) (El-one-sided T≈T′ ⟦S≈T⟧ (RelExp.t≈t′ re))
                                          }


≈-sym′ : ∀ {i} →
         Γ ⊨ t ≈ t′ ∶[ i ] T →
         ----------------
         Γ ⊨ t′ ≈ t ∶[ i ] T
≈-sym′ {_} {t} {t′} {T} (⊨Γ , t≈t′) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 ---------------------------------------------------------
                 Σ (RelTyp _ T ρ T ρ′)
                 λ rel → RelExp t′ ρ t ρ′ (El _ (RelTyp.T≈T′ rel))
        helper ρ≈ρ′
          with rt , re ← t≈t′ (⟦⟧ρ-sym′ ⊨Γ ρ≈ρ′) = record
                           { ↘⟦T⟧  = ↘⟦T′⟧
                           ; ↘⟦T′⟧ = ↘⟦T⟧
                           ; T≈T′  = 𝕌-sym T≈T′
                           }
                       , record
                           { ↘⟦t⟧  = ↘⟦t′⟧
                           ; ↘⟦t′⟧ = ↘⟦t⟧
                           ; t≈t′  = El-sym T≈T′ (𝕌-sym T≈T′) re.t≈t′
                           }
          where module rt = RelTyp rt
                module re = RelExp re
                open rt
                open re


≈-trans′ : ∀ {i} →
           Γ ⊨ t ≈ t′ ∶[ i ] T →
           Γ ⊨ t′ ≈ t″ ∶[ i ] T →
           ------ ------------
           Γ ⊨ t ≈ t″ ∶[ i ] T
≈-trans′ {_} {t} {t′} {T} {t″} (⊨Γ , t≈t′) (⊨Γ₁ , t′≈t″) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 ---------------------------------------------------
                 Σ (RelTyp _ T ρ T ρ′)
                 λ rel → RelExp t ρ t″ ρ′ (El _ (RelTyp.T≈T′ rel))
        helper ρ≈ρ′
          with t≈t′ (⟦⟧ρ-refl ⊨Γ ⊨Γ ρ≈ρ′)
             | t′≈t″ (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ′)
        ...  | record { ↘⟦T⟧ = ↘⟦T⟧ ; T≈T′ = T≈T′ }
             , record { ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
             | rt@record { ↘⟦T⟧ = ↘⟦T⟧′ ; T≈T′ = T≈T′₁ }
             , record { ↘⟦t⟧ = ↘⟦t′⟧₁ ; ↘⟦t′⟧ = ↘⟦t″⟧ ; t≈t′ = t′≈t″ }
            rewrite ⟦⟧-det ↘⟦t′⟧₁ ↘⟦t′⟧
                  | ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧′ = rt
                                      , record
                                          { ↘⟦t⟧  = ↘⟦t⟧
                                          ; ↘⟦t′⟧ = ↘⟦t″⟧
                                          ; t≈t′  = El-trans′ T≈T′₁ (El-one-sided T≈T′ T≈T′₁ t≈t′) t′≈t″
                                          }
