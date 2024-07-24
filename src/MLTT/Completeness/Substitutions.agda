{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Semantic judgments for substitutions
module MLTT.Completeness.Substitutions (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Data.Nat.Properties

open import Lib hiding (lookup)
open import MLTT.Completeness.LogRel

open import MLTT.Semantics.Properties.PER fext
open import MLTT.Completeness.Contexts fext
open import MLTT.Completeness.Terms fext
open import MLTT.Completeness.Universe fext


I-≈′ : ⊨ Γ →
       --------------
       Γ ⊨s I ≈ I ∶ Γ
I-≈′ ⊨Γ = ⊨Γ , ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 ---------------------------
                 RelSubst I ρ I ρ′ ⟦ ⊨Γ ⟧ρ
        helper ρ≈ρ′ = record
          { ↘⟦σ⟧ = ⟦I⟧
          ; ↘⟦δ⟧ = ⟦I⟧
          ; σ≈δ  = ρ≈ρ′
          }


wk-≈′ : ⊨ T ∷ Γ →
        --------------------------
        T ∷ Γ ⊨s wk ≈ wk ∶ Γ
wk-≈′ {T} ⊨TΓ@(∷-cong ⊨Γ _) = ⊨TΓ , ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨TΓ ⟧ρ →
                 ------------------------------
                 RelSubst wk ρ wk ρ′ ⟦ ⊨Γ ⟧ρ
        helper (ρ≈ρ′ , _) = record
          { ↘⟦σ⟧ = ⟦wk⟧
          ; ↘⟦δ⟧ = ⟦wk⟧
          ; σ≈δ  = ρ≈ρ′
          }


∘-cong′ : Γ ⊨s τ ≈ τ′ ∶ Γ′ →
          Γ′ ⊨s σ ≈ σ′ ∶ Γ″ →
          ----------------
          Γ ⊨s σ ∘ τ ≈ σ′ ∘ τ′ ∶ Γ″
∘-cong′ {_} {τ} {τ′} {_} {σ} {σ′} (⊨Γ , ⊨Γ′ , τ≈τ′) (⊨Γ′₁ , ⊨Γ″ , σ≈σ′) = ⊨Γ , ⊨Γ″ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 ------------------------------------------
                 RelSubst (σ ∘ τ) ρ (σ′ ∘ τ′) ρ′ ⟦ ⊨Γ″ ⟧ρ
        helper ρ≈ρ′ = record
          { σ
          ; ↘⟦σ⟧ = ⟦∘⟧ τ.↘⟦σ⟧ σ.↘⟦σ⟧
          ; ↘⟦δ⟧ = ⟦∘⟧ τ.↘⟦δ⟧ σ.↘⟦δ⟧
          }
          where module τ = RelSubst (τ≈τ′ ρ≈ρ′)
                module σ = RelSubst (σ≈σ′ (⊨-irrel ⊨Γ′ ⊨Γ′₁ τ.σ≈δ))


,-cong′ : ∀ {i} →
          Γ ⊨s σ ≈ σ′ ∶ Δ →
          Δ ⊨ T ∶ Se i →
          Γ ⊨ t ≈ t′ ∶ T [ σ ] →
          -----------------------------
          Γ ⊨s σ , t ≈ σ′ , t′ ∶ T ∷ Δ
,-cong′ {_} {σ} {σ′} {_} {T} {t} {t′} (⊨Γ , ⊨Δ , σ≈σ′) (⊨Δ₁ , i , ⊨T) (⊨Γ₁ , j , t≈t′) = ⊨Γ , ∷-cong ⊨Δ helper , helper′
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Δ ⟧ρ →
                 -------------------
                 RelTyp _ T ρ T ρ′
        helper = ∷-cong-helper (⊨Δ₁ , i , ⊨T) ⊨Δ

        helper′ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                  -------------------------------------------------------
                  RelSubst (σ , t) ρ (σ′ , t′) ρ′ ⟦ ∷-cong ⊨Δ helper ⟧ρ
        helper′ {ρ} {ρ′} ρ≈ρ′
          with ρ≈ρ′₁ ← ⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ′
             with σ≈σ′ ρ≈ρ′
                | t≈t′ ρ≈ρ′₁
        ...     | record { ⟦σ⟧ = ⟦σ⟧ ; ⟦δ⟧ = ⟦δ⟧ ; ↘⟦σ⟧ = ↘⟦σ⟧ ; ↘⟦δ⟧ = ↘⟦δ⟧ ; σ≈δ = σ≈δ }
                | record { ↘⟦T⟧ = ⟦[]⟧ ↘⟦σ⟧′ ↘⟦T⟧ ; T≈T′ = T≈T′ }
                , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
                rewrite ⟦⟧s-det ↘⟦σ⟧′ ↘⟦σ⟧ = record
                                                  { ↘⟦σ⟧ = ⟦,⟧ ↘⟦σ⟧ ↘⟦t⟧
                                                  ; ↘⟦δ⟧ = ⟦,⟧ ↘⟦δ⟧ ↘⟦t′⟧
                                                  ; σ≈δ  = σ≈δ , t≈t′₁
                                                  }
            where t≈t′₁ : ⟦t⟧ ≈ ⟦t′⟧ ∈ El _ (RelTyp.T≈T′ (helper σ≈δ))
                  t≈t′₁
                    with σ≈δ₂ ← ⊨-irrel ⊨Δ ⊨Δ₁ σ≈δ
                       with ⊨T σ≈δ₂
                  ...     | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U j<i _ }
                          , record { ⟦t⟧ = ⟦t⟧₁ ; ↘⟦t⟧ = ↘⟦t⟧₁ ; t≈t′ = t≈t′₁ }
                          rewrite 𝕌-wellfounded-≡-𝕌 _ j<i
                                | ⟦⟧-det ↘⟦t⟧₁ ↘⟦T⟧ = El-one-sided T≈T′ t≈t′₁ t≈t′


I-∘′ : Γ ⊨s σ ∶ Δ →
       -------------------
       Γ ⊨s I ∘ σ ≈ σ ∶ Δ
I-∘′ {_} {σ} (⊨Γ , ⊨Δ , ⊨σ) = ⊨Γ , ⊨Δ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 -------------------
                 RelSubst (I ∘ σ) ρ σ ρ′ ⟦ ⊨Δ ⟧ρ
        helper ρ≈ρ′ = record
          { RelSubst (⊨σ ρ≈ρ′)
          ; ↘⟦σ⟧ = ⟦∘⟧ ↘⟦σ⟧ ⟦I⟧
          }
          where open RelSubst (⊨σ ρ≈ρ′)


∘-I′ : Γ ⊨s σ ∶ Δ →
       -------------------
       Γ ⊨s σ ∘ I ≈ σ ∶ Δ
∘-I′ {_} {σ} (⊨Γ , ⊨Δ , ⊨σ) = ⊨Γ , ⊨Δ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 ---------------------------------
                 RelSubst (σ ∘ I) ρ σ ρ′ ⟦ ⊨Δ ⟧ρ
        helper ρ≈ρ′ = record
          { RelSubst (⊨σ ρ≈ρ′)
          ; ↘⟦σ⟧ = ⟦∘⟧ ⟦I⟧ ↘⟦σ⟧
          }
          where open RelSubst (⊨σ ρ≈ρ′)


∘-assoc′ : ∀ {Γ‴} →
           Γ′ ⊨s σ ∶ Γ →
           Γ″ ⊨s σ′ ∶ Γ′ →
           Γ‴ ⊨s σ″ ∶ Γ″ →
           ---------------------------------------
           Γ‴ ⊨s σ ∘ σ′ ∘ σ″ ≈ σ ∘ (σ′ ∘ σ″) ∶ Γ
∘-assoc′ {_} {σ} {_} {_} {σ′} {σ″} (⊨Γ′ , ⊨Γ , ⊨σ) (⊨Γ″ , ⊨Γ′₁ , ⊨σ′) (⊨Γ‴ , ⊨Γ″₁ , ⊨σ″) = ⊨Γ‴ , ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ‴ ⟧ρ →
                 -----------------------------------------------------
                 RelSubst (σ ∘ σ′ ∘ σ″) ρ (σ ∘ (σ′ ∘ σ″)) ρ′ ⟦ ⊨Γ ⟧ρ
        helper ρ≈ρ′ = record
            { σ
            ; ↘⟦σ⟧ = ⟦∘⟧ σ″.↘⟦σ⟧ (⟦∘⟧ σ′.↘⟦σ⟧ σ.↘⟦σ⟧)
            ; ↘⟦δ⟧ = ⟦∘⟧ (⟦∘⟧ σ″.↘⟦δ⟧ σ′.↘⟦δ⟧) σ.↘⟦δ⟧
            }
          where module σ″ = RelSubst (⊨σ″ ρ≈ρ′)
                module σ′ = RelSubst (⊨σ′ (⊨-irrel ⊨Γ″₁ ⊨Γ″ σ″.σ≈δ))
                module σ  = RelSubst (⊨σ (⊨-irrel ⊨Γ′₁ ⊨Γ′ σ′.σ≈δ))


,-∘′ : ∀ {i} →
       Γ′ ⊨s σ ∶ Γ″ →
       Γ″ ⊨ T ∶ Se i →
       Γ′ ⊨ t ∶ T [ σ ] →
       Γ ⊨s τ ∶ Γ′ →
       ---------------------------------------------
       Γ ⊨s (σ , t) ∘ τ ≈ (σ ∘ τ) , t [ τ ] ∶ T ∷ Γ″
,-∘′ {_} {σ} {_} {T} {t} {_} {τ} (⊨Γ′ , ⊨Γ″ , ⊨σ) (⊨Γ″₁ , i , ⊨T) (⊨Γ′₁ , j , ⊨t) (⊨Γ , ⊨Γ′₂ , ⊨τ) = ⊨Γ , ∷-cong ⊨Γ″ helper , helper″
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ″ ⟧ρ →
                 -------------------
                 RelTyp _ T ρ T ρ′
        helper = ∷-cong-helper (⊨Γ″₁ , i , ⊨T) ⊨Γ″

        helper′ : ∀ {i} →
                  (A≈B : A ≈ B ∈ 𝕌 i) →
                  a ≈ b ∈ El i A≈B →
                  (ρ≈ρ′ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ″ ⟧ρ) →
                  ⟦ T ⟧ ρ ↘ A →
                  -----------------------------------------
                  a ≈ b ∈ El _ (RelTyp.T≈T′ (helper ρ≈ρ′))
        helper′ {i = i} A≈B a≈b ρ≈ρ′ ↘A
          with ρ≈ρ′₁ ← ⊨-irrel ⊨Γ″ ⊨Γ″₁ ρ≈ρ′
             with ⊨T ρ≈ρ′₁
        ...     | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U j<i _ }
                , record { ⟦t⟧ = ⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; t≈t′ = T≈T′₁ }
                rewrite 𝕌-wellfounded-≡-𝕌 _ j<i
                      | ⟦⟧-det ↘A ↘⟦t⟧ = El-one-sided A≈B T≈T′₁ a≈b

        helper″ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                  ------------------------------------------------------------------------
                  RelSubst ((σ , t) ∘ τ) ρ ((σ ∘ τ) , t [ τ ]) ρ′ ⟦ ∷-cong ⊨Γ″ helper ⟧ρ
        helper″ {ρ} {ρ′} ρ≈ρ′
          with record { ↘⟦σ⟧ = ↘⟦σ⟧ ; ↘⟦δ⟧ = ↘⟦δ⟧ ; σ≈δ = σ≈δ } ← ⊨τ ρ≈ρ′
             with ⊨t (⊨-irrel ⊨Γ′₂ ⊨Γ′₁ σ≈δ) | ⊨σ (⊨-irrel ⊨Γ′₂ ⊨Γ′ σ≈δ)
        ...     | record { ↘⟦T⟧ = ⟦[]⟧ ↘⟦σ⟧′ ↘⟦T⟧ ; T≈T′ = T≈T′ }
                , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
                | record { ↘⟦σ⟧ = ↘⟦σ⟧₁ ; ↘⟦δ⟧ = ↘⟦δ⟧₁ ; σ≈δ = σ≈δ₁ }
                rewrite ⟦⟧s-det ↘⟦σ⟧′ ↘⟦σ⟧₁ = record
                                      { ↘⟦σ⟧ = ⟦∘⟧ ↘⟦σ⟧ (⟦,⟧ ↘⟦σ⟧₁ ↘⟦t⟧)
                                      ; ↘⟦δ⟧ = ⟦,⟧ (⟦∘⟧ ↘⟦δ⟧ ↘⟦δ⟧₁) (⟦[]⟧ ↘⟦δ⟧ ↘⟦t′⟧)
                                      ; σ≈δ  = σ≈δ₁ , t≈t′₁
                                      }
          where t≈t′₁ : ⟦t⟧ ≈ ⟦t′⟧ ∈ El _ (RelTyp.T≈T′ (helper σ≈δ₁))
                t≈t′₁ = helper′ T≈T′ t≈t′ σ≈δ₁ ↘⟦T⟧



p-,′ : Γ′ ⊨s σ ∶ Γ →
       Γ′ ⊨ t ∶ T [ σ ] →
       -------------------------
       Γ′ ⊨s p (σ , t) ≈ σ ∶ Γ
p-,′ {_} {σ} {_} {t} {T} (⊨Γ′ , ⊨Γ , ⊨σ) (⊨Γ′₁ , _ , ⊨t) = ⊨Γ′ , ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ′ ⟧ρ →
                 -------------------------------------
                 RelSubst (p (σ , t)) ρ σ ρ′ ⟦ ⊨Γ ⟧ρ
        helper {ρ} {ρ′} ρ≈ρ′ = help
          where module σ = RelSubst (⊨σ ρ≈ρ′)
                help : RelSubst (p (σ , t)) ρ σ ρ′ ⟦ ⊨Γ ⟧ρ
                help
                  with ⊨t (⊨-irrel ⊨Γ′ ⊨Γ′₁ ρ≈ρ′)
                ... | record { ↘⟦T⟧ = ⟦[]⟧ ↘⟦σ⟧ ↘⟦T⟧ ; ↘⟦T′⟧ = ⟦[]⟧ ↘⟦σ⟧′ ↘⟦T′⟧ }
                    , re
                    rewrite ⟦⟧s-det ↘⟦σ⟧ σ.↘⟦σ⟧
                          | ⟦⟧s-det ↘⟦σ⟧′ σ.↘⟦δ⟧ = record
                                                     { σ
                                                     ; ⟦σ⟧  = drop (σ.⟦σ⟧ ↦ re.⟦t⟧)
                                                     ; ↘⟦σ⟧ = ⟦∘⟧ (⟦,⟧ σ.↘⟦σ⟧ re.↘⟦t⟧) ⟦wk⟧
                                                     ; σ≈δ  = σ.σ≈δ
                                                     }
                  where module re = RelExp re


,-ext′ : Γ′ ⊨s σ ∶ T ∷ Γ →
         ----------------------------------
         Γ′ ⊨s σ ≈ p σ , v 0 [ σ ] ∶ T ∷ Γ
,-ext′ {_} {σ} {T} (⊨Γ′ , ⊨TΓ@(∷-cong _ _) , ⊨σ) = ⊨Γ′ , ⊨TΓ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ′ ⟧ρ →
                 ------------------------------------------------------
                 RelSubst σ ρ (p σ , v 0 [ σ ]) ρ′ ⟦ ⊨TΓ ⟧ρ
        helper ρ≈ρ′ = record
          { RelSubst (⊨σ ρ≈ρ′)
          ; ⟦δ⟧  = drop ⟦δ⟧ ↦ lookup ⟦δ⟧ 0
          ; ↘⟦δ⟧ = ⟦,⟧ (⟦∘⟧ ↘⟦δ⟧ ⟦wk⟧) (⟦[]⟧ ↘⟦δ⟧ (⟦v⟧ 0))
          ; σ≈δ  = σ≈δ
          }
          where open RelSubst (⊨σ ρ≈ρ′)


s-≈-sym′ : Γ ⊨s σ ≈ σ′ ∶ Δ →
           ------------------
           Γ ⊨s σ′ ≈ σ ∶ Δ
s-≈-sym′ {_} {σ} {σ′} (⊨Γ , ⊨Δ , σ≈σ′) = ⊨Γ , ⊨Δ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 ---------------------------
                 RelSubst σ′ ρ σ ρ′ ⟦ ⊨Δ ⟧ρ
        helper ρ≈ρ′ = record
          { ↘⟦σ⟧ = ↘⟦δ⟧
          ; ↘⟦δ⟧ = ↘⟦σ⟧
          ; σ≈δ  = ⟦⟧ρ-sym ⊨Δ ⊨Δ σ≈δ
          }
          where open RelSubst (σ≈σ′ (⟦⟧ρ-sym ⊨Γ ⊨Γ ρ≈ρ′))


s-≈-trans′ : Γ ⊨s σ ≈ σ′ ∶ Δ →
             Γ ⊨s σ′ ≈ σ″ ∶ Δ →
             -------------------
             Γ ⊨s σ ≈ σ″ ∶ Δ
s-≈-trans′ {_} {σ} {σ′} {_} {σ″} (⊨Γ , ⊨Δ , σ≈σ′) (⊨Γ′ , ⊨Δ′ , σ′≈σ″) = ⊨Γ , ⊨Δ′ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 ----------------------------
                 RelSubst σ ρ σ″ ρ′ ⟦ ⊨Δ′ ⟧ρ
        helper ρ≈ρ′
          with σ≈σ′ (⟦⟧ρ-refl ⊨Γ ⊨Γ ρ≈ρ′) | σ′≈σ″ (⊨-irrel ⊨Γ ⊨Γ′ ρ≈ρ′)
        ...  | record { ↘⟦σ⟧ = ↘⟦σ⟧   ; ↘⟦δ⟧ = ↘⟦σ′⟧ ; σ≈δ = σ≈σ′ }
             | record { ↘⟦σ⟧ = ↘⟦σ′⟧′ ; ↘⟦δ⟧ = ↘⟦σ″⟧ ; σ≈δ = σ′≈σ″ }
             rewrite ⟦⟧s-det ↘⟦σ′⟧ ↘⟦σ′⟧′ = record
          { ↘⟦σ⟧ = ↘⟦σ⟧
          ; ↘⟦δ⟧ = ↘⟦σ″⟧
          ; σ≈δ  = ⟦⟧ρ-trans ⊨Δ ⊨Δ′ ⊨Δ′ σ≈σ′ σ′≈σ″
          }


s-≈-conv′ : Γ ⊨s σ ≈ σ′ ∶ Δ →
            ⊨ Δ ≈ Δ′ →
            ------------------
            Γ ⊨s σ ≈ σ′ ∶ Δ′
s-≈-conv′ {_} {σ} {σ′} (⊨Γ , ⊨Δ , σ≈σ′) Δ≈Δ′ = ⊨Γ , ⊨Δ′ , helper
  where ⊨Δ′ = ⊨-refl (⊨-sym Δ≈Δ′)
        helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 ----------------------------
                 RelSubst σ ρ σ′ ρ′ ⟦ ⊨Δ′ ⟧ρ
        helper ρ≈ρ′ = record
          { RelSubst (σ≈σ′ ρ≈ρ′)
          ; σ≈δ  = ⟦⟧ρ-transport ⊨Δ ⊨Δ′ σ≈δ Δ≈Δ′
          }
          where open RelSubst (σ≈σ′ ρ≈ρ′)
