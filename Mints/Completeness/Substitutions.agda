{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

-- Semantic judgments for substitutions
module Mints.Completeness.Substitutions (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Data.Nat.Properties

open import Lib
open import Mints.Completeness.LogRel

open import Mints.Statics.Properties.Ops
open import Mints.Semantics.Properties.Domain fext
open import Mints.Semantics.Properties.Evaluation fext
open import Mints.Semantics.Properties.PER fext
open import Mints.Completeness.Contexts fext
open import Mints.Completeness.Terms fext
open import Mints.Completeness.Universe fext


I-≈′ : ⊨ Γ →
       --------------
       Γ ⊨s I ≈ I ∶ Γ
I-≈′ ⊨Γ = ⊨Γ , ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 ---------------------------
                 RelSubsts I ρ I ρ′ ⟦ ⊨Γ ⟧ρ
        helper ρ≈ρ′ = record
          { ↘⟦σ⟧ = ⟦I⟧
          ; ↘⟦δ⟧ = ⟦I⟧
          ; σ≈δ  = ρ≈ρ′
          }


wk-≈′ : ⊨ T ∺ Γ →
        --------------------------
        T ∺ Γ ⊨s wk ≈ wk ∶ Γ
wk-≈′ {T} ⊨TΓ@(∺-cong ⊨Γ _) = ⊨TΓ , ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨TΓ ⟧ρ →
                 ------------------------------
                 RelSubsts wk ρ wk ρ′ ⟦ ⊨Γ ⟧ρ
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
                 RelSubsts (σ ∘ τ) ρ (σ′ ∘ τ′) ρ′ ⟦ ⊨Γ″ ⟧ρ
        helper ρ≈ρ′ = record
          { σ
          ; ↘⟦σ⟧ = ⟦∘⟧ τ.↘⟦σ⟧ σ.↘⟦σ⟧
          ; ↘⟦δ⟧ = ⟦∘⟧ τ.↘⟦δ⟧ σ.↘⟦δ⟧
          }
          where module τ = RelSubsts (τ≈τ′ ρ≈ρ′)
                module σ = RelSubsts (σ≈σ′ (⊨-irrel ⊨Γ′ ⊨Γ′₁ τ.σ≈δ))


,-cong′ : ∀ {i} →
          Γ ⊨s σ ≈ σ′ ∶ Δ →
          Δ ⊨ T ∶ Se i →
          Γ ⊨ t ≈ t′ ∶ T [ σ ] →
          -----------------------------
          Γ ⊨s σ , t ≈ σ′ , t′ ∶ T ∺ Δ
,-cong′ {_} {σ} {σ′} {_} {T} {t} {t′} (⊨Γ , ⊨Δ , σ≈σ′) (⊨Δ₁ , i , ⊨T) (⊨Γ₁ , j , t≈t′) = ⊨Γ , ∺-cong ⊨Δ helper , helper′
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Δ ⟧ρ →
                 -------------------
                 RelTyp _ T ρ T ρ′
        helper = ∺-cong-helper (⊨Δ₁ , i , ⊨T) ⊨Δ

        helper′ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                  -------------------------------------------------------
                  RelSubsts (σ , t) ρ (σ′ , t′) ρ′ ⟦ ∺-cong ⊨Δ helper ⟧ρ
        helper′ {ρ} {ρ′} ρ≈ρ′
          with ρ≈ρ′₁ ← ⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ′
             with σ≈σ′ ρ≈ρ′
                | t≈t′ ρ≈ρ′₁
        ...     | record { ⟦σ⟧ = ⟦σ⟧ ; ⟦δ⟧ = ⟦δ⟧ ; ↘⟦σ⟧ = ↘⟦σ⟧ ; ↘⟦δ⟧ = ↘⟦δ⟧ ; σ≈δ = σ≈δ }
                | record { ↘⟦T⟧ = ⟦[]⟧ ↘⟦σ⟧′ ↘⟦T⟧ ; T≈T′ = T≈T′ }
                , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
                rewrite ⟦⟧s-det ↘⟦σ⟧′ ↘⟦σ⟧
                with σ≈δ₁ ← subst₂ (_≈_∈ ⟦ ⊨Δ ⟧ρ) (sym (drop-↦ _ _)) (sym (drop-↦ _ _)) σ≈δ = record
                                                  { ↘⟦σ⟧ = ⟦,⟧ ↘⟦σ⟧ ↘⟦t⟧
                                                  ; ↘⟦δ⟧ = ⟦,⟧ ↘⟦δ⟧ ↘⟦t′⟧
                                                  ; σ≈δ  = σ≈δ₁ , t≈t′₁
                                                  }
            where t≈t′₁ : ⟦t⟧ ≈ ⟦t′⟧ ∈ El _ (RelTyp.T≈T′ (helper σ≈δ₁))
                  t≈t′₁
                    with σ≈δ₂ ← ⊨-irrel ⊨Δ ⊨Δ₁ σ≈δ₁
                       with ⊨T σ≈δ₂
                  ...     | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U j<i _ }
                          , record { ⟦t⟧ = ⟦t⟧₁ ; ↘⟦t⟧ = ↘⟦t⟧₁ ; t≈t′ = t≈t′₁ }
                          rewrite 𝕌-wellfounded-≡-𝕌 _ j<i
                          with ↘⟦t⟧₂ ← subst (⟦ T ⟧_↘ ⟦t⟧₁) (drop-↦ ⟦σ⟧ ⟦t⟧) ↘⟦t⟧₁
                             rewrite ⟦⟧-det ↘⟦t⟧₂ ↘⟦T⟧ = El-one-sided T≈T′ t≈t′₁ t≈t′


；-cong′ : ∀ {n} Ψs →
           Γ ⊨s σ ≈ σ′ ∶ Δ →
           ⊨ Ψs ++⁺ Γ →
           len Ψs ≡ n →
           --------------------------------------
           Ψs ++⁺ Γ ⊨s σ ； n ≈ σ′ ； n ∶ [] ∷⁺ Δ
；-cong′ {_} {σ} {σ′} {_} {n} Ψs (⊨Γ , ⊨Δ , σ≈σ′) ⊨ΨsΓ refl = ⊨ΨsΓ , κ-cong ⊨Δ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨ΨsΓ ⟧ρ →
                 -------------------------------------------------
                 RelSubsts (σ ； n) ρ (σ′ ； n) ρ′ ⟦ κ-cong ⊨Δ ⟧ρ
        helper {ρ} {ρ′} ρ≈ρ′
          with ρ≈ρ′∥n ← ⊨-irrel (⊨-resp-∥ Ψs Ψs ⊨ΨsΓ refl) ⊨Γ (⟦⟧ρ-resp-∥ Ψs Ψs ⊨ΨsΓ refl ρ≈ρ′) = record
                                             { ↘⟦σ⟧ = ⟦；⟧ ↘⟦σ⟧
                                             ; ↘⟦δ⟧ = ⟦；⟧ ↘⟦δ⟧
                                             ; σ≈δ  = σ≈δ , ⟦⟧ρ-resp-O ⊨ΨsΓ ρ≈ρ′ (≤-trans (s≤s (m≤m+n n _)) (≤-reflexive (sym (length-++⁺-tail Ψs _))))
                                             }
          where open RelSubsts (σ≈σ′ ρ≈ρ′∥n)


I-∘′ : Γ ⊨s σ ∶ Δ →
       -------------------
       Γ ⊨s I ∘ σ ≈ σ ∶ Δ
I-∘′ {_} {σ} (⊨Γ , ⊨Δ , ⊨σ) = ⊨Γ , ⊨Δ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 -------------------
                 RelSubsts (I ∘ σ) ρ σ ρ′ ⟦ ⊨Δ ⟧ρ
        helper ρ≈ρ′ = record
          { RelSubsts (⊨σ ρ≈ρ′)
          ; ↘⟦σ⟧ = ⟦∘⟧ ↘⟦σ⟧ ⟦I⟧
          }
          where open RelSubsts (⊨σ ρ≈ρ′)


∘-I′ : Γ ⊨s σ ∶ Δ →
       -------------------
       Γ ⊨s σ ∘ I ≈ σ ∶ Δ
∘-I′ {_} {σ} (⊨Γ , ⊨Δ , ⊨σ) = ⊨Γ , ⊨Δ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 ---------------------------------
                 RelSubsts (σ ∘ I) ρ σ ρ′ ⟦ ⊨Δ ⟧ρ
        helper ρ≈ρ′ = record
          { RelSubsts (⊨σ ρ≈ρ′)
          ; ↘⟦σ⟧ = ⟦∘⟧ ⟦I⟧ ↘⟦σ⟧
          }
          where open RelSubsts (⊨σ ρ≈ρ′)


∘-assoc′ : ∀ {Γ‴} →
           Γ′ ⊨s σ ∶ Γ →
           Γ″ ⊨s σ′ ∶ Γ′ →
           Γ‴ ⊨s σ″ ∶ Γ″ →
           ---------------------------------------
           Γ‴ ⊨s σ ∘ σ′ ∘ σ″ ≈ σ ∘ (σ′ ∘ σ″) ∶ Γ
∘-assoc′ {_} {σ} {_} {_} {σ′} {σ″} (⊨Γ′ , ⊨Γ , ⊨σ) (⊨Γ″ , ⊨Γ′₁ , ⊨σ′) (⊨Γ‴ , ⊨Γ″₁ , ⊨σ″) = ⊨Γ‴ , ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ‴ ⟧ρ →
                 -----------------------------------------------------
                 RelSubsts (σ ∘ σ′ ∘ σ″) ρ (σ ∘ (σ′ ∘ σ″)) ρ′ ⟦ ⊨Γ ⟧ρ
        helper ρ≈ρ′ = record
            { σ
            ; ↘⟦σ⟧ = ⟦∘⟧ σ″.↘⟦σ⟧ (⟦∘⟧ σ′.↘⟦σ⟧ σ.↘⟦σ⟧)
            ; ↘⟦δ⟧ = ⟦∘⟧ (⟦∘⟧ σ″.↘⟦δ⟧ σ′.↘⟦δ⟧) σ.↘⟦δ⟧
            }
          where module σ″ = RelSubsts (⊨σ″ ρ≈ρ′)
                module σ′ = RelSubsts (⊨σ′ (⊨-irrel ⊨Γ″₁ ⊨Γ″ σ″.σ≈δ))
                module σ  = RelSubsts (⊨σ (⊨-irrel ⊨Γ′₁ ⊨Γ′ σ′.σ≈δ))


,-∘′ : ∀ {i} →
       Γ′ ⊨s σ ∶ Γ″ →
       Γ″ ⊨ T ∶ Se i →
       Γ′ ⊨ t ∶ T [ σ ] →
       Γ ⊨s τ ∶ Γ′ →
       ---------------------------------------------
       Γ ⊨s (σ , t) ∘ τ ≈ (σ ∘ τ) , t [ τ ] ∶ T ∺ Γ″
,-∘′ {_} {σ} {_} {T} {t} {_} {τ} (⊨Γ′ , ⊨Γ″ , ⊨σ) (⊨Γ″₁ , i , ⊨T) (⊨Γ′₁ , j , ⊨t) (⊨Γ , ⊨Γ′₂ , ⊨τ) = ⊨Γ , ∺-cong ⊨Γ″ helper , helper″
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ″ ⟧ρ →
                 -------------------
                 RelTyp _ T ρ T ρ′
        helper = ∺-cong-helper (⊨Γ″₁ , i , ⊨T) ⊨Γ″

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
                  RelSubsts ((σ , t) ∘ τ) ρ ((σ ∘ τ) , t [ τ ]) ρ′ ⟦ ∺-cong ⊨Γ″ helper ⟧ρ
        helper″ {ρ} {ρ′} ρ≈ρ′
          with record { ↘⟦σ⟧ = ↘⟦σ⟧ ; ↘⟦δ⟧ = ↘⟦δ⟧ ; σ≈δ = σ≈δ } ← ⊨τ ρ≈ρ′
             with ⊨t (⊨-irrel ⊨Γ′₂ ⊨Γ′₁ σ≈δ) | ⊨σ (⊨-irrel ⊨Γ′₂ ⊨Γ′ σ≈δ)
        ...     | record { ↘⟦T⟧ = ⟦[]⟧ ↘⟦σ⟧′ ↘⟦T⟧ ; T≈T′ = T≈T′ }
                , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
                | record { ↘⟦σ⟧ = ↘⟦σ⟧₁ ; ↘⟦δ⟧ = ↘⟦δ⟧₁ ; σ≈δ = σ≈δ₁ }
                rewrite ⟦⟧s-det ↘⟦σ⟧′ ↘⟦σ⟧₁
                with σ≈δ₂ ← subst₂ (_≈_∈ ⟦ _ ⟧ρ) (sym (drop-↦ _ _)) (sym (drop-↦ _ _)) σ≈δ₁ = record
                                      { ↘⟦σ⟧ = ⟦∘⟧ ↘⟦σ⟧ (⟦,⟧ ↘⟦σ⟧₁ ↘⟦t⟧)
                                      ; ↘⟦δ⟧ = ⟦,⟧ (⟦∘⟧ ↘⟦δ⟧ ↘⟦δ⟧₁) (⟦[]⟧ ↘⟦δ⟧ ↘⟦t′⟧)
                                      ; σ≈δ  = σ≈δ₂ , t≈t′₁
                                      }
          where t≈t′₁ : ⟦t⟧ ≈ ⟦t′⟧ ∈ El _ (RelTyp.T≈T′ (helper σ≈δ₂))
                t≈t′₁ = helper′ T≈T′ t≈t′ σ≈δ₂ (subst (⟦ T ⟧_↘ _) (sym (drop-↦ _ _)) ↘⟦T⟧)


；-∘′ : ∀ {n} Ψs →
       Γ′ ⊨s σ ∶ Γ″ →
       Γ ⊨s τ ∶ Ψs ++⁺ Γ′ →
       len Ψs ≡ n →
       ------------------------------
       Γ ⊨s σ ； n ∘ τ ≈ (σ ∘ τ ∥ n) ； O τ n ∶ [] ∷⁺ Γ″
；-∘′ {_} {σ} {_} {_} {τ} {n} Ψs (⊨Γ′ , ⊨Γ″ , ⊨σ) (⊨Γ , ⊨ΨsΓ′ , ⊨τ) refl = ⊨Γ , κ-cong ⊨Γ″ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 ---------------------------------------------------------------------
                 RelSubsts (σ ； n ∘ τ) ρ ((σ ∘ τ ∥ n) ； O τ n) ρ′ ⟦ κ-cong ⊨Γ″ ⟧ρ
        helper {ρ} {ρ′} ρ≈ρ′ = record
          { ⟦σ⟧  = ext σ.⟦σ⟧ (O τ.⟦σ⟧ n)
          ; ⟦δ⟧  = ext σ.⟦δ⟧ (O ρ′ (O τ n))
          ; ↘⟦σ⟧ = ⟦∘⟧ τ.↘⟦σ⟧ (⟦；⟧ σ.↘⟦σ⟧)
          ; ↘⟦δ⟧ = ⟦；⟧ (⟦∘⟧ (∥-⟦⟧s n τ.↘⟦δ⟧) σ.↘⟦δ⟧)
          ; σ≈δ  = σ.σ≈δ , trans (⟦⟧ρ-resp-O ⊨ΨsΓ′ τ.σ≈δ (length-<-++⁺ Ψs)) (sym (O-⟦⟧s n τ.↘⟦δ⟧))
          }
          where module τ = RelSubsts (⊨τ ρ≈ρ′)
                module σ = RelSubsts (⊨σ (⊨-irrel (⊨-resp-∥ Ψs Ψs ⊨ΨsΓ′ refl) ⊨Γ′ (⟦⟧ρ-resp-∥ Ψs Ψs ⊨ΨsΓ′ refl τ.σ≈δ)))


p-,′ : Γ′ ⊨s σ ∶ Γ →
       Γ′ ⊨ t ∶ T [ σ ] →
       -------------------------
       Γ′ ⊨s p (σ , t) ≈ σ ∶ Γ
p-,′ {_} {σ} {_} {t} {T} (⊨Γ′ , ⊨Γ , ⊨σ) (⊨Γ′₁ , _ , ⊨t) = ⊨Γ′ , ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ′ ⟧ρ →
                 -------------------------------------
                 RelSubsts (p (σ , t)) ρ σ ρ′ ⟦ ⊨Γ ⟧ρ
        helper {ρ} {ρ′} ρ≈ρ′ = help
          where module σ = RelSubsts (⊨σ ρ≈ρ′)
                help : RelSubsts (p (σ , t)) ρ σ ρ′ ⟦ ⊨Γ ⟧ρ
                help
                  with ⊨t (⊨-irrel ⊨Γ′ ⊨Γ′₁ ρ≈ρ′)
                ... | record { ↘⟦T⟧ = ⟦[]⟧ ↘⟦σ⟧ ↘⟦T⟧ ; ↘⟦T′⟧ = ⟦[]⟧ ↘⟦σ⟧′ ↘⟦T′⟧ }
                    , re
                    rewrite ⟦⟧s-det ↘⟦σ⟧ σ.↘⟦σ⟧
                          | ⟦⟧s-det ↘⟦σ⟧′ σ.↘⟦δ⟧ = record
                                                     { σ
                                                     ; ⟦σ⟧  = drop (σ.⟦σ⟧ ↦ re.⟦t⟧)
                                                     ; ↘⟦σ⟧ = ⟦∘⟧ (⟦,⟧ σ.↘⟦σ⟧ re.↘⟦t⟧) ⟦wk⟧
                                                     ; σ≈δ  = subst (_≈ σ.⟦δ⟧ ∈ ⟦ ⊨Γ ⟧ρ) (sym (drop-↦ _ _)) σ.σ≈δ
                                                     }
                  where module re = RelExp re


,-ext′ : Γ′ ⊨s σ ∶ T ∺ Γ →
         ----------------------------------
         Γ′ ⊨s σ ≈ p σ , v 0 [ σ ] ∶ T ∺ Γ
,-ext′ {_} {σ} {T} (⊨Γ′ , ⊨TΓ@(∺-cong _ _) , ⊨σ) = ⊨Γ′ , ⊨TΓ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ′ ⟧ρ →
                 ------------------------------------------------------
                 RelSubsts σ ρ (p σ , v 0 [ σ ]) ρ′ ⟦ ⊨TΓ ⟧ρ
        helper ρ≈ρ′ = record
          { RelSubsts (⊨σ ρ≈ρ′)
          ; ⟦δ⟧  = drop ⟦δ⟧ ↦ lookup ⟦δ⟧ 0
          ; ↘⟦δ⟧ = ⟦,⟧ (⟦∘⟧ ↘⟦δ⟧ ⟦wk⟧) (⟦[]⟧ ↘⟦δ⟧ (⟦v⟧ 0))
          ; σ≈δ  = subst (⟦σ⟧ ≈_∈ ⟦ ⊨TΓ ⟧ρ) (sym (drop-same _)) σ≈δ
          }
          where open RelSubsts (⊨σ ρ≈ρ′)

；-ext′ : Γ ⊨s σ ∶ [] ∷⁺ Δ →
         -----------------------------------
         Γ ⊨s σ ≈ (σ ∥ 1) ； O σ 1 ∶ [] ∷⁺ Δ
；-ext′ {_} {σ} (⊨Γ , ⊨κΔ@(κ-cong _) , ⊨σ) = ⊨Γ , ⊨κΔ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 -------------------------------------------
                 RelSubsts σ ρ (σ ∥ 1 ； O σ 1) ρ′ ⟦ ⊨κΔ ⟧ρ
        helper {ρ} {ρ′} ρ≈ρ′ = record
          { RelSubsts (⊨σ ρ≈ρ′)
          ; ⟦δ⟧  = ext (⟦δ⟧ ∥ 1) (O ρ′ (O σ 1))
          ; ↘⟦δ⟧ = ⟦；⟧ (∥-⟦⟧s 1 ↘⟦δ⟧)
          ; σ≈δ  = proj₁ σ≈δ , helper-eq
          }
          where open RelSubsts (⊨σ ρ≈ρ′)
                helper-eq : proj₁ (⟦σ⟧ 0) ≡ O ρ′ (S-O σ 1)
                helper-eq = trans (proj₂ σ≈δ) (trans (sym (+-identityʳ _)) (sym (O-⟦⟧s 1 ↘⟦δ⟧)))


s-≈-sym′ : Γ ⊨s σ ≈ σ′ ∶ Δ →
           ------------------
           Γ ⊨s σ′ ≈ σ ∶ Δ
s-≈-sym′ {_} {σ} {σ′} (⊨Γ , ⊨Δ , σ≈σ′) = ⊨Γ , ⊨Δ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 ---------------------------
                 RelSubsts σ′ ρ σ ρ′ ⟦ ⊨Δ ⟧ρ
        helper ρ≈ρ′ = record
          { ↘⟦σ⟧ = ↘⟦δ⟧
          ; ↘⟦δ⟧ = ↘⟦σ⟧
          ; σ≈δ  = ⟦⟧ρ-sym ⊨Δ ⊨Δ σ≈δ
          }
          where open RelSubsts (σ≈σ′ (⟦⟧ρ-sym ⊨Γ ⊨Γ ρ≈ρ′))


s-≈-trans′ : Γ ⊨s σ ≈ σ′ ∶ Δ →
             Γ ⊨s σ′ ≈ σ″ ∶ Δ →
             -------------------
             Γ ⊨s σ ≈ σ″ ∶ Δ
s-≈-trans′ {_} {σ} {σ′} {_} {σ″} (⊨Γ , ⊨Δ , σ≈σ′) (⊨Γ′ , ⊨Δ′ , σ′≈σ″) = ⊨Γ , ⊨Δ′ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 ----------------------------
                 RelSubsts σ ρ σ″ ρ′ ⟦ ⊨Δ′ ⟧ρ
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
                 RelSubsts σ ρ σ′ ρ′ ⟦ ⊨Δ′ ⟧ρ
        helper ρ≈ρ′ = record
          { RelSubsts (σ≈σ′ ρ≈ρ′)
          ; σ≈δ  = ⟦⟧ρ-transport ⊨Δ ⊨Δ′ σ≈δ Δ≈Δ′
          }
          where open RelSubsts (σ≈σ′ ρ≈ρ′)
