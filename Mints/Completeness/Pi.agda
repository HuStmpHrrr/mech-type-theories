{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

-- Semantic judgments for Π types
module Mints.Completeness.Pi (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Data.Nat
open import Data.Nat.Properties

open import Lib
open import Mints.Completeness.LogRel
open import Mints.Completeness.Substitutions fext
open import Mints.Completeness.Terms fext

open import Mints.Semantics.Properties.Domain fext
open import Mints.Semantics.Properties.Evaluation fext
open import Mints.Semantics.Properties.PER fext


Π-[]′ : ∀ {i} →
        Γ ⊨s σ ∶ Δ →
        Δ ⊨ S ∶ Se i →
        S ∺ Δ ⊨ T ∶ Se i →
        -------------------------------------------------
        Γ ⊨ Π S T [ σ ] ≈ Π (S [ σ ]) (T [ q σ ]) ∶ Se i
Π-[]′ {_} {σ} {_} {S} {T} {i} (⊨Γ , ⊨Δ , ⊨σ) (⊨Δ₁ , _ , ⊨S) (∺-cong ⊨Δ₂ rel , _ , ⊨T) = ⊨Γ , _ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 -------------------------------------------------------------------------------------
                 Σ (RelTyp _ (Se i) ρ (Se i) ρ′)
                 λ rel → RelExp (Π S T [ σ ]) ρ (Π (S [ σ ]) (T [ q σ ])) ρ′ (El _ (RelTyp.T≈T′ rel))
        helper {ρ} {ρ′} ρ≈ρ′ = help
          where module σ = RelSubsts (⊨σ ρ≈ρ′)
                help : Σ (RelTyp _ (Se i) ρ (Se i) ρ′)
                       λ rel → RelExp (Π S T [ σ ]) ρ (Π (S [ σ ]) (T [ q σ ])) ρ′ (El _ (RelTyp.T≈T′ rel))
                help
                  with ⊨S (⊨-irrel ⊨Δ ⊨Δ₁ σ.σ≈δ)
                ...  | record { ⟦T⟧ = .(U i) ; ⟦T′⟧ = .(U i) ; ↘⟦T⟧ = (⟦Se⟧ .i) ; ↘⟦T′⟧ = (⟦Se⟧ .i) ; T≈T′ = U i<j _ }
                     , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
                     = record
                        { ⟦T⟧   = U i
                        ; ⟦T′⟧  = U i
                        ; ↘⟦T⟧  = ⟦Se⟧ i
                        ; ↘⟦T′⟧ = ⟦Se⟧ i
                        ; T≈T′  = U′ i<j
                        }
                     , record
                         { ⟦t⟧   = Π ⟦t⟧ T σ.⟦σ⟧
                         ; ⟦t′⟧  = Π ⟦t′⟧ (T [ q σ ]) ρ′
                         ; ↘⟦t⟧  = ⟦[]⟧ σ.↘⟦σ⟧ (⟦Π⟧ ↘⟦t⟧)
                         ; ↘⟦t′⟧ = ⟦Π⟧ (⟦[]⟧ σ.↘⟦δ⟧ ↘⟦t′⟧)
                         ; t≈t′  = subst (Π ⟦t⟧ T σ.⟦σ⟧ ≈ Π ⟦t′⟧ (T [ q σ ]) ρ′ ∈_) (sym (𝕌-wellfounded-≡-𝕌 _ i<j))
                                         (result (subst (⟦t⟧ ≈ ⟦t′⟧ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<j) t≈t′))
                         }
                  where result : ⟦t⟧ ≈ ⟦t′⟧ ∈ 𝕌 i →
                                 ------------------------------------------
                                 Π ⟦t⟧ T σ.⟦σ⟧ ≈ Π ⟦t′⟧ (T [ q σ ]) ρ′ ∈ 𝕌 i
                        result S≈ = Π (λ κ → 𝕌-mon κ S≈) step
                          where step : (κ : UMoT) →
                                       a ≈ a′ ∈ El i (𝕌-mon κ S≈) →
                                       -----------------------------------------------------------
                                       ΠRT T (σ.⟦σ⟧ [ κ ] ↦ a) (T [ q σ ]) (ρ′ [ κ ] ↦ a′) (𝕌 i)
                                step {a} {a′} κ a≈a′
                                  with σ≈δ₁ ← subst₂ (_≈_∈ ⟦ ⊨Δ₂ ⟧ρ) (sym (drop-↦ _ _)) (sym (drop-↦ _ _)) (⊨-irrel ⊨Δ ⊨Δ₂ (⟦⟧ρ-mon ⊨Δ κ σ.σ≈δ)) = answer
                                  where insert : a ≈ a′ ∈ El _ (RelTyp.T≈T′ (rel σ≈δ₁))
                                        insert
                                          with record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ } ← rel σ≈δ₁
                                             rewrite ⟦⟧-det (subst (⟦ S ⟧_↘ ⟦T⟧) (drop-↦ _ _) ↘⟦T⟧) (⟦⟧-mon κ ↘⟦t⟧)
                                                   | ⟦⟧-det (subst (⟦ S ⟧_↘ ⟦T′⟧) (drop-↦ _ _) ↘⟦T′⟧) (⟦⟧-mon κ ↘⟦t′⟧) = 𝕌-irrel (𝕌-mon κ S≈) T≈T′ a≈a′

                                        answer : ΠRT T (σ.⟦σ⟧ [ κ ] ↦ a) (T [ q σ ]) (ρ′ [ κ ] ↦ a′) (𝕌 i)
                                        answer
                                          with ⊨T {σ.⟦σ⟧ [ κ ] ↦ a} {σ.⟦δ⟧ [ κ ] ↦ a′} (σ≈δ₁ , insert)
                                        ...  | record { ⟦T⟧ = .(U i) ; ⟦T′⟧ = .(U i) ; ↘⟦T⟧ = (⟦Se⟧ .i) ; ↘⟦T′⟧ = (⟦Se⟧ .i) ; T≈T′ = U i<j _ }
                                             , re = record
                                                      { ⟦T⟧   = re.⟦t⟧
                                                      ; ⟦T′⟧  = re.⟦t′⟧
                                                      ; ↘⟦T⟧  = re.↘⟦t⟧
                                                      ; ↘⟦T′⟧ = ⟦[]⟧ (⟦q⟧ (subst (⟦ σ ⟧s_↘ σ.⟦δ⟧ [ κ ]) (sym (drop-↦ _ _)) (⟦⟧s-mon κ σ.↘⟦δ⟧))) re.↘⟦t′⟧
                                                      ; T≈T′  = subst (re.⟦t⟧ ≈ re.⟦t′⟧ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<j) re.t≈t′
                                                      }
                                          where module re = RelExp re


Π-cong′ : ∀ {i} →
          Γ ⊨ S ≈ S′ ∶ Se i →
          S ∺ Γ ⊨ T ≈ T′ ∶ Se i →
          --------------------------
          Γ ⊨ Π S T ≈ Π S′ T′ ∶ Se i
Π-cong′ {_} {S} {S′} {T} {T′} {i} (⊨Γ , _ , S≈S′) (∺-cong ⊨Γ₁ rel , _ , T≈T′) = ⊨Γ , _ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 ----------------------------------------------------------------
                 Σ (RelTyp _ (Se i) ρ (Se i) ρ′)
                 λ rel → RelExp (Π S T) ρ (Π S′ T′) ρ′ (El _ (RelTyp.T≈T′ rel))
        helper {ρ} {ρ′} ρ≈ρ′
          with S≈S′ ρ≈ρ′
        ...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<j _ }
             , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
             rewrite 𝕌-wellfounded-≡-𝕌 _ i<j = record
                                                 { ↘⟦T⟧  = ⟦Se⟧ _
                                                 ; ↘⟦T′⟧ = ⟦Se⟧ _
                                                 ; T≈T′  = U′ i<j
                                                 }
                                             , record
                                                 { ↘⟦t⟧  = ⟦Π⟧ ↘⟦t⟧
                                                 ; ↘⟦t′⟧ = ⟦Π⟧ ↘⟦t′⟧
                                                 ; t≈t′  = subst (Π ⟦t⟧ T ρ ≈ Π ⟦t′⟧ T′ ρ′ ∈_) (sym (𝕌-wellfounded-≡-𝕌 _ i<j)) (Π (λ κ → 𝕌-mon κ t≈t′) result)
                                                 }
          where result : (κ : UMoT) →
                         a ≈ a′ ∈ El _ (𝕌-mon κ t≈t′) →
                         ------------------------------------------------
                         ΠRT T (ρ [ κ ] ↦ a) T′ (ρ′ [ κ ] ↦ a′) (𝕌 i)
                result {a} {a′} κ a≈a′
                  with ρ≈ρ′₁ ← subst₂ (_≈_∈ ⟦ ⊨Γ₁ ⟧ρ) (sym (drop-↦ _ _)) (sym (drop-↦ _ _)) (⊨-irrel ⊨Γ ⊨Γ₁ (⟦⟧ρ-mon ⊨Γ κ ρ≈ρ′)) = answer
                  where insert : a ≈ a′ ∈ El _ (RelTyp.T≈T′ (rel ρ≈ρ′₁))
                        insert
                          with record { ⟦T⟧ = ⟦T⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; T≈T′ = T≈T′ } ← rel ρ≈ρ′₁
                             rewrite ⟦⟧-det (subst (⟦ S ⟧_↘ ⟦T⟧) (drop-↦ _ _) ↘⟦T⟧) (⟦⟧-mon κ ↘⟦t⟧) = El-one-sided (𝕌-mon κ t≈t′) T≈T′ a≈a′

                        answer : ΠRT T (ρ [ κ ] ↦ a) T′ (ρ′ [ κ ] ↦ a′) (𝕌 i)
                        answer
                          with T≈T′ {ρ [ κ ] ↦ a} {ρ′ [ κ ] ↦ a′} (ρ≈ρ′₁ , insert)
                        ...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<j _ }
                             , re = record
                                      { ↘⟦T⟧  = re.↘⟦t⟧
                                      ; ↘⟦T′⟧ = re.↘⟦t′⟧
                                      ; T≈T′  = subst (re.⟦t⟧ ≈ re.⟦t′⟧ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<j) re.t≈t′
                                      }
                          where module re = RelExp re


Λ-cong′ : S ∺ Γ ⊨ t ≈ t′ ∶ T →
          -----------------------
          Γ ⊨ Λ t ≈ Λ t′ ∶ Π S T
Λ-cong′ {S} {_} {t} {t′} {T} (∺-cong ⊨Γ rel , n , t≈t′) = ⊨Γ , _ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 ----------------------------------------------------------
                 Σ (RelTyp _ (Π S T) ρ (Π S T) ρ′)
                 λ rel → RelExp (Λ t) ρ (Λ t′) ρ′ (El _ (RelTyp.T≈T′ rel))
        helper {ρ} {ρ′} ρ≈ρ′ = record
                                 { ↘⟦T⟧  = ⟦Π⟧ S.↘⟦T⟧
                                 ; ↘⟦T′⟧ = ⟦Π⟧ S.↘⟦T′⟧
                                 ; T≈T′  = Π (λ κ → 𝕌-cumu (m≤m⊔n _ n) (𝕌-mon κ S.T≈T′)) λ κ a≈b → proj₁ (Πres κ a≈b)
                                 }
                             , record
                                 { ↘⟦t⟧  = ⟦Λ⟧ t
                                 ; ↘⟦t′⟧ = ⟦Λ⟧ t′
                                 ; t≈t′  = λ κ a≈b → proj₂ (Πres κ a≈b)
                                 }
             where module S = RelTyp (rel ρ≈ρ′)
                   insert : (⊨Γ : ⊨ Γ) →
                            (rel : ∀ {ρ ρ′} → ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → RelTyp _ S ρ S ρ′) →
                            (κ : UMoT) (ρ≈ρ′ : drop (ρ [ κ ] ↦ a) ≈ drop (ρ′ [ κ ] ↦ a′) ∈ ⟦ ⊨Γ ⟧ρ) →
                            a ≈ a′ ∈ El _ (𝕌-cumu (m≤m⊔n _ n) (𝕌-mon κ S.T≈T′)) →
                            ---------------------------------------------------------------------------
                            a ≈ a′ ∈ El _ (RelTyp.T≈T′ (rel ρ≈ρ′))
                   insert ⊨Γ rel κ ρ≈ρ′ a≈a′
                     with record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ } ← rel ρ≈ρ′
                        rewrite ⟦⟧-det (subst (⟦ S ⟧_↘ ⟦T⟧) (drop-↦ _ _) ↘⟦T⟧) (⟦⟧-mon κ S.↘⟦T⟧) = El-one-sided (𝕌-cumu (m≤m⊔n _ n) (𝕌-mon κ S.T≈T′)) T≈T′ a≈a′

                   Πres : (κ : UMoT) (a≈b : a ≈ b ∈ El _ (𝕌-cumu (m≤m⊔n _ n) (𝕌-mon κ S.T≈T′))) →
                          ---------------------------------------------------------------------------
                          Σ (ΠRT T (ρ [ κ ] ↦ a) T (ρ′ [ κ ] ↦ b) (𝕌 _))
                          λ rel → Π̂ (Λ t (ρ [ κ ])) a (Λ t′ (ρ′ [ κ ])) b (El _ (ΠRT.T≈T′ rel))
                   Πres {a} {b} κ a≈b
                     with ρ≈ρ′₁ ← subst₂ (_≈_∈ ⟦ ⊨Γ ⟧ρ) (sym (drop-↦ _ _)) (sym (drop-↦ _ _)) (⟦⟧ρ-mon ⊨Γ κ ρ≈ρ′) = answer
                     where answer : Σ (ΠRT T (ρ [ κ ] ↦ a) T (ρ′ [ κ ] ↦ b) (𝕌 _))
                                    λ rel → Π̂ (Λ t (ρ [ κ ])) a (Λ t′ (ρ′ [ κ ])) b (El _ (ΠRT.T≈T′ rel))
                           answer
                             with t≈t′ {ρ [ κ ] ↦ a} {ρ′ [ κ ] ↦ b} (ρ≈ρ′₁ , insert ⊨Γ rel κ ρ≈ρ′₁ a≈b)
                           ...  | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
                                , re = record
                                         { ↘⟦T⟧  = ↘⟦T⟧
                                         ; ↘⟦T′⟧ = ↘⟦T′⟧
                                         ; T≈T′  = T≈T′₁
                                         }
                                     , record
                                         { ↘fa    = Λ∙ re.↘⟦t⟧
                                         ; ↘fa′   = Λ∙ re.↘⟦t′⟧
                                         ; fa≈fa′ = 𝕌-irrel T≈T′ T≈T′₁ re.t≈t′
                                         }
                             where module re = RelExp re
                                   T≈T′₁ = 𝕌-cumu (m≤n⊔m _ n) T≈T′


$-cong′ : Γ ⊨ r ≈ r′ ∶ Π S T →
          Γ ⊨ s ≈ s′ ∶ S →
          -------------------------------
          Γ ⊨ r $ s ≈ r′ $ s′ ∶ T [| s ]
$-cong′ {_} {r} {r′} {S} {T} {s} {s′} (⊨Γ , _ , r≈r′) (⊨Γ₁ , _ , s≈s′) = ⊨Γ , _ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 ----------------------------------------------------------------
                 Σ (RelTyp _ (T [| s ]) ρ (T [| s ]) ρ′)
                 λ rel → RelExp (r $ s) ρ (r′ $ s′) ρ′ (El _ (RelTyp.T≈T′ rel))
        helper {ρ} {ρ′} ρ≈ρ′
          with ρ≈ρ ← ⊨-irrel ⊨Γ ⊨Γ₁ (⟦⟧ρ-refl ⊨Γ ⊨Γ ρ≈ρ′)
             | ρ′≈ρ ← ⊨-irrel ⊨Γ ⊨Γ₁ (⟦⟧ρ-sym′ ⊨Γ ρ≈ρ′)
          with r≈r′ ρ≈ρ′
             | s≈s′ ρ≈ρ
             | s≈s′ ρ′≈ρ
             | s≈s′ (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ′)
        ...  | record { ↘⟦T⟧ = ⟦Π⟧ ↘⟦S⟧ ; ↘⟦T′⟧ = ⟦Π⟧ ↘⟦S⟧′ ; T≈T′ = Π iA RT }
             , record { ⟦t⟧ = ⟦r⟧ ; ⟦t′⟧ = ⟦r′⟧ ; ↘⟦t⟧ = ↘⟦r⟧ ; ↘⟦t′⟧ = ↘⟦r′⟧ ; t≈t′ = r≈r′ }
             | record { ⟦T⟧ = ⟦T⟧₁ ; ⟦T′⟧ = ⟦T′⟧₁ ; ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ }
             , record { ⟦t⟧ = ⟦t⟧₁ ; ⟦t′⟧ = ⟦t′⟧₁ ; ↘⟦t⟧ = ↘⟦t⟧₁ ; ↘⟦t′⟧ = ↘⟦t′⟧₁ ; t≈t′ = t≈t′₁ }
             | record { ⟦T⟧ = ⟦T⟧₂ ; ⟦T′⟧ = ⟦T′⟧₂ ; ↘⟦T⟧ = ↘⟦T⟧₂ ; ↘⟦T′⟧ = ↘⟦T′⟧₂ ; T≈T′ = T≈T′₂ }
             , record { ⟦t⟧ = ⟦t⟧₂ ; ⟦t′⟧ = ⟦t′⟧₂ ; ↘⟦t⟧ = ↘⟦t⟧₂ ; ↘⟦t′⟧ = ↘⟦t′⟧₂ ; t≈t′ = t≈t′₂ }
             | record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
             , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
             rewrite ⟦⟧-det ↘⟦S⟧ ↘⟦T⟧
                   | ⟦⟧-det ↘⟦S⟧′ ↘⟦T′⟧
                   | ⟦⟧-det ↘⟦T⟧₁ ↘⟦T⟧
                   | ⟦⟧-det ↘⟦T′⟧₁ ↘⟦T′⟧₂
                   | ⟦⟧-det ↘⟦t′⟧₁ ↘⟦t′⟧₂
                   | ⟦⟧-det ↘⟦t⟧₁ ↘⟦t⟧ = record
                                           { ↘⟦T⟧  = ⟦[]⟧ (⟦,⟧ ⟦I⟧ ↘⟦t⟧) (subst (λ x → ⟦ T ⟧ x ↦ ⟦t⟧ ↘ RT.⟦T⟧) (ρ-ap-vone _) RT.↘⟦T⟧)
                                           ; ↘⟦T′⟧ = ⟦[]⟧ (⟦,⟧ ⟦I⟧ ↘⟦t⟧₂) (subst (λ x → ⟦ T ⟧ x ↦ ⟦t⟧₂ ↘ RT.⟦T′⟧) (ρ-ap-vone _) RT.↘⟦T′⟧)
                                           ; T≈T′  = RT.T≈T′
                                           }
                                       , record
                                           { ↘⟦t⟧  = ⟦$⟧ ↘⟦r⟧ ↘⟦t⟧ (subst (_∙ ⟦t⟧ ↘ rs.fa) (D-ap-vone _) rs.↘fa)
                                           ; ↘⟦t′⟧ = ⟦$⟧ ↘⟦r′⟧ ↘⟦t′⟧ (subst (_∙ ⟦t′⟧ ↘ rs.fa′) (D-ap-vone _) rs.↘fa′)
                                           ; t≈t′  = El-transp RT′.T≈T′ RT.T≈T′ rs.fa≈fa′ (sym (⟦⟧-det RT.↘⟦T⟧ RT′.↘⟦T⟧))
                                           }
          where T≈T  = 𝕌-trans T≈T′₁ (𝕌-sym T≈T′₂)
                srel = El-trans T≈T′₁ (𝕌-sym T≈T′₂) T≈T t≈t′₁ (El-sym T≈T′₂ (𝕌-sym T≈T′₂) t≈t′₂)

                module RT  = ΠRT (RT vone (El-transp T≈T (iA vone) srel (sym (D-ap-vone _))))
                module RT′ = ΠRT (RT vone (El-transp T≈T′ (iA vone) t≈t′ (sym (D-ap-vone _))))
                module rs  = Π̂ (r≈r′ vone (El-transp T≈T′ (iA vone) t≈t′ (sym (D-ap-vone _))))


Λ-β′ : S ∺ Γ ⊨ t ∶ T →
       Γ ⊨ s ∶ S →
       ----------------------------------
       Γ ⊨ Λ t $ s ≈ t [| s ] ∶ T [| s ]
Λ-β′ {S} {_} {t} {T} {s} (∺-cong ⊨Γ rel , _ , ⊨t) (⊨Γ₁ , _ , ⊨s) = ⊨Γ , _ , helper
  where
    helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
             ------------------------------------------------------------------
             Σ (RelTyp _ (T [| s ]) ρ (T [| s ]) ρ′)
             λ rel → RelExp (Λ t $ s) ρ (t [| s ]) ρ′ (El _ (RelTyp.T≈T′ rel))
    helper {ρ} {ρ′} ρ≈ρ′
      with ⊨s (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ′)
    ...  | record { ↘⟦T⟧ = ↘⟦S⟧ ; ↘⟦T′⟧ = ↘⟦S′⟧ ; T≈T′ = S≈S′ }
         , record { ⟦t⟧ = ⟦s⟧ ; ⟦t′⟧ = ⟦s′⟧ ; ↘⟦t⟧ = ↘⟦s⟧ ; ↘⟦t′⟧ = ↘⟦s′⟧ ; t≈t′ = s≈s′ } = helper′
      where
        ρ≈ρ′₁ : drop (ρ ↦ ⟦s⟧) ≈ drop (ρ′ ↦ ⟦s′⟧) ∈ ⟦ ⊨Γ ⟧ρ
        ρ≈ρ′₁
         rewrite drop-↦ ρ ⟦s⟧
               | drop-↦ ρ′ ⟦s′⟧ = ρ≈ρ′

        s≈s′₁ : ⟦s⟧ ≈ ⟦s′⟧ ∈ El _ (RelTyp.T≈T′ (rel ρ≈ρ′₁))
        s≈s′₁
          with record { ↘⟦T⟧ = ↘⟦S⟧₁ ; ↘⟦T′⟧ = ↘⟦S′⟧₁ ; T≈T′ = S≈S′₁ } ← rel ρ≈ρ′₁
            rewrite drop-↦ ρ ⟦s⟧
                  | drop-↦ ρ′ ⟦s′⟧
                  | ⟦⟧-det ↘⟦S⟧ ↘⟦S⟧₁
                  | ⟦⟧-det ↘⟦S′⟧ ↘⟦S′⟧₁
                  = 𝕌-irrel S≈S′ S≈S′₁ s≈s′

        helper′ : Σ (RelTyp _ (T [| s ]) ρ (T [| s ]) ρ′)
                  λ rel → RelExp (Λ t $ s) ρ (t [| s ]) ρ′ (El _ (RelTyp.T≈T′ rel))
        helper′
          with ⊨t (ρ≈ρ′₁ , s≈s′₁)
        ...  | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
             , record { ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ } = record
                                     { ↘⟦T⟧ = ⟦[]⟧ (⟦,⟧ ⟦I⟧ ↘⟦s⟧) ↘⟦T⟧
                                     ; ↘⟦T′⟧ = ⟦[]⟧ ((⟦,⟧ ⟦I⟧ ↘⟦s′⟧)) ↘⟦T′⟧
                                     ; T≈T′ = T≈T′
                                     }
                                   , record
                                     { ↘⟦t⟧ = ⟦$⟧ (⟦Λ⟧ _) ↘⟦s⟧ (Λ∙ ↘⟦t⟧)
                                     ; ↘⟦t′⟧ = ⟦[]⟧ (⟦,⟧ ⟦I⟧ ↘⟦s′⟧) ↘⟦t′⟧
                                     ; t≈t′ = t≈t′
                                     }

Λ-η′ : Γ ⊨ t ∶ Π S T →
       ----------------------------------
       Γ ⊨ t ≈ Λ (t [ wk ] $ v 0) ∶ Π S T
Λ-η′ {_} {t} {S} {T} (⊨Γ , n , ⊨t) = ⊨Γ , _ , helper
  where
    helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
             ---------------------------------------------------------------------
             Σ (RelTyp _ (Π S T) ρ (Π S T) ρ′)
             λ rel → RelExp t ρ (Λ (t [ wk ] $ v 0)) ρ′ (El _ (RelTyp.T≈T′ rel))
    helper {ρ} {ρ′} ρ≈ρ′
      with ⊨t ρ≈ρ′
    ...  | ⊨ΠST@(record { ↘⟦T⟧ = ⟦Π⟧ _ ; ↘⟦T′⟧ = ⟦Π⟧ _ ; T≈T′ = Π iS T≈T′ })
         , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ } = ⊨ΠST , record
                                   { ↘⟦t⟧ = ↘⟦t⟧
                                   ; ↘⟦t′⟧ = ⟦Λ⟧ _
                                   ; t≈t′ = helper′
                                   }
      where
        helper′ : {a b : D} (κ : UMoT) (inp : a ≈ b ∈ El _ (iS κ)) →
                  -----------------------------------------------------------------------------------
                  Π̂ (⟦t⟧ [ κ ]) a ((Λ (t [ wk ] $ v 0) ρ′) [ κ ]) b (El _ (ΠRT.T≈T′ (T≈T′ κ inp)))
        helper′ {a} {b} κ inp
          with record { ↘fa = ↘fa ; ↘fa′ = ↘fa′ ; fa≈fa′ = fa≈fa′ } ← t≈t′ κ inp = record
                                   { ↘fa = ↘fa
                                   ; ↘fa′ = Λ∙ (⟦$⟧ (⟦[]⟧ ⟦wk⟧ (subst (⟦ t ⟧_↘ ⟦t′⟧ [ κ ]) (sym (drop-↦ _ _)) (⟦⟧-mon κ ↘⟦t′⟧))) (⟦v⟧ 0) ↘fa′)
                                   ; fa≈fa′ = fa≈fa′
                                   }

Λ-[]′ : Γ ⊨s σ ∶ Δ →
        S ∺ Δ ⊨ t ∶ T →
        --------------------------------------------
        Γ ⊨ Λ t [ σ ] ≈ Λ (t [ q σ ]) ∶ Π S T [ σ ]
Λ-[]′ {_} {σ} {_} {S} {t} {T} (⊨Γ , ⊨Δ , ⊨σ) (∺-cong ⊨Δ₁ Srel₁ , n₁ , ⊨t) = ⊨Γ , _ , helper
  where
    helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
             ------------------------------------------------------------------------------
             Σ (RelTyp _ (Π S T [ σ ]) ρ (Π S T [ σ ]) ρ′)
             λ rel → RelExp (Λ t [ σ ]) ρ (Λ (t [ q σ ])) ρ′ (El _ (RelTyp.T≈T′ rel))
    helper {ρ} {ρ′} ρ≈ρ′
      with record { ⟦σ⟧ = ⟦σ⟧ ; ⟦δ⟧ = ⟦δ⟧ ; ↘⟦σ⟧ = ↘⟦σ⟧ ; ↘⟦δ⟧ = ↘⟦δ⟧ ; σ≈δ = σ≈δ } ← ⊨σ ρ≈ρ′
        with record { ↘⟦T⟧ = ↘⟦S⟧ ; ↘⟦T′⟧ = ↘⟦S′⟧ ; T≈T′ = S≈S′ } ← Srel₁ (⊨-irrel ⊨Δ ⊨Δ₁ σ≈δ) = record
                          { ↘⟦T⟧ = ⟦[]⟧ ↘⟦σ⟧ (⟦Π⟧ ↘⟦S⟧)
                          ; ↘⟦T′⟧ = ⟦[]⟧ ↘⟦δ⟧ (⟦Π⟧ ↘⟦S′⟧)
                          ; T≈T′ = Π (λ κ → 𝕌-mon κ (𝕌-cumu (m≤m⊔n _ n₁) S≈S′)) return
                          }
                        , record
                          { ↘⟦t⟧ = ⟦[]⟧ ↘⟦σ⟧ (⟦Λ⟧ _)
                          ; ↘⟦t′⟧ = ⟦Λ⟧ _
                          ; t≈t′ = result
                          }
      where
        helper′ : {a b : D} (κ : UMoT) (inp : a ≈ b ∈ El _ (𝕌-mon κ (𝕌-cumu (m≤m⊔n _ n₁) S≈S′))) →
                  -----------------------------------------------------------------------------------
                  Σ (RelTyp n₁ T (⟦σ⟧ [ κ ] ↦ a) T (⟦δ⟧ [ κ ] ↦ b))
                  λ rel → RelExp t (⟦σ⟧ [ κ ] ↦ a) t (⟦δ⟧ [ κ ] ↦ b) (El _ (RelTyp.T≈T′ rel))
        helper′ {a} {b} κ inp = ⊨t (σ≈δ₁ , a≈b)
          where
            σ≈δ₁ : drop (⟦σ⟧ [ κ ] ↦ a) ≈ drop (⟦δ⟧ [ κ ] ↦ b) ∈ ⟦ ⊨Δ₁ ⟧ρ
            σ≈δ₁
              rewrite drop-↦ (⟦σ⟧ [ κ ]) a
                    | drop-↦ (⟦δ⟧ [ κ ]) b = ⟦⟧ρ-mon ⊨Δ₁ κ (⊨-irrel ⊨Δ ⊨Δ₁ σ≈δ)

            a≈b : a ≈ b ∈ El _ (RelTyp.T≈T′ (Srel₁ σ≈δ₁))
            a≈b
              with record { ↘⟦T⟧ = ↘⟦S⟧₁ ; ↘⟦T′⟧ = ↘⟦S′⟧₁ ; T≈T′ = S≈S′₁ } ← Srel₁ σ≈δ₁
                rewrite drop-↦ (⟦σ⟧ [ κ ]) a
                      | drop-↦ (⟦δ⟧ [ κ ]) b
                      | ⟦⟧-det ↘⟦S⟧₁ (⟦⟧-mon κ ↘⟦S⟧)
                      | ⟦⟧-det ↘⟦S′⟧₁ (⟦⟧-mon κ ↘⟦S′⟧) = 𝕌-irrel (𝕌-mon κ (𝕌-cumu (m≤m⊔n _ n₁) S≈S′)) S≈S′₁ inp

        return : {a b : D} (κ : UMoT) →
                 a ≈ b ∈ El _ (𝕌-mon κ (𝕌-cumu (m≤m⊔n _ n₁) S≈S′)) →
                 -------------------------------------------------------
                 ΠRT T (⟦σ⟧ [ κ ] ↦ a) T (⟦δ⟧ [ κ ] ↦ b) (𝕌 (_ ⊔ n₁))
        return κ inp
          with record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ } ← proj₁ (helper′ κ inp) = record
                           { ↘⟦T⟧ = ↘⟦T⟧
                           ; ↘⟦T′⟧ = ↘⟦T′⟧
                           ; T≈T′ = 𝕌-cumu (m≤n⊔m _ _) T≈T′
                           }

        result : {a b : D} (κ : UMoT) (inp : a ≈ b ∈ El _ (𝕌-mon κ (𝕌-cumu (m≤m⊔n _ n₁) S≈S′))) →
                 -------------------------------------------------------------------------------------
                 Π̂ (Λ t ⟦σ⟧ [ κ ]) a ((Λ (t [ q σ ]) ρ′) [ κ ]) b (El _ (ΠRT.T≈T′ (return κ inp)))
        result {a} {b} κ inp
          with helper′ κ inp
        ...  | record { T≈T′ = T≈T′ }
             , record { ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ } = record
                          { ↘fa = Λ∙ ↘⟦t⟧
                          ; ↘fa′ = Λ∙ (⟦[]⟧ (⟦q⟧ (subst (⟦ σ ⟧s_↘ ⟦δ⟧ [ κ ]) (sym (drop-↦ _ _)) (⟦⟧s-mon κ ↘⟦δ⟧))) ↘⟦t′⟧)
                          ; fa≈fa′ = 𝕌-irrel T≈T′ (𝕌-cumu (m≤n⊔m _ _) T≈T′) t≈t′
                          }

$-[]′ : Γ ⊨s σ ∶ Δ →
        Δ ⊨ r ∶ Π S T →
        Δ ⊨ s ∶ S →
        ---------------------------------------------------------
        Γ ⊨ (r $ s) [ σ ] ≈ r [ σ ] $ s [ σ ] ∶ T [ σ , s [ σ ] ]
$-[]′ {_} {σ} {_} {r} {S} {T} {s} (⊨Γ , ⊨Δ , ⊨σ) (⊨Δ₁ , _ , ⊨r) (⊨Δ₂ , _ , ⊨s) = ⊨Γ , _ , helper
  where
    helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
             ----------------------------------------------------------------------------------
             Σ (RelTyp _ (T [ σ , s [ σ ] ]) ρ (T [ σ , s [ σ ] ]) ρ′)
             λ rel → RelExp ((r $ s) [ σ ]) ρ (r [ σ ] $ s [ σ ]) ρ′ (El _ (RelTyp.T≈T′ rel))
    helper {ρ} {ρ′} ρ≈ρ′
      with record { ⟦σ⟧ = ⟦σ⟧ ; ⟦δ⟧ = ⟦δ⟧ ; ↘⟦σ⟧ = ↘⟦σ⟧ ; ↘⟦δ⟧ = ↘⟦δ⟧ ; σ≈δ = σ≈δ } ← ⊨σ ρ≈ρ′
        with ⊨r (⊨-irrel ⊨Δ ⊨Δ₁ σ≈δ)
           | ⊨s (⊨-irrel ⊨Δ ⊨Δ₂ σ≈δ)
    ...    | record { ↘⟦T⟧ = ⟦Π⟧ ↘⟦S⟧ ; ↘⟦T′⟧ = ⟦Π⟧ ↘⟦S′⟧ ; T≈T′ = Π iS Trel }
           , record { ⟦t⟧ = ⟦r⟧ ; ⟦t′⟧ = ⟦r′⟧ ; ↘⟦t⟧ = ↘⟦r⟧ ; ↘⟦t′⟧ = ↘⟦r′⟧ ; t≈t′ = r≈r′ }
           | record { ⟦T⟧ = ⟦S⟧₁ ; ⟦T′⟧ = ⟦S′⟧₁ ; ↘⟦T⟧ = ↘⟦S⟧₁ ; ↘⟦T′⟧ = ↘⟦S′⟧₁ ; T≈T′ = S≈S′₁ }
           , record { ⟦t⟧ = ⟦s⟧ ; ⟦t′⟧ = ⟦s′⟧ ; ↘⟦t⟧ = ↘⟦s⟧ ; ↘⟦t′⟧ = ↘⟦s′⟧ ; t≈t′ = s≈s′ }
           with S≈S′ ← iS vone
              | Trel₁ ← Trel {⟦s⟧} {⟦s′⟧} vone
              | r≈r′₁ ← r≈r′ {⟦s⟧} {⟦s′⟧} vone
             rewrite ⟦⟧-det ↘⟦S⟧ ↘⟦S⟧₁
                   | ⟦⟧-det ↘⟦S′⟧ ↘⟦S′⟧₁
                   | ρ-ap-vone ⟦σ⟧ 
                   | ρ-ap-vone ⟦δ⟧
                   | D-ap-vone ⟦r⟧
                   | D-ap-vone ⟦r′⟧
                   | D-ap-vone ⟦S⟧₁
                   | D-ap-vone ⟦S′⟧₁
                with record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ } ← Trel₁ (𝕌-irrel S≈S′₁ S≈S′ s≈s′)
                   | record { ↘fa = ↘fa ; ↘fa′ = ↘fa′ ; fa≈fa′ = fa≈fa′ } ← r≈r′₁ (𝕌-irrel S≈S′₁ S≈S′ s≈s′) = record
                                      { ↘⟦T⟧ = ⟦[]⟧ (⟦,⟧ ↘⟦σ⟧ (⟦[]⟧ ↘⟦σ⟧ ↘⟦s⟧)) ↘⟦T⟧
                                      ; ↘⟦T′⟧ = ⟦[]⟧ (⟦,⟧ ↘⟦δ⟧ (⟦[]⟧ ↘⟦δ⟧ ↘⟦s′⟧)) ↘⟦T′⟧
                                      ; T≈T′ = T≈T′
                                      }
                                    , record
                                      { ↘⟦t⟧ = ⟦[]⟧ ↘⟦σ⟧ (⟦$⟧ ↘⟦r⟧ ↘⟦s⟧ ↘fa)
                                      ; ↘⟦t′⟧ = ⟦$⟧ (⟦[]⟧ ↘⟦δ⟧ ↘⟦r′⟧) (⟦[]⟧ ↘⟦δ⟧ ↘⟦s′⟧) ↘fa′
                                      ; t≈t′ = fa≈fa′
                                      }
