{-# OPTIONS --without-K --safe #-}

open import Level using ()
open import Axiom.Extensionality.Propositional

module kMLTT.Completeness.Pi (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Data.Nat.Properties

open import Lib
open import kMLTT.Completeness.LogRel
open import kMLTT.Completeness.Substitutions fext
open import kMLTT.Completeness.Terms fext

open import kMLTT.Semantics.Properties.Domain fext
open import kMLTT.Semantics.Properties.Evaluation fext
open import kMLTT.Semantics.Properties.PER fext


Π-[]′ : ∀ {i} →
        Γ ⊨s σ ∶ Δ →
        Δ ⊨ S ∶ Se i →
        S ∺ Δ ⊨ T ∶ Se i →
        -------------------------------------------------
        Γ ⊨ Π S T [ σ ] ≈ Π (S [ σ ]) (T [ q σ ]) ∶ Se i
Π-[]′ {_} {σ} {_} {S} {T} {i} (⊨Γ , ⊨Δ , ⊨σ) (⊨Δ₁ , _ , ⊨S) (∷-cong ⊨Δ₂ rel , _ , ⊨T) = ⊨Γ , _ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp _ (Se i) ρ (Se i) ρ′) (λ rel → RelExp (Π S T [ σ ]) ρ (Π (S [ σ ]) (T [ q σ ])) ρ′ (El _ (RelTyp.T≈T′ rel)))
        helper {ρ} {ρ′} ρ≈ρ′ = help
          where module σ = RelSubsts (⊨σ ρ≈ρ′)
                help : Σ (RelTyp _ (Se i) ρ (Se i) ρ′) (λ rel → RelExp (Π S T [ σ ]) ρ (Π (S [ σ ]) (T [ q σ ])) ρ′ (El _ (RelTyp.T≈T′ rel)))
                help
                  with ⊨S (⊨-irrel ⊨Δ ⊨Δ₁ σ.σ≈δ)
                ...  | record { ⟦T⟧ = .(U i) ; ⟦T′⟧ = .(U i) ; ↘⟦T⟧ = (⟦Se⟧ .i) ; ↘⟦T′⟧ = (⟦Se⟧ .i) ; T≈T′ = PERDef.U i<j eq }
                     , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
                     = record
                        { ⟦T⟧   = U i
                        ; ⟦T′⟧  = U i
                        ; ↘⟦T⟧  = ⟦Se⟧ i
                        ; ↘⟦T′⟧ = ⟦Se⟧ i
                        ; T≈T′  = PERDef.U i<j eq
                        }
                     , record
                         { ⟦t⟧   = Π ⟦t⟧ T σ.⟦σ⟧
                         ; ⟦t′⟧  = Π ⟦t′⟧ (T [ q σ ]) ρ′
                         ; ↘⟦t⟧  = ⟦[]⟧ σ.↘⟦σ⟧ (⟦Π⟧ ↘⟦t⟧)
                         ; ↘⟦t′⟧ = ⟦Π⟧ (⟦[]⟧ σ.↘⟦δ⟧ ↘⟦t′⟧)
                         ; t≈t′  = subst (Π ⟦t⟧ T σ.⟦σ⟧ ≈ Π ⟦t′⟧ (T [ q σ ]) ρ′ ∈_) (sym (𝕌-wellfounded-≡-𝕌 _ i<j))
                                         (result (subst (⟦t⟧ ≈ ⟦t′⟧ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<j) t≈t′))
                         }
                  where result : ⟦t⟧ ≈ ⟦t′⟧ ∈ 𝕌 i → Π ⟦t⟧ T σ.⟦σ⟧ ≈ Π ⟦t′⟧ (sub T (q σ)) ρ′ ∈ 𝕌 i
                        result S≈ = Π (λ κ → 𝕌-mon κ S≈) step
                          where step : (κ : UMoT) → a ≈ a′ ∈ El i (𝕌-mon κ S≈) → ΠRT T (σ.⟦σ⟧ [ κ ] ↦ a) (T [ q σ ]) (ρ′ [ κ ] ↦ a′) (𝕌 i)
                                step {a} {a′} κ a≈a′
                                  with subst₂ (_≈_∈ ⟦ ⊨Δ₂ ⟧ρ) (sym (drop-↦ _ _)) (sym (drop-↦ _ _)) (⊨-irrel ⊨Δ ⊨Δ₂ (⟦⟧ρ-mon ⊨Δ κ σ.σ≈δ))
                                ...  | σ≈δ₁ = answer
                                  where insert : a ≈ a′ ∈ El _ (RelTyp.T≈T′ (rel σ≈δ₁))
                                        insert
                                          with rel σ≈δ₁
                                        ...  | record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
                                             rewrite ⟦⟧-det (subst (⟦ S ⟧_↘ ⟦T⟧) (drop-↦ _ _) ↘⟦T⟧) (⟦⟧-mon κ ↘⟦t⟧)
                                                   | ⟦⟧-det (subst (⟦ S ⟧_↘ ⟦T′⟧) (drop-↦ _ _) ↘⟦T′⟧) (⟦⟧-mon κ ↘⟦t′⟧) = 𝕌-irrel (𝕌-mon κ S≈) T≈T′ a≈a′

                                        answer : ΠRT T (σ.⟦σ⟧ [ κ ] ↦ a) (T [ q σ ]) (ρ′ [ κ ] ↦ a′) (𝕌 i)
                                        answer
                                          with ⊨T {σ.⟦σ⟧ [ κ ] ↦ a} {σ.⟦δ⟧ [ κ ] ↦ a′} (σ≈δ₁ , insert)
                                        ...  | record { ⟦T⟧ = .(U i) ; ⟦T′⟧ = .(U i) ; ↘⟦T⟧ = (⟦Se⟧ .i) ; ↘⟦T′⟧ = (⟦Se⟧ .i) ; T≈T′ = PERDef.U i<j eq }
                                             , re = record
                                                      { ⟦T⟧   = re.⟦t⟧
                                                      ; ⟦T′⟧  = re.⟦t′⟧
                                                      ; ↘⟦T⟧  = re.↘⟦t⟧
                                                      ; ↘⟦T′⟧ = ⟦[]⟧ (⟦,⟧ (⟦∘⟧ ⟦wk⟧ (subst (⟦ σ ⟧s_↘ σ.⟦δ⟧ [ κ ]) (sym (drop-↦ _ _)) (⟦⟧s-mon κ σ.↘⟦δ⟧))) (⟦v⟧ 0)) re.↘⟦t′⟧
                                                      ; T≈T′  = subst (re.⟦t⟧ ≈ re.⟦t′⟧ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<j) re.t≈t′
                                                      }
                                          where module re = RelExp re


Π-cong′ : ∀ {i} →
          Γ ⊨ S ≈ S′ ∶ Se i →
          S ∺ Γ ⊨ T ≈ T′ ∶ Se i →
          --------------------------
          Γ ⊨ Π S T ≈ Π S′ T′ ∶ Se i
Π-cong′ {_} {S} {S′} {T} {T′} {i} (⊨Γ , _ , S≈S′) (∷-cong ⊨Γ₁ rel , _ , T≈T′) = ⊨Γ , _ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp _ (Se i) ρ (Se i) ρ′) (λ rel → RelExp (Π S T) ρ (Π S′ T′) ρ′ (El _ (RelTyp.T≈T′ rel)))
        helper {ρ} {ρ′} ρ≈ρ′
          with S≈S′ ρ≈ρ′
        ...  | record { ⟦T⟧ = .(U i) ; ⟦T′⟧ = .(U i) ; ↘⟦T⟧ = (⟦Se⟧ .i) ; ↘⟦T′⟧ = (⟦Se⟧ .i) ; T≈T′ = PERDef.U i<j eq }
             , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
             rewrite 𝕌-wellfounded-≡-𝕌 _ i<j = record
                                                 { ⟦T⟧   = U i
                                                 ; ⟦T′⟧  = U i
                                                 ; ↘⟦T⟧  = ⟦Se⟧ i
                                                 ; ↘⟦T′⟧ = ⟦Se⟧ i
                                                 ; T≈T′  = PERDef.U i<j eq
                                                 }
                                             , record
                                                 { ⟦t⟧   = Π ⟦t⟧ T ρ
                                                 ; ⟦t′⟧  = Π ⟦t′⟧ T′ ρ′
                                                 ; ↘⟦t⟧  = ⟦Π⟧ ↘⟦t⟧
                                                 ; ↘⟦t′⟧ = ⟦Π⟧ ↘⟦t′⟧
                                                 ; t≈t′  = subst (Π ⟦t⟧ T ρ ≈ Π ⟦t′⟧ T′ ρ′ ∈_) (sym (𝕌-wellfounded-≡-𝕌 _ i<j)) (Π (λ κ → 𝕌-mon κ t≈t′) result)
                                                 }
          where result : (κ : UMoT) → a ≈ a′ ∈ El i (𝕌-mon κ t≈t′) → ΠRT T (ρ [ κ ] ↦ a) T′ (ρ′ [ κ ] ↦ a′) (𝕌 i)
                result {a} {a′} κ a≈a′
                  with subst₂ (_≈_∈ ⟦ ⊨Γ₁ ⟧ρ) (sym (drop-↦ _ _)) (sym (drop-↦ _ _)) (⊨-irrel ⊨Γ ⊨Γ₁ (⟦⟧ρ-mon ⊨Γ κ ρ≈ρ′))
                ...  | ρ≈ρ′₁ = answer
                  where insert : a ≈ a′ ∈ El _ (RelTyp.T≈T′ (rel ρ≈ρ′₁))
                        insert
                          with rel ρ≈ρ′₁
                        ...  | record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
                             rewrite ⟦⟧-det (subst (⟦ S ⟧_↘ ⟦T⟧) (drop-↦ _ _) ↘⟦T⟧) (⟦⟧-mon κ ↘⟦t⟧) = El-one-sided (𝕌-mon κ t≈t′) T≈T′ a≈a′

                        answer : ΠRT T (ρ [ κ ] ↦ a) T′ (ρ′ [ κ ] ↦ a′) (𝕌 i)
                        answer
                          with T≈T′ {ρ [ κ ] ↦ a} {ρ′ [ κ ] ↦ a′} (ρ≈ρ′₁ , insert)
                        ...  | record { ⟦T⟧ = .(U i) ; ⟦T′⟧ = .(U i) ; ↘⟦T⟧ = (⟦Se⟧ .i) ; ↘⟦T′⟧ = (⟦Se⟧ .i) ; T≈T′ = PERDef.U i<j eq }
                             , re = record
                                      { ⟦T⟧   = re.⟦t⟧
                                      ; ⟦T′⟧  = re.⟦t′⟧
                                      ; ↘⟦T⟧  = re.↘⟦t⟧
                                      ; ↘⟦T′⟧ = re.↘⟦t′⟧
                                      ; T≈T′  = subst (re.⟦t⟧ ≈ re.⟦t′⟧ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<j) re.t≈t′
                                      }
                          where module re = RelExp re


Λ-cong′ : S ∺ Γ ⊨ t ≈ t′ ∶ T →
          -----------------------
          Γ ⊨ Λ t ≈ Λ t′ ∶ Π S T
Λ-cong′ {S} {_} {t} {t′} {T} (∷-cong {i = j} ⊨Γ rel , i , t≈t′) = ⊨Γ , max j i , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp _ (Π S T) ρ (Π S T) ρ′) (λ rel → RelExp (Λ t) ρ (Λ t′) ρ′ (El _ (RelTyp.T≈T′ rel)))
        helper {ρ} {ρ′} ρ≈ρ′ = record
                                 { ⟦T⟧   = Π S.⟦T⟧ T ρ
                                 ; ⟦T′⟧  = Π S.⟦T′⟧ T ρ′
                                 ; ↘⟦T⟧  = ⟦Π⟧ S.↘⟦T⟧
                                 ; ↘⟦T′⟧ = ⟦Π⟧ S.↘⟦T′⟧
                                 ; T≈T′  = Π (λ κ → 𝕌-cumu (m≤m⊔n _ _) (𝕌-mon κ S.T≈T′)) λ κ a≈b → proj₁ (Πres κ a≈b)
                                 }
                             , record
                                 { ⟦t⟧   = Λ t ρ
                                 ; ⟦t′⟧  = Λ t′ ρ′
                                 ; ↘⟦t⟧  = ⟦Λ⟧ t
                                 ; ↘⟦t′⟧ = ⟦Λ⟧ t′
                                 ; t≈t′  = λ κ a≈b → proj₂ (Πres κ a≈b)
                                 }
             where module S = RelTyp (rel ρ≈ρ′)
                   insert : (⊨Γ : ⊨ Γ) →
                            (rel : ∀ {ρ ρ′} → ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → RelTyp _ S ρ S ρ′) →
                            (κ : UMoT) (ρ≈ρ′ : drop (ρ [ κ ] ↦ a) ≈ drop (ρ′ [ κ ] ↦ a′) ∈ ⟦ ⊨Γ ⟧ρ) →
                            a ≈ a′ ∈ El _ (𝕌-cumu (m≤m⊔n _ i) (𝕌-mon κ S.T≈T′)) →
                            a ≈ a′ ∈ El _ (RelTyp.T≈T′ (rel ρ≈ρ′))
                   insert ⊨Γ rel κ ρ≈ρ′ a≈a′
                     with rel ρ≈ρ′
                   ...  | record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
                        rewrite ⟦⟧-det (subst (⟦ S ⟧_↘ ⟦T⟧) (drop-↦ _ _) ↘⟦T⟧) (⟦⟧-mon κ S.↘⟦T⟧) = El-one-sided (𝕌-cumu (m≤m⊔n _ i) (𝕌-mon κ S.T≈T′)) T≈T′ a≈a′

                   Πres : (κ : UMoT) (a≈b : a ≈ b ∈ El _ (𝕌-cumu (m≤m⊔n _ i) (𝕌-mon κ S.T≈T′))) →
                          Σ (ΠRT T (ρ [ κ ] ↦ a) T (ρ′ [ κ ] ↦ b) (𝕌 _))
                            λ rel → Π̂ (Λ t (ρ [ κ ])) a (Λ t′ (ρ′ [ κ ])) b (El _ (ΠRT.T≈T′ rel))
                   Πres {a} {b} κ a≈b
                     with subst₂ (_≈_∈ ⟦ ⊨Γ ⟧ρ) (sym (drop-↦ _ _)) (sym (drop-↦ _ _)) (⟦⟧ρ-mon ⊨Γ κ ρ≈ρ′)
                   ...  | ρ≈ρ′₁ = answer
                     where answer : Σ (ΠRT T (ρ [ κ ] ↦ a) T (ρ′ [ κ ] ↦ b) (𝕌 _))
                                      λ rel → Π̂ (Λ t (ρ [ κ ])) a (Λ t′ (ρ′ [ κ ])) b (El _ (ΠRT.T≈T′ rel))
                           answer
                             with t≈t′ {ρ [ κ ] ↦ a} {ρ′ [ κ ] ↦ b} (ρ≈ρ′₁ , insert ⊨Γ rel κ ρ≈ρ′₁ a≈b)
                           ...  | record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
                                , re = record
                                         { ⟦T⟧   = ⟦T⟧
                                         ; ⟦T′⟧  = ⟦T′⟧
                                         ; ↘⟦T⟧  = ↘⟦T⟧
                                         ; ↘⟦T′⟧ = ↘⟦T′⟧
                                         ; T≈T′  = T≈T′₁
                                         }
                                     , record
                                         { fa     = re.⟦t⟧
                                         ; fa′    = re.⟦t′⟧
                                         ; ↘fa    = Λ∙ re.↘⟦t⟧
                                         ; ↘fa′   = Λ∙ re.↘⟦t′⟧
                                         ; fa≈fa′ = 𝕌-irrel T≈T′ T≈T′₁ re.t≈t′
                                         }
                             where module re = RelExp re
                                   T≈T′₁ = 𝕌-cumu (m≤n⊔m _ i) T≈T′


$-cong′ : Γ ⊨ r ≈ r′ ∶ Π S T →
          Γ ⊨ s ≈ s′ ∶ S →
          -------------------------------
          Γ ⊨ r $ s ≈ r′ $ s′ ∶ T [| s ]
$-cong′ {_} {r} {r′} {S} {T} {s} {s′} (⊨Γ , _ , r≈r′) (⊨Γ₁ , _ , s≈s′) = ⊨Γ , _ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp _ (T [| s ]) ρ (T [| s ]) ρ′) (λ rel → RelExp (r $ s) ρ (r′ $ s′) ρ′ (El _ (RelTyp.T≈T′ rel)))
        helper {ρ} {ρ′} ρ≈ρ′
          with ⊨-irrel ⊨Γ ⊨Γ₁ (⟦⟧ρ-refl ⊨Γ ⊨Γ ρ≈ρ′) | ⊨-irrel ⊨Γ ⊨Γ₁ (⟦⟧ρ-sym′ ⊨Γ ρ≈ρ′)
        ...  | ρ≈ρ | ρ′≈ρ
          with r≈r′ ρ≈ρ′
             | s≈s′ ρ≈ρ
             | s≈s′ ρ′≈ρ
             | s≈s′ (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ′)
        ...  | record { ⟦T⟧ = .(Π _ T _) ; ⟦T′⟧ = .(Π _ T _) ; ↘⟦T⟧ = ⟦Π⟧ ↘⟦S⟧ ; ↘⟦T′⟧ = ⟦Π⟧ ↘⟦S⟧′ ; T≈T′ = PERDef.Π iA RT }
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
                                           { ⟦T⟧   = RT.⟦T⟧
                                           ; ⟦T′⟧  = RT.⟦T′⟧
                                           ; ↘⟦T⟧  = ⟦[]⟧ (⟦,⟧ ⟦I⟧ ↘⟦t⟧) (subst (λ x → ⟦ T ⟧ x ↦ ⟦t⟧ ↘ RT.⟦T⟧) (ρ-ap-vone _) RT.↘⟦T⟧)
                                           ; ↘⟦T′⟧ = ⟦[]⟧ (⟦,⟧ ⟦I⟧ ↘⟦t⟧₂) (subst (λ x → ⟦ T ⟧ x ↦ ⟦t⟧₂ ↘ RT.⟦T′⟧) (ρ-ap-vone _) RT.↘⟦T′⟧)
                                           ; T≈T′  = RT.T≈T′
                                           }
                                       , record
                                           { ⟦t⟧   = rs.fa
                                           ; ⟦t′⟧  = rs.fa′
                                           ; ↘⟦t⟧  = ⟦$⟧ ↘⟦r⟧ ↘⟦t⟧ (subst (_∙ ⟦t⟧ ↘ rs.fa) (D-ap-vone _) rs.↘fa)
                                           ; ↘⟦t′⟧ = ⟦$⟧ ↘⟦r′⟧ ↘⟦t′⟧ (subst (_∙ ⟦t′⟧ ↘ rs.fa′) (D-ap-vone _) rs.↘fa′)
                                           ; t≈t′  = El-transp RT′.T≈T′ RT.T≈T′ rs.fa≈fa′ (sym (⟦⟧-det RT.↘⟦T⟧ RT′.↘⟦T⟧))
                                           }
          where T≈T  = 𝕌-trans T≈T′₁ (𝕌-sym T≈T′₂)
                srel = El-trans T≈T′₁ (𝕌-sym T≈T′₂) T≈T t≈t′₁ (El-sym T≈T′₂ (𝕌-sym T≈T′₂) t≈t′₂)

                module RT  = ΠRT (RT vone (El-transp T≈T (iA vone) srel (sym (D-ap-vone _))))
                module RT′ = ΠRT (RT vone (El-transp T≈T′ (iA vone) t≈t′ (sym (D-ap-vone _))))
                module rs  = Π̂ (r≈r′ vone (El-transp T≈T′ (iA vone) t≈t′ (sym (D-ap-vone _))))


Λ-β′        : S ∺ Γ ⊨ t ∶ T →
              Γ ⊨ s ∶ S →
              ----------------------------------
              Γ ⊨ Λ t $ s ≈ t [| s ] ∶ T [| s ]
Λ-β′ {S} {_} {t} {T} {s} (∷-cong ⊨Γ rel , n , ⊨t) (⊨Γ₁ , _ , ⊨s) = ⊨Γ , _ , helper
  where
    helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp n (T [| s ]) ρ (T [| s ]) ρ′) (λ rel → RelExp (Λ t $ s) ρ (t [| s ]) ρ′ (El _ (RelTyp.T≈T′ rel)))
    helper {ρ} {ρ′} ρ≈ρ′
      with ⊨s (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ′)
    ...  | record { ⟦T⟧ = ⟦S⟧ ; ⟦T′⟧ = ⟦S′⟧ ; ↘⟦T⟧ = ↘⟦S⟧ ; ↘⟦T′⟧ = ↘⟦S′⟧ ; T≈T′ = S≈S′ }
         , record { ⟦t⟧ = ⟦s⟧ ; ⟦t′⟧ = ⟦s′⟧ ; ↘⟦t⟧ = ↘⟦s⟧ ; ↘⟦t′⟧ = ↘⟦s′⟧ ; t≈t′ = s≈s′ } = helper′
      where
        ρ≈ρ′₁ : drop (ρ ↦ ⟦s⟧) ≈ drop (ρ′ ↦ ⟦s′⟧) ∈ ⟦ ⊨Γ ⟧ρ
        ρ≈ρ′₁
         rewrite drop-↦ ρ ⟦s⟧
               | drop-↦ ρ′ ⟦s′⟧ = ρ≈ρ′

        s≈s′₁ : ⟦s⟧ ≈ ⟦s′⟧ ∈ El _ (RelTyp.T≈T′ (rel ρ≈ρ′₁))
        s≈s′₁
          with rel ρ≈ρ′₁
        ...  | record { ⟦T⟧ = ⟦S⟧₁ ; ⟦T′⟧ = ⟦S′⟧₁ ; ↘⟦T⟧ = ↘⟦S⟧₁ ; ↘⟦T′⟧ = ↘⟦S′⟧₁ ; T≈T′ = S≈S′₁ }
            rewrite drop-↦ ρ ⟦s⟧
                  | drop-↦ ρ′ ⟦s′⟧
                  | ⟦⟧-det ↘⟦S⟧ ↘⟦S⟧₁
                  | ⟦⟧-det ↘⟦S′⟧ ↘⟦S′⟧₁
                  = 𝕌-irrel S≈S′ S≈S′₁ s≈s′

        helper′ : Σ (RelTyp n (T [| s ]) ρ (T [| s ]) ρ′) (λ rel → RelExp (Λ t $ s) ρ (t [| s ]) ρ′ (El _ (RelTyp.T≈T′ rel)))
        helper′
          with ⊨t (ρ≈ρ′₁ , s≈s′₁)
        ... | record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
            , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ } = record
                                     { ⟦T⟧ = ⟦T⟧
                                     ; ⟦T′⟧ = ⟦T′⟧
                                     ; ↘⟦T⟧ = ⟦[]⟧ (⟦,⟧ ⟦I⟧ ↘⟦s⟧) ↘⟦T⟧
                                     ; ↘⟦T′⟧ = ⟦[]⟧ ((⟦,⟧ ⟦I⟧ ↘⟦s′⟧)) ↘⟦T′⟧
                                     ; T≈T′ = T≈T′
                                     }
                                   , record
                                     { ⟦t⟧ = ⟦t⟧
                                     ; ⟦t′⟧ = ⟦t′⟧
                                     ; ↘⟦t⟧ = ⟦$⟧ (⟦Λ⟧ t) ↘⟦s⟧ (Λ∙ ↘⟦t⟧)
                                     ; ↘⟦t′⟧ = ⟦[]⟧ (⟦,⟧ ⟦I⟧ ↘⟦s′⟧) ↘⟦t′⟧
                                     ; t≈t′ = t≈t′
                                     }

        x = ⊨t (ρ≈ρ′₁ , s≈s′₁)

-- Λ-η′        : Γ ⊨ t ∶ Π S T →
--               ----------------------------------
--               Γ ⊨ t ≈ Λ (t [ wk ] $ v 0) ∶ Π S T
-- Λ-[]′       : Γ ⊨s σ ∶ Δ →
--               S ∺ Δ ⊨ t ∶ T →
--               --------------------------------------------
--               Γ ⊨ Λ t [ σ ] ≈ Λ (t [ q σ ]) ∶ Π S T [ σ ]
-- $-[]′       : Γ ⊨s σ ∶ Δ →
--               Δ ⊨ r ∶ Π S T →
--               Δ ⊨ s ∶ S →
--               ---------------------------------------------------------
--               Γ ⊨ (r $ s) [ σ ] ≈ r [ σ ] $ s [ σ ] ∶ T [ σ , s [ σ ] ]
