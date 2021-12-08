{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Completeness.Box (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Data.Nat.Properties

open import Lib
open import kMLTT.Completeness.LogRel

open import kMLTT.Semantics.Properties.Domain fext
open import kMLTT.Semantics.Properties.Evaluation fext
open import kMLTT.Semantics.Properties.PER fext


□-[]′ : ∀ {i} →
        Γ ⊨s σ ∶ Δ →
        ([] ∷⁺ Δ) ⊨ T ∶ Se i →
        ---------------------------------------
        Γ ⊨ □ T [ σ ] ≈ □ (T [ σ ； 1 ]) ∶ Se i
□-[]′ {_} {σ} {_} {T} {i} (⊨Γ , ⊨Δ , ⊨σ) (κ-cong ⊨Δ₁ , _ , ⊨T) = ⊨Γ , _ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp _ (Se i) ρ (Se i) ρ′) (λ rel → RelExp (□ T [ σ ]) ρ (□ (T [ σ ； 1 ])) ρ′ (El _ (RelTyp.T≈T′ rel)))
        helper {ρ} {ρ′} ρ≈ρ′ = help
          where module σ = RelSubsts (⊨σ ρ≈ρ′)
                help : Σ (RelTyp _ (Se i) ρ (Se i) ρ′) (λ rel → RelExp (□ T [ σ ]) ρ (□ (T [ σ ； 1 ])) ρ′ (El _ (RelTyp.T≈T′ rel)))
                help
                  with ⊨T {ext σ.⟦σ⟧ 1} {ext σ.⟦δ⟧ 1} (⊨-irrel ⊨Δ ⊨Δ₁ σ.σ≈δ , refl)
                ...  | record { ↘⟦T⟧ = ⟦Se⟧ .i ; ↘⟦T′⟧ = ⟦Se⟧ .i ; T≈T′ = PERDef.U i<j _ }
                     , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
                     rewrite 𝕌-wellfounded-≡-𝕌 _ i<j = record
                                                         { ⟦T⟧   = U i
                                                         ; ⟦T′⟧  = U i
                                                         ; ↘⟦T⟧  = ⟦Se⟧ i
                                                         ; ↘⟦T′⟧ = ⟦Se⟧ i
                                                         ; T≈T′  = U′ ≤-refl
                                                         }
                                                     , record
                                                         { ⟦t⟧   = □ ⟦t⟧
                                                         ; ⟦t′⟧  = □ ⟦t′⟧
                                                         ; ↘⟦t⟧  = ⟦[]⟧ σ.↘⟦σ⟧ (⟦□⟧ ↘⟦t⟧)
                                                         ; ↘⟦t′⟧ = ⟦□⟧ (⟦[]⟧ (⟦；⟧ σ.↘⟦δ⟧) ↘⟦t′⟧)
                                                         ; t≈t′  = PERDef.□ λ κ → subst (⟦t⟧ [ κ ] ≈ ⟦t′⟧ [ κ ] ∈_) (sym (𝕌-wellfounded-≡-𝕌 (suc i) ≤-refl)) (𝕌-mon κ t≈t′)
                                                         }


□-cong′ : ∀ {i} →
          ([] ∷⁺ Γ) ⊨ T ≈ T′ ∶ Se i →
          --------------------------
          Γ ⊨ □ T ≈ □ T′ ∶ Se i
□-cong′ {_} {T} {T′} {i} (κ-cong ⊨Γ , _ , T≈T′) = ⊨Γ , _ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp _ (Se i) ρ (Se i) ρ′) (λ rel → RelExp (□ T) ρ (□ T′) ρ′ (El _ (RelTyp.T≈T′ rel)))
        helper {ρ} {ρ′} ρ≈ρ′
          with T≈T′ {ext ρ 1} {ext ρ′ 1} (ρ≈ρ′ , refl)
        ...  | record { ↘⟦T⟧ = ⟦Se⟧ .i ; ↘⟦T′⟧ = ⟦Se⟧ .i ; T≈T′ = PERDef.U i<j _ }
             , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
             rewrite 𝕌-wellfounded-≡-𝕌 _ i<j = record
                                                 { ⟦T⟧   = U i
                                                 ; ⟦T′⟧  = U i
                                                 ; ↘⟦T⟧  = ⟦Se⟧ i
                                                 ; ↘⟦T′⟧ = ⟦Se⟧ i
                                                 ; T≈T′  = U′ i<j
                                                 }
                                             , record
                                                 { ⟦t⟧   = □ ⟦t⟧
                                                 ; ⟦t′⟧  = □ ⟦t′⟧
                                                 ; ↘⟦t⟧  = ⟦□⟧ ↘⟦t⟧
                                                 ; ↘⟦t′⟧ = ⟦□⟧ ↘⟦t′⟧
                                                 ; t≈t′  = subst (□ ⟦t⟧ ≈ □ ⟦t′⟧ ∈_) (sym (𝕌-wellfounded-≡-𝕌 _ i<j)) (□ λ κ → 𝕌-mon κ t≈t′)
                                                 }


box-cong′ : ([] ∷⁺ Γ) ⊨ t ≈ t′ ∶ T →
            ------------------------
            Γ ⊨ box t ≈ box t′ ∶ □ T
box-cong′ {_} {t} {t′} {T} (κ-cong ⊨Γ , _ , t≈t′) = ⊨Γ , _ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp _ (□ T) ρ (□ T) ρ′) (λ rel → RelExp (box t) ρ (box t′) ρ′ (El _ (RelTyp.T≈T′ rel)))
        helper {ρ} {ρ′} ρ≈ρ′
          with t≈t′ {ext ρ 1} {ext ρ′ 1} (ρ≈ρ′ , refl)
        ...  | rt , re = record
                           { ⟦T⟧   = □ rt.⟦T⟧
                           ; ⟦T′⟧  = □ rt.⟦T′⟧
                           ; ↘⟦T⟧  = ⟦□⟧ rt.↘⟦T⟧
                           ; ↘⟦T′⟧ = ⟦□⟧ rt.↘⟦T′⟧
                           ; T≈T′  = □ λ κ → 𝕌-mon κ rt.T≈T′
                           }
                       , record
                           { ⟦t⟧   = box re.⟦t⟧
                           ; ⟦t′⟧  = box re.⟦t′⟧
                           ; ↘⟦t⟧  = ⟦box⟧ re.↘⟦t⟧
                           ; ↘⟦t′⟧ = ⟦box⟧ re.↘⟦t′⟧
                           ; t≈t′  = λ n κ → record
                             { ua    = re.⟦t⟧ [ ins κ 1 ] [ ins vone n ]
                             ; ub    = re.⟦t′⟧ [ ins κ 1 ] [ ins vone n ]
                             ; ↘ua   = box↘ n
                             ; ↘ub   = box↘ n
                             ; ua≈ub = subst₂ (_≈_∈ El _ (𝕌-mon (ins κ n) rt.T≈T′))
                                              (trans (cong (re.⟦t⟧ [_]) (sym (ins-1-ø-ins-vone κ n))) (sym (D-comp re.⟦t⟧ (ins κ 1) (ins vone n))))
                                              (trans (cong (re.⟦t′⟧ [_]) (sym (ins-1-ø-ins-vone κ n))) (sym (D-comp re.⟦t′⟧ (ins κ 1) (ins vone n))))
                                              (El-mon rt.T≈T′ (ins κ n) (𝕌-mon (ins κ n) rt.T≈T′) re.t≈t′)
                             }
                           }
          where module rt = RelTyp rt
                module re = RelExp re


unbox-cong′ : ∀ {n} Ψs →
              Γ ⊨ t ≈ t′ ∶ □ T →
              ⊨ (Ψs ++⁺ Γ) →
              len Ψs ≡ n →
              ------------------------------------------------
              (Ψs ++⁺ Γ) ⊨ unbox n t ≈ unbox n t′ ∶ (T [ I ； n ])
unbox-cong′ {_} {t} {t′} {T} {n} Ψs (⊨Γ , _ , t≈t′) ⊨ΨsΓ refl = ⊨ΨsΓ , _ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨ΨsΓ ⟧ρ → Σ (RelTyp _ (T [ I ； n ]) ρ (T [ I ； n ]) ρ′) (λ rel → RelExp (unbox n t) ρ (unbox n t′) ρ′ (El _ (RelTyp.T≈T′ rel)))
        helper {ρ} {ρ′} ρ≈ρ′
          with ⊨-resp-∥ Ψs Ψs ⊨ΨsΓ refl | ⟦⟧ρ-resp-∥ Ψs Ψs ⊨ΨsΓ refl ρ≈ρ′
        ...  | ⊨Γ₁ | ρ≈ρ′∥n
             with t≈t′ (⊨-irrel ⊨Γ₁ ⊨Γ ρ≈ρ′∥n)
        ...     | record { ⟦T⟧ = □ ⟦T⟧ ; ⟦T′⟧ = □ ⟦T′⟧ ; ↘⟦T⟧ = ⟦□⟧ ↘⟦T⟧ ; ↘⟦T′⟧ = ⟦□⟧ ↘⟦T′⟧ ; T≈T′ = □ A≈A′ }
                , re = record
                         { ⟦T⟧   = ⟦T⟧ [ ins vone (L ρ n) ]
                         ; ⟦T′⟧  = ⟦T′⟧ [ ins vone (L ρ n) ]
                         ; ↘⟦T⟧  = ⟦[]⟧ (⟦；⟧ ⟦I⟧) (subst (⟦ T ⟧_↘ ⟦T⟧ [ ins vone (L ρ n) ]) (ext1-mon (ρ ∥ n) (L ρ n)) (⟦⟧-mon (ins vone (L ρ n)) ↘⟦T⟧))
                         ; ↘⟦T′⟧ = ⟦[]⟧ (⟦；⟧ ⟦I⟧) (subst₂ (λ x y → ⟦ T ⟧ x ↘ ⟦T′⟧ [ ins vone y ]) (ext1-mon (ρ′ ∥ n) (L ρ′ n)) (sym L≡) (⟦⟧-mon (ins vone (L ρ′ n)) ↘⟦T′⟧))
                         ; T≈T′  = A≈A′ (ins vone (L ρ n))
                         }
                     , record
                         { ⟦t⟧   = ua
                         ; ⟦t′⟧  = ub
                         ; ↘⟦t⟧  = ⟦unbox⟧ n re.↘⟦t⟧ (subst (unbox∙ L ρ n ,_↘ ua) (D-ap-vone re.⟦t⟧) ↘ua)
                         ; ↘⟦t′⟧ = ⟦unbox⟧ n re.↘⟦t′⟧ (subst₂ (unbox∙_,_↘ ub) L≡ (D-ap-vone re.⟦t′⟧) ↘ub)
                         ; t≈t′  = ua≈ub
                         }
          where module re = RelExp re
                open □̂ (re.t≈t′ (L ρ n) vone)
                L≡ = ⟦⟧ρ-resp-L ⊨ΨsΓ ρ≈ρ′ (length-<-++⁺ Ψs)


box-[]′ : Γ ⊨s σ ∶ Δ →
          ([] ∷⁺ Δ) ⊨ t ∶ T →
          ------------------------------------------------
          Γ ⊨ box t [ σ ] ≈ box (t [ σ ； 1 ]) ∶ (□ T [ σ ])
box-[]′ {_} {σ} {_} {t} {T} (⊨Γ , ⊨Δ , ⊨σ) (κ-cong ⊨Δ₁ , _ , ⊨t) = ⊨Γ , _ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp _ (□ T [ σ ]) ρ (□ T [ σ ]) ρ′) (λ rel → RelExp (box t [ σ ]) ρ (box (t [ σ ； 1 ])) ρ′ (El _ (RelTyp.T≈T′ rel)))
        helper {ρ} {ρ′} ρ≈ρ′ = help
          where module σ = RelSubsts (⊨σ ρ≈ρ′)
                help : Σ (RelTyp _ (□ T [ σ ]) ρ (□ T [ σ ]) ρ′) (λ rel → RelExp (box t [ σ ]) ρ (box (t [ σ ； 1 ])) ρ′ (El _ (RelTyp.T≈T′ rel)))
                help
                  with ⊨t {ext σ.⟦σ⟧ 1} {ext σ.⟦δ⟧ 1} (⊨-irrel ⊨Δ ⊨Δ₁ σ.σ≈δ , refl)
                ... | rt , re = record
                                  { ⟦T⟧   = □ rt.⟦T⟧
                                  ; ⟦T′⟧  = □ rt.⟦T′⟧
                                  ; ↘⟦T⟧  = ⟦[]⟧ σ.↘⟦σ⟧ (⟦□⟧ rt.↘⟦T⟧)
                                  ; ↘⟦T′⟧ = ⟦[]⟧ σ.↘⟦δ⟧ (⟦□⟧ rt.↘⟦T′⟧)
                                  ; T≈T′  = PERDef.□ λ κ → 𝕌-mon κ rt.T≈T′
                                  }
                              , record
                                  { ⟦t⟧   = box re.⟦t⟧
                                  ; ⟦t′⟧  = box re.⟦t′⟧
                                  ; ↘⟦t⟧  = ⟦[]⟧ σ.↘⟦σ⟧ (⟦box⟧ re.↘⟦t⟧)
                                  ; ↘⟦t′⟧ = ⟦box⟧ (⟦[]⟧ (⟦；⟧ σ.↘⟦δ⟧) re.↘⟦t′⟧)
                                  ; t≈t′  = λ n κ → record
                                    { ua    = re.⟦t⟧ [ ins κ 1 ] [ ins vone n ]
                                    ; ub    = re.⟦t′⟧ [ ins κ 1 ] [ ins vone n ]
                                    ; ↘ua   = box↘ n
                                    ; ↘ub   = box↘ n
                                    ; ua≈ub = subst₂ (_≈_∈ El _ (𝕌-mon (ins κ n) rt.T≈T′))
                                                     (sym (D-ins-ins re.⟦t⟧ κ n))
                                                     (sym (D-ins-ins re.⟦t′⟧ κ n))
                                                     (El-mon rt.T≈T′ (ins κ n) (𝕌-mon (ins κ n) rt.T≈T′) re.t≈t′)
                                    }
                                  }
                  where module rt = RelTyp rt
                        module re = RelExp re


unbox-[]′ : ∀ {n} Ψs →
            Δ ⊨ t ∶ □ T →
            Γ ⊨s σ ∶ (Ψs ++⁺ Δ) →
            len Ψs ≡ n →
            --------------------------------------------------------------------------
            Γ ⊨ unbox n t [ σ ] ≈ unbox (L σ n) (t [ σ ∥ n ]) ∶ (T [ (σ ∥ n) ； L σ n ])
unbox-[]′ {_} {t} {T} {_} {σ} {n} Ψs (⊨Δ , _ , ⊨t) (⊨Γ , ⊨ΨsΔ , ⊨σ) refl = ⊨Γ , _ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp _ (T [ (σ ∥ n) ； L σ n ]) ρ (T [ (σ ∥ n) ； L σ n ]) ρ′) (λ rel → RelExp (unbox n t [ σ ]) ρ (unbox (L σ n) (t [ σ ∥ n ])) ρ′ (El _ (RelTyp.T≈T′ rel)))
        helper {ρ} {ρ′} ρ≈ρ′ = help
          where module σ = RelSubsts (⊨σ ρ≈ρ′)
                help : Σ (RelTyp _ (T [ (σ ∥ n) ； L σ n ]) ρ (T [ (σ ∥ n) ； L σ n ]) ρ′) (λ rel → RelExp (unbox n t [ σ ]) ρ (unbox (L σ n) (t [ σ ∥ n ])) ρ′ (El _ (RelTyp.T≈T′ rel)))
                help
                  with ⊨-resp-∥ Ψs Ψs ⊨ΨsΔ refl | ⟦⟧ρ-resp-∥ Ψs Ψs ⊨ΨsΔ refl σ.σ≈δ
                ...  | ⊨Δ₁ | σ≈δ∥n
                     with ⊨t (⊨-irrel ⊨Δ₁ ⊨Δ σ≈δ∥n)
                ...     | record { ⟦T⟧ = □ ⟦T⟧ ; ⟦T′⟧ = □ ⟦T′⟧ ; ↘⟦T⟧ = ⟦□⟧ ↘⟦T⟧ ; ↘⟦T′⟧ = ⟦□⟧ ↘⟦T′⟧ ; T≈T′ = □ T≈T′ }
                        , re = record
                                 { ⟦T⟧   = ⟦T⟧ [ ins vone (L ρ (L σ n)) ]
                                 ; ⟦T′⟧  = ⟦T′⟧ [ ins vone (L ρ (L σ n)) ]
                                 ; ↘⟦T⟧  = ⟦[]⟧ (⟦；⟧ (∥-⟦⟧s n σ.↘⟦σ⟧))
                                                (subst (⟦ T ⟧_↘ ⟦T⟧ [ ins vone (L ρ (L σ n)) ])
                                                       (ext1-mon (σ.⟦σ⟧ ∥ n) (L ρ (L σ n)))
                                                       (⟦⟧-mon (ins vone (L ρ (L σ n))) ↘⟦T⟧))
                                 ; ↘⟦T′⟧ = ⟦[]⟧ (⟦；⟧ (∥-⟦⟧s n σ.↘⟦δ⟧))
                                                (subst₂ (λ x y → ⟦ T ⟧ x ↘ ⟦T′⟧ [ ins vone y ])
                                                       (ext1-mon (σ.⟦δ⟧ ∥ n) (L ρ′ (L σ n)))
                                                       L≡′
                                                       (⟦⟧-mon (ins vone (L ρ′ (L σ n))) ↘⟦T′⟧))
                                 ; T≈T′  = T≈T′ (ins vone (L ρ (L σ n)))
                                 }
                             , record
                                 { ⟦t⟧   = ua
                                 ; ⟦t′⟧  = ub
                                 ; ↘⟦t⟧  = ⟦[]⟧ σ.↘⟦σ⟧
                                                (⟦unbox⟧ n re.↘⟦t⟧ (subst₂ (unbox∙_,_↘ ua) (L-⟦⟧s n σ.↘⟦σ⟧) (D-ap-vone re.⟦t⟧) ↘ua))
                                 ; ↘⟦t′⟧ = ⟦unbox⟧ (L σ n)
                                                   (⟦[]⟧ (∥-⟦⟧s n σ.↘⟦δ⟧) re.↘⟦t′⟧)
                                                   (subst₂ (unbox∙_,_↘ ub) (sym L≡′) (D-ap-vone re.⟦t′⟧) ↘ub)
                                 ; t≈t′  = ua≈ub
                                 }
                  where module re = RelExp re
                        open □̂ (re.t≈t′ (L ρ (L σ n)) vone)
                        L≡ = ⟦⟧ρ-resp-L ⊨ΨsΔ σ.σ≈δ (length-<-++⁺ Ψs)
                        L≡′ = trans (L-⟦⟧s n σ.↘⟦δ⟧) (sym (trans (L-⟦⟧s n σ.↘⟦σ⟧) L≡))


□-β′ : ∀ {n} Ψs →
       ([] ∷⁺ Γ) ⊨ t ∶ T →
       ⊨ (Ψs ++⁺ Γ) →
       len Ψs ≡ n →
       --------------------------------------------------------
       (Ψs ++⁺ Γ) ⊨ unbox n (box t) ≈ t [ I ； n ] ∶ (T [ I ； n ])
□-β′ {_} {t} {T} {n} Ψs (κ-cong ⊨Γ , _ , ⊨t) ⊨ΨsΓ refl = ⊨ΨsΓ , _ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨ΨsΓ ⟧ρ → Σ (RelTyp _ (T [ I ； n ]) ρ (T [ I ； n ]) ρ′) (λ rel → RelExp (unbox n (box t)) ρ (t [ I ； n ]) ρ′ (El _ (RelTyp.T≈T′ rel)))
        helper {ρ} {ρ′} ρ≈ρ′
          with ⊨-resp-∥ Ψs Ψs ⊨ΨsΓ refl | ⟦⟧ρ-resp-∥ Ψs Ψs ⊨ΨsΓ refl ρ≈ρ′
        ...  | ⊨Γ₁ | ρ≈ρ′∥n
             with ⊨t {ext (ρ ∥ n) 1} {ext (ρ′ ∥ n) 1} (⊨-irrel ⊨Γ₁ ⊨Γ ρ≈ρ′∥n , refl)
        ...     | rt , re = record
                              { ⟦T⟧   = rt.⟦T⟧ [ ins vone (L ρ n) ]
                              ; ⟦T′⟧  = rt.⟦T′⟧ [ ins vone (L ρ n) ]
                              ; ↘⟦T⟧  = ⟦[]⟧ (⟦；⟧ ⟦I⟧) (subst (⟦ T ⟧_↘ rt.⟦T⟧ [ ins vone (L ρ n) ]) (ext1-mon (ρ ∥ n) (L ρ n)) (⟦⟧-mon (ins vone (L ρ n)) rt.↘⟦T⟧))
                              ; ↘⟦T′⟧ = ⟦[]⟧ (⟦；⟧ ⟦I⟧) (subst₂ (λ x y → ⟦ T ⟧ x ↘ rt.⟦T′⟧ [ ins vone y ]) (ext1-mon (ρ′ ∥ n) (L ρ′ n)) (sym L≡) (⟦⟧-mon (ins vone (L ρ′ n)) rt.↘⟦T′⟧))
                              ; T≈T′  = 𝕌-mon (ins vone (L ρ n)) rt.T≈T′
                              }
                          , record
                              { ⟦t⟧   = re.⟦t⟧ [ ins vone (L ρ n) ]
                              ; ⟦t′⟧  = re.⟦t′⟧ [ ins vone (L ρ n) ]
                              ; ↘⟦t⟧  = ⟦unbox⟧ n (⟦box⟧ re.↘⟦t⟧) (box↘ (L ρ n))
                              ; ↘⟦t′⟧ = ⟦[]⟧ (⟦；⟧ ⟦I⟧) (subst (⟦ t ⟧_↘ re.⟦t′⟧ [ ins vone (L ρ n) ]) (trans (ext1-mon (ρ′ ∥ n) (L ρ n)) (cong (ext _) L≡)) (⟦⟧-mon (ins vone (L ρ n)) re.↘⟦t′⟧))
                              ; t≈t′  = El-mon rt.T≈T′ (ins vone (L ρ n)) (𝕌-mon (ins vone (L ρ n)) rt.T≈T′) re.t≈t′
                              }
          where module rt = RelTyp rt
                module re = RelExp re
                L≡ = ⟦⟧ρ-resp-L ⊨ΨsΓ ρ≈ρ′ (length-<-++⁺ Ψs)


□-η′ : Γ ⊨ t ∶ □ T →
       ------------------------------
       Γ ⊨ t ≈ box (unbox 1 t) ∶ □ T
□-η′ {_} {t} {T} (⊨Γ , _ , ⊨t) = ⊨Γ , _ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp _ (□ T) ρ (□ T) ρ′) (λ rel → RelExp t ρ (box (unbox 1 t)) ρ′ (El _ (RelTyp.T≈T′ rel)))
        helper ρ≈ρ′
          with ⊨t ρ≈ρ′
        ...  | rt@record { ⟦T⟧ = □ ⟦T⟧ ; ⟦T′⟧ = □ ⟦T′⟧ ; ↘⟦T⟧ = ⟦□⟧ ↘⟦T⟧ ; ↘⟦T′⟧ = ⟦□⟧ ↘⟦T′⟧ ; T≈T′ = □ A≈A′ }
             , re = rt
                  , record
                      { ⟦t⟧   = re.⟦t⟧
                      ; ⟦t′⟧  = box ub
                      ; ↘⟦t⟧  = re.↘⟦t⟧
                      ; ↘⟦t′⟧ = ⟦box⟧ (⟦unbox⟧ 1 re.↘⟦t′⟧ (subst (unbox∙ 1 ,_↘ ub) (D-ap-vone re.⟦t′⟧) ↘ub))
                      ; t≈t′  = λ n κ →
                        let module u = □̂ (re.t≈t′ n κ)
                        in record
                        { ua    = u.ua
                        ; ub    = u.ub
                        ; ↘ua   = u.↘ua
                        ; ↘ub   = subst (unbox∙ n , box (ub [ ins κ 1 ]) ↘_) (trans (D-ins-ins ub κ n) (unbox-mon (ins κ n) ↘ub (subst₂ (λ x y → unbox∙ x , y [ κ ] ↘ u.ub) (sym (+-identityʳ _)) (sym (D-ap-vone re.⟦t′⟧)) u.↘ub))) (box↘ n)
                        ; ua≈ub = u.ua≈ub
                        }
                      }
          where module re = RelExp re
                open □̂ (re.t≈t′ 1 vone)
