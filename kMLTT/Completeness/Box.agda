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
□-[]′ {_} {σ} {_} {T} {i} (⊨Γ , ⊨Δ , ⊨σ) (κ-cong ⊨Δ₁ , ⊨T) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp (Se i) ρ (Se i) ρ′) (λ rel → RelExp (□ T [ σ ]) ρ (□ (T [ σ ； 1 ])) ρ′ (El∞ (RelTyp.T≈T′ rel)))
        helper {ρ} {ρ′} ρ≈ρ′ = help
          where module σ = RelSubsts (⊨σ ρ≈ρ′)
                help : Σ (RelTyp (Se i) ρ (Se i) ρ′) (λ rel → RelExp (□ T [ σ ]) ρ (□ (T [ σ ； 1 ])) ρ′ (El∞ (RelTyp.T≈T′ rel)))
                help
                  with ⊨T {ext σ.⟦σ⟧ 1} {ext σ.⟦δ⟧ 1} (⊨-irrel ⊨Δ ⊨Δ₁ σ.σ≈δ , refl)
                ...  | record { ↘⟦T⟧ = ⟦Se⟧ .i ; ↘⟦T′⟧ = ⟦Se⟧ .i ; T≈T′ = _ , PERDef.U i<j _ }
                     , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
                     rewrite 𝕌-wellfounded-≡-𝕌 _ i<j = record
                                                         { ⟦T⟧   = U i
                                                         ; ⟦T′⟧  = U i
                                                         ; ↘⟦T⟧  = ⟦Se⟧ i
                                                         ; ↘⟦T′⟧ = ⟦Se⟧ i
                                                         ; T≈T′  = suc i , U′ ≤-refl
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
□-cong′ {_} {T} {T′} {i} (κ-cong ⊨Γ , T≈T′) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp (Se i) ρ (Se i) ρ′) (λ rel → RelExp (□ T) ρ (□ T′) ρ′ (El∞ (RelTyp.T≈T′ rel)))
        helper {ρ} {ρ′} ρ≈ρ′
          with T≈T′ {ext ρ 1} {ext ρ′ 1} (ρ≈ρ′ , refl)
        ...  | record { ↘⟦T⟧ = ⟦Se⟧ .i ; ↘⟦T′⟧ = ⟦Se⟧ .i ; T≈T′ = _ , PERDef.U i<j _ }
             , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
             rewrite 𝕌-wellfounded-≡-𝕌 _ i<j = record
                                                 { ⟦T⟧   = U i
                                                 ; ⟦T′⟧  = U i
                                                 ; ↘⟦T⟧  = ⟦Se⟧ i
                                                 ; ↘⟦T′⟧ = ⟦Se⟧ i
                                                 ; T≈T′  = _ , U′ i<j
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
box-cong′ {_} {t} {t′} {T} (κ-cong ⊨Γ , t≈t′) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp (□ T) ρ (□ T) ρ′) (λ rel → RelExp (box t) ρ (box t′) ρ′ (El∞ (RelTyp.T≈T′ rel)))
        helper {ρ} {ρ′} ρ≈ρ′
          with t≈t′ {ext ρ 1} {ext ρ′ 1} (ρ≈ρ′ , refl)
        ...  | rt , re = record
                           { ⟦T⟧   = □ rt.⟦T⟧
                           ; ⟦T′⟧  = □ rt.⟦T′⟧
                           ; ↘⟦T⟧  = ⟦□⟧ rt.↘⟦T⟧
                           ; ↘⟦T′⟧ = ⟦□⟧ rt.↘⟦T′⟧
                           ; T≈T′  = _ , □ λ κ → 𝕌-mon κ (proj₂ rt.T≈T′)
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
                             ; ua≈ub = subst₂ (_≈_∈ El _ (𝕌-mon (ins κ n) (proj₂ rt.T≈T′)))
                                              (trans (cong (re.⟦t⟧ [_]) (sym (ins-1-ø-ins-vone κ n))) (sym (D-comp re.⟦t⟧ (ins κ 1) (ins vone n))))
                                              (trans (cong (re.⟦t′⟧ [_]) (sym (ins-1-ø-ins-vone κ n))) (sym (D-comp re.⟦t′⟧ (ins κ 1) (ins vone n))))
                                              (El-mon (proj₂ rt.T≈T′) (ins κ n) (𝕌-mon (ins κ n) (proj₂ rt.T≈T′)) re.t≈t′)
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
unbox-cong′ {_} {t} {t′} {T} {n} Ψs (⊨Γ , t≈t′) ⊨ΨsΓ refl = ⊨ΨsΓ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨ΨsΓ ⟧ρ → Σ (RelTyp (T [ I ； n ]) ρ (T [ I ； n ]) ρ′) (λ rel → RelExp (unbox n t) ρ (unbox n t′) ρ′ (El∞ (RelTyp.T≈T′ rel)))
        helper {ρ} {ρ′} ρ≈ρ′
          with ⊨-resp-∥ Ψs Ψs ⊨ΨsΓ refl | ⟦⟧ρ-resp-∥ Ψs Ψs ⊨ΨsΓ refl ρ≈ρ′
        ...  | ⊨Γ₁ | ρ≈ρ′∥n
             with t≈t′ (⊨-irrel ⊨Γ₁ ⊨Γ ρ≈ρ′∥n)
        ... | record { ⟦T⟧ = □ ⟦T⟧ ; ⟦T′⟧ = □ ⟦T′⟧ ; ↘⟦T⟧ = ⟦□⟧ ↘⟦T⟧ ; ↘⟦T′⟧ = ⟦□⟧ ↘⟦T′⟧ ; T≈T′ = i , □ A≈A′ }
            , re = record
                     { ⟦T⟧   = ⟦T⟧ [ ins vone (L ρ n) ]
                     ; ⟦T′⟧  = ⟦T′⟧ [ ins vone (L ρ n) ]
                     ; ↘⟦T⟧  = ⟦[]⟧ (⟦；⟧ ⟦I⟧) (subst (⟦ T ⟧_↘ ⟦T⟧ [ ins vone (L ρ n) ]) (ext1-mon (ρ ∥ n) (L ρ n)) (⟦⟧-mon (ins vone (L ρ n)) ↘⟦T⟧))
                     ; ↘⟦T′⟧ = ⟦[]⟧ (⟦；⟧ ⟦I⟧) (subst₂ (λ x y → ⟦ T ⟧ x ↘ ⟦T′⟧ [ ins vone y ]) (ext1-mon (ρ′ ∥ n) (L ρ′ n)) (sym (⟦⟧ρ-resp-L ⊨ΨsΓ ρ≈ρ′ (length-<-++⁺ Ψs))) (⟦⟧-mon (ins vone (L ρ′ n)) ↘⟦T′⟧))
                     ; T≈T′  = i , A≈A′ (ins vone (L ρ n))
                     }
                 , record
                     { ⟦t⟧   = ua
                     ; ⟦t′⟧  = ub
                     ; ↘⟦t⟧  = ⟦unbox⟧ n re.↘⟦t⟧ (subst (unbox∙ L ρ n ,_↘ ua) (D-ap-vone re.⟦t⟧) ↘ua)
                     ; ↘⟦t′⟧ = ⟦unbox⟧ n re.↘⟦t′⟧ (subst₂ (unbox∙_,_↘ ub) (⟦⟧ρ-resp-L ⊨ΨsΓ ρ≈ρ′ (length-<-++⁺ Ψs)) (D-ap-vone re.⟦t′⟧) ↘ub)
                     ; t≈t′  = ua≈ub
                     }
          where module re = RelExp re
                open □̂ (re.t≈t′ (L ρ n) vone)


-- box-[]     : Γ ⊨s σ ∶ Δ →
--              [] ∷⁺ Δ ⊨ t ∶ T →
--              ------------------------------------------------
--              Γ ⊨ box t [ σ ] ≈ box (t [ σ ； 1 ]) ∶ □ T [ σ ]
-- unbox-[]   : ∀ {n} Ψs →
--              Δ ⊨ t ∶ □ T →
--              Γ ⊨s σ ∶ Ψs ++⁺ Δ →
--              len Ψs ≡ n →
--              --------------------------------------------------------------------------
--              Γ ⊨ unbox n t [ σ ] ≈ unbox (L σ n) (t [ σ ∥ n ]) ∶ T [ (σ ∥ n) ； L σ n ]
-- □-β        : ∀ {n} Ψs →
--              [] ∷⁺ Γ ⊨ t ∶ T →
--              ⊨ Ψs ++⁺ Γ →
--              len Ψs ≡ n →
--              --------------------------------------------------------
--              Ψs ++⁺ Γ ⊨ unbox n (box t) ≈ t [ I ； n ] ∶ T [ I ； n ]
-- □-η        : Γ ⊨ t ∶ □ T →
--              ------------------------------
--              Γ ⊨ t ≈ box (unbox 1 t) ∶ □ T
