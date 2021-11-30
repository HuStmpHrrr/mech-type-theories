{-# OPTIONS --without-K --safe #-}

open import Level using ()
open import Axiom.Extensionality.Propositional

module kMLTT.Completeness.Box (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Data.Nat.Properties

open import Lib
open import kMLTT.Completeness.LogRel

open import kMLTT.Semantics.Properties.Domain fext
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
                     , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ ; nat = nat ; nat′ = nat′ }
                     rewrite 𝕌-wellfounded-≡-𝕌 _ i<j = record
                                                         { ⟦T⟧   = U i
                                                         ; ⟦T′⟧  = U i
                                                         ; ↘⟦T⟧  = ⟦Se⟧ i
                                                         ; ↘⟦T′⟧ = ⟦Se⟧ i
                                                         ; T≈T′  = suc i , U′ ≤-refl
                                                         ; nat   = λ κ → ⟦Se⟧ i
                                                         ; nat′  = λ κ → ⟦Se⟧ i
                                                         }
                                                     , record
                                                         { ⟦t⟧   = □ ⟦t⟧
                                                         ; ⟦t′⟧  = □ ⟦t′⟧
                                                         ; ↘⟦t⟧  = ⟦[]⟧ σ.↘⟦σ⟧ (⟦□⟧ ↘⟦t⟧)
                                                         ; ↘⟦t′⟧ = ⟦□⟧ (⟦[]⟧ (⟦；⟧ σ.↘⟦δ⟧) ↘⟦t′⟧)
                                                         ; t≈t′  = PERDef.□ λ κ → subst (⟦t⟧ [ κ ] ≈ ⟦t′⟧ [ κ ] ∈_) (sym (𝕌-wellfounded-≡-𝕌 (suc i) ≤-refl)) (𝕌-mon κ t≈t′)
                                                         ; nat   = λ κ → ⟦[]⟧ (σ.nat κ) (⟦□⟧ (subst (⟦ T ⟧_↘ ⟦t⟧ [ ins κ 1 ]) (ext-mon σ.⟦σ⟧ 1 (ins κ 1)) (nat (ins κ 1))))
                                                         ; nat′  = λ κ → ⟦□⟧ (⟦[]⟧ (⟦；⟧ (σ.nat′ κ)) (subst (⟦ T ⟧_↘ ⟦t′⟧ [ ins κ 1 ]) (ext-mon σ.⟦δ⟧ 1 (ins κ 1)) (nat′ (ins κ 1))))
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
             , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ ; nat = nat ; nat′ = nat′ }
             rewrite 𝕌-wellfounded-≡-𝕌 _ i<j = record
                                                 { ⟦T⟧   = U i
                                                 ; ⟦T′⟧  = U i
                                                 ; ↘⟦T⟧  = ⟦Se⟧ i
                                                 ; ↘⟦T′⟧ = ⟦Se⟧ i
                                                 ; T≈T′  = _ , U′ i<j
                                                 ; nat   = λ κ → ⟦Se⟧ i
                                                 ; nat′  = λ κ → ⟦Se⟧ i
                                                 }
                                             , record
                                                 { ⟦t⟧   = □ ⟦t⟧
                                                 ; ⟦t′⟧  = □ ⟦t′⟧
                                                 ; ↘⟦t⟧  = ⟦□⟧ ↘⟦t⟧
                                                 ; ↘⟦t′⟧ = ⟦□⟧ ↘⟦t′⟧
                                                 ; t≈t′  = subst (□ ⟦t⟧ ≈ □ ⟦t′⟧ ∈_) (sym (𝕌-wellfounded-≡-𝕌 _ i<j)) (□ λ κ → 𝕌-mon κ t≈t′)
                                                 ; nat   = λ κ → ⟦□⟧ (subst (⟦ T ⟧_↘ ⟦t⟧ [ ins κ 1 ]) (ext-mon ρ 1 (ins κ 1)) (nat (ins κ 1)))
                                                 ; nat′  = λ κ → ⟦□⟧ (subst (⟦ T′ ⟧_↘ ⟦t′⟧ [ ins κ 1 ]) (ext-mon ρ′ 1 (ins κ 1)) (nat′ (ins κ 1)))
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
                           ; nat   = λ κ → ⟦□⟧ (subst (⟦ T ⟧_↘ rt.⟦T⟧ [ ins κ 1 ]) (ext-mon ρ 1 (ins κ 1)) (rt.nat (ins κ 1)))
                           ; nat′  = λ κ → ⟦□⟧ (subst (⟦ T ⟧_↘ rt.⟦T′⟧ [ ins κ 1 ]) (ext-mon ρ′ 1 (ins κ 1)) (rt.nat′ (ins κ 1)))
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
                           ; nat   = λ κ → ⟦box⟧ (subst (⟦ t ⟧_↘ re.⟦t⟧ [ ins κ 1 ]) (ext-mon ρ 1 (ins κ 1)) (re.nat (ins κ 1)))
                           ; nat′  = λ κ → ⟦box⟧ (subst (⟦ t′ ⟧_↘ re.⟦t′⟧ [ ins κ 1 ]) (ext-mon ρ′ 1 (ins κ 1)) (re.nat′ (ins κ 1)))
                           }
          where module rt = RelTyp rt
                module re = RelExp re

-- unbox-cong : ∀ {n} Ψs →
--              Γ ⊨ t ≈ t′ ∶ □ T →
--              ⊨ Ψs ++⁺ Γ →
--              len Ψs ≡ n →
--              ------------------------------------------------
--              Ψs ++⁺ Γ ⊨ unbox n t ≈ unbox n t′ ∶ T [ I ； n ]
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
