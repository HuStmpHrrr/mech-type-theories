{-# OPTIONS --without-K --safe #-}

open import Level hiding (_⊔_)
open import Axiom.Extensionality.Propositional

-- Semantic judgments for Π types
module MLTT.Completeness.Pi (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Data.Nat
open import Data.Nat.Properties

open import Lib
open import MLTT.Completeness.LogRel
open import MLTT.Completeness.Substitutions fext
open import MLTT.Completeness.Terms fext

open import MLTT.Semantics.Properties.PER fext


Π-[]′ : ∀ {i} →
        Γ ⊨s σ ∶ Δ →
        Δ ⊨ S ∶ Se i →
        S ∷ Δ ⊨ T ∶ Se i →
        -------------------------------------------------
        Γ ⊨ Π S T [ σ ] ≈ Π (S [ σ ]) (T [ q σ ]) ∶ Se i
Π-[]′ {_} {σ} {_} {S} {T} {i} (⊨Γ , ⊨Δ , ⊨σ) (⊨Δ₁ , _ , ⊨S) (∷-cong ⊨Δ₂ rel , _ , ⊨T) = ⊨Γ , _ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 -------------------------------------------------------------------------------------
                 Σ (RelTyp _ (Se i) ρ (Se i) ρ′)
                 λ rel → RelExp (Π S T [ σ ]) ρ (Π (S [ σ ]) (T [ q σ ])) ρ′ (El _ (RelTyp.T≈T′ rel))
        helper {ρ} {ρ′} ρ≈ρ′ = help
          where module σ = RelSubst (⊨σ ρ≈ρ′)
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
                        result S≈ = Π S≈ step
                          where step : a ≈ a′ ∈ El i S≈ →
                                       -----------------------------------------------------------
                                       ΠRT T (σ.⟦σ⟧ ↦ a) (T [ q σ ]) (ρ′ ↦ a′) (𝕌 i)
                                step {a} {a′} a≈a′
                                  with σ≈δ₁ ← ⊨-irrel ⊨Δ ⊨Δ₂ σ.σ≈δ = answer
                                  where insert : a ≈ a′ ∈ El _ (RelTyp.T≈T′ (rel σ≈δ₁))
                                        insert
                                          with record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ } ← rel σ≈δ₁
                                             rewrite ⟦⟧-det ↘⟦T′⟧ ↘⟦t′⟧
                                                   | ⟦⟧-det ↘⟦T⟧ ↘⟦t⟧ = 𝕌-irrel S≈ T≈T′ a≈a′

                                        answer : ΠRT T (σ.⟦σ⟧ ↦ a) (T [ q σ ]) (ρ′ ↦ a′) (𝕌 i)
                                        answer
                                          with ⊨T {σ.⟦σ⟧ ↦ a} {σ.⟦δ⟧ ↦ a′} (σ≈δ₁ , insert)
                                        ...  | record { ⟦T⟧ = .(U i) ; ⟦T′⟧ = .(U i) ; ↘⟦T⟧ = (⟦Se⟧ .i) ; ↘⟦T′⟧ = (⟦Se⟧ .i) ; T≈T′ = U i<j _ }
                                             , re = record
                                                      { ⟦T⟧   = re.⟦t⟧
                                                      ; ⟦T′⟧  = re.⟦t′⟧
                                                      ; ↘⟦T⟧  = re.↘⟦t⟧
                                                      ; ↘⟦T′⟧ = ⟦[]⟧ (⟦q⟧ σ.↘⟦δ⟧) re.↘⟦t′⟧
                                                      ; T≈T′  = subst (re.⟦t⟧ ≈ re.⟦t′⟧ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<j) re.t≈t′
                                                      }
                                          where module re = RelExp re


Π-cong′ : ∀ {i} →
          Γ ⊨ S ≈ S′ ∶ Se i →
          S ∷ Γ ⊨ T ≈ T′ ∶ Se i →
          --------------------------
          Γ ⊨ Π S T ≈ Π S′ T′ ∶ Se i
Π-cong′ {_} {S} {S′} {T} {T′} {i} (⊨Γ , _ , S≈S′) (∷-cong ⊨Γ₁ rel , _ , T≈T′) = ⊨Γ , _ , helper
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
                                                 ; t≈t′  = subst (Π ⟦t⟧ T ρ ≈ Π ⟦t′⟧ T′ ρ′ ∈_) (sym (𝕌-wellfounded-≡-𝕌 _ i<j)) (Π t≈t′ result)
                                                 }
          where result : a ≈ a′ ∈ El _ t≈t′ →
                         ------------------------------------------------
                         ΠRT T (ρ ↦ a) T′ (ρ′ ↦ a′) (𝕌 i)
                result {a} {a′} a≈a′
                  with ρ≈ρ′₁ ← ⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ′ = answer
                  where insert : a ≈ a′ ∈ El _ (RelTyp.T≈T′ (rel ρ≈ρ′₁))
                        insert
                          with record { ⟦T⟧ = ⟦T⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; T≈T′ = T≈T′ } ← rel ρ≈ρ′₁
                             rewrite ⟦⟧-det ↘⟦T⟧ ↘⟦t⟧ = El-one-sided t≈t′ T≈T′ a≈a′

                        answer : ΠRT T (ρ ↦ a) T′ (ρ′ ↦ a′) (𝕌 i)
                        answer
                          with T≈T′ {ρ ↦ a} {ρ′ ↦ a′} (ρ≈ρ′₁ , insert)
                        ...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<j _ }
                             , re = record
                                      { ↘⟦T⟧  = re.↘⟦t⟧
                                      ; ↘⟦T′⟧ = re.↘⟦t′⟧
                                      ; T≈T′  = subst (re.⟦t⟧ ≈ re.⟦t′⟧ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<j) re.t≈t′
                                      }
                          where module re = RelExp re


Λ-cong′ : S ∷ Γ ⊨ t ≈ t′ ∶ T →
          -----------------------
          Γ ⊨ Λ t ≈ Λ t′ ∶ Π S T
Λ-cong′ {S} {_} {t} {t′} {T} (∷-cong ⊨Γ rel , n , t≈t′) = ⊨Γ , _ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 ----------------------------------------------------------
                 Σ (RelTyp _ (Π S T) ρ (Π S T) ρ′)
                 λ rel → RelExp (Λ t) ρ (Λ t′) ρ′ (El _ (RelTyp.T≈T′ rel))
        helper {ρ} {ρ′} ρ≈ρ′ = record
                                 { ↘⟦T⟧  = ⟦Π⟧ S.↘⟦T⟧
                                 ; ↘⟦T′⟧ = ⟦Π⟧ S.↘⟦T′⟧
                                 ; T≈T′  = Π (𝕌-cumu (m≤m⊔n _ n) S.T≈T′) λ a≈b → proj₁ (Πres a≈b)
                                 }
                             , record
                                 { ↘⟦t⟧  = ⟦Λ⟧ t
                                 ; ↘⟦t′⟧ = ⟦Λ⟧ t′
                                 ; t≈t′  = λ a≈b → proj₂ (Πres a≈b)
                                 }
             where module S = RelTyp (rel ρ≈ρ′)
                   insert : (⊨Γ : ⊨ Γ) →
                            (rel : ∀ {ρ ρ′} → ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → RelTyp _ S ρ S ρ′) →
                            (ρ≈ρ′ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ) →
                            a ≈ a′ ∈ El _ (𝕌-cumu (m≤m⊔n _ n) S.T≈T′) →
                            ---------------------------------------------------------------------------
                            a ≈ a′ ∈ El _ (RelTyp.T≈T′ (rel ρ≈ρ′))
                   insert ⊨Γ rel ρ≈ρ′ a≈a′
                     with record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ } ← rel ρ≈ρ′
                        rewrite ⟦⟧-det ↘⟦T⟧ S.↘⟦T⟧ = El-one-sided (𝕌-cumu (m≤m⊔n _ n) S.T≈T′) T≈T′ a≈a′

                   Πres : (a≈b : a ≈ b ∈ El _ (𝕌-cumu (m≤m⊔n _ n) S.T≈T′)) →
                          ---------------------------------------------------------------------------
                          Σ (ΠRT T (ρ ↦ a) T (ρ′ ↦ b) (𝕌 _))
                          λ rel → Π̂ (Λ t ρ) a (Λ t′ ρ′) b (El _ (ΠRT.T≈T′ rel))
                   Πres {a} {b} a≈b = answer
                     where answer : Σ (ΠRT T (ρ ↦ a) T (ρ′ ↦ b) (𝕌 _))
                                    λ rel → Π̂ (Λ t ρ) a (Λ t′ ρ′) b (El _ (ΠRT.T≈T′ rel))
                           answer
                             with t≈t′ {ρ ↦ a} {ρ′ ↦ b} (ρ≈ρ′ , insert ⊨Γ rel ρ≈ρ′ a≈b)
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
                                           { ↘⟦T⟧  = ⟦[]⟧ (⟦,⟧ ⟦I⟧ ↘⟦t⟧) RT.↘⟦T⟧
                                           ; ↘⟦T′⟧ = ⟦[]⟧ (⟦,⟧ ⟦I⟧ ↘⟦t⟧₂) RT.↘⟦T′⟧
                                           ; T≈T′  = RT.T≈T′
                                           }
                                       , record
                                           { ↘⟦t⟧  = ⟦$⟧ ↘⟦r⟧ ↘⟦t⟧ rs.↘fa
                                           ; ↘⟦t′⟧ = ⟦$⟧ ↘⟦r′⟧ ↘⟦t′⟧ rs.↘fa′
                                           ; t≈t′  = El-transp RT′.T≈T′ RT.T≈T′ rs.fa≈fa′ (sym (⟦⟧-det RT.↘⟦T⟧ RT′.↘⟦T⟧))
                                           }
          where T≈T  = 𝕌-trans T≈T′₁ (𝕌-sym T≈T′₂)
                srel = El-trans T≈T′₁ (𝕌-sym T≈T′₂) T≈T t≈t′₁ (El-sym T≈T′₂ (𝕌-sym T≈T′₂) t≈t′₂)

                module RT  = ΠRT (RT (El-one-sided T≈T iA srel))
                module RT′ = ΠRT (RT (El-one-sided T≈T′ iA t≈t′))
                module rs  = Π̂ (r≈r′ (El-one-sided T≈T′ iA t≈t′))


Λ-β′ : S ∷ Γ ⊨ t ∶ T →
       Γ ⊨ s ∶ S →
       ----------------------------------
       Γ ⊨ Λ t $ s ≈ t [| s ] ∶ T [| s ]
Λ-β′ {S} {_} {t} {T} {s} (∷-cong ⊨Γ rel , _ , ⊨t) (⊨Γ₁ , _ , ⊨s) = ⊨Γ , _ , helper
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
        s≈s′₁ : ⟦s⟧ ≈ ⟦s′⟧ ∈ El _ (RelTyp.T≈T′ (rel ρ≈ρ′))
        s≈s′₁
          with record { ↘⟦T⟧ = ↘⟦S⟧₁ ; ↘⟦T′⟧ = ↘⟦S′⟧₁ ; T≈T′ = S≈S′₁ } ← rel ρ≈ρ′
            rewrite ⟦⟧-det ↘⟦S⟧ ↘⟦S⟧₁
                  | ⟦⟧-det ↘⟦S′⟧ ↘⟦S′⟧₁
                  = 𝕌-irrel S≈S′ S≈S′₁ s≈s′

        helper′ : Σ (RelTyp _ (T [| s ]) ρ (T [| s ]) ρ′)
                  λ rel → RelExp (Λ t $ s) ρ (t [| s ]) ρ′ (El _ (RelTyp.T≈T′ rel))
        helper′
          with ⊨t (ρ≈ρ′ , s≈s′₁)
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
        helper′ : {a b : D} (inp : a ≈ b ∈ El _ iS) →
                  -----------------------------------------------------------------------------------
                  Π̂ (⟦t⟧) a ((Λ (t [ wk ] $ v 0) ρ′)) b (El _ (ΠRT.T≈T′ (T≈T′ inp)))
        helper′ {a} {b} inp
          with record { ↘fa = ↘fa ; ↘fa′ = ↘fa′ ; fa≈fa′ = fa≈fa′ } ← t≈t′ inp = record
                                   { ↘fa = ↘fa
                                   ; ↘fa′ = Λ∙ (⟦$⟧ (⟦[]⟧ ⟦wk⟧ ↘⟦t′⟧) (⟦v⟧ 0) ↘fa′)
                                   ; fa≈fa′ = fa≈fa′
                                   }

Λ-[]′ : Γ ⊨s σ ∶ Δ →
        S ∷ Δ ⊨ t ∶ T →
        --------------------------------------------
        Γ ⊨ Λ t [ σ ] ≈ Λ (t [ q σ ]) ∶ Π S T [ σ ]
Λ-[]′ {_} {σ} {_} {S} {t} {T} (⊨Γ , ⊨Δ , ⊨σ) (∷-cong ⊨Δ₁ Srel₁ , n₁ , ⊨t) = ⊨Γ , _ , helper
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
                          ; T≈T′ = Π (𝕌-cumu (m≤m⊔n _ n₁) S≈S′) return
                          }
                        , record
                          { ↘⟦t⟧ = ⟦[]⟧ ↘⟦σ⟧ (⟦Λ⟧ _)
                          ; ↘⟦t′⟧ = ⟦Λ⟧ _
                          ; t≈t′ = result
                          }
      where
        helper′ : {a b : D} (inp : a ≈ b ∈ El _ (𝕌-cumu (m≤m⊔n _ n₁) S≈S′)) →
                  -----------------------------------------------------------------------------------
                  Σ (RelTyp n₁ T (⟦σ⟧ ↦ a) T (⟦δ⟧ ↦ b))
                  λ rel → RelExp t (⟦σ⟧ ↦ a) t (⟦δ⟧ ↦ b) (El _ (RelTyp.T≈T′ rel))
        helper′ {a} {b} inp = ⊨t (σ≈δ₁ , a≈b)
          where
            σ≈δ₁ : ⟦σ⟧ ≈ ⟦δ⟧ ∈ ⟦ ⊨Δ₁ ⟧ρ
            σ≈δ₁ = ⊨-irrel ⊨Δ ⊨Δ₁ σ≈δ

            a≈b : a ≈ b ∈ El _ (RelTyp.T≈T′ (Srel₁ σ≈δ₁))
            a≈b
              with record { ↘⟦T⟧ = ↘⟦S⟧₁ ; ↘⟦T′⟧ = ↘⟦S′⟧₁ ; T≈T′ = S≈S′₁ } ← Srel₁ σ≈δ₁
                rewrite ⟦⟧-det ↘⟦S⟧₁ ↘⟦S⟧
                      | ⟦⟧-det ↘⟦S′⟧₁ ↘⟦S′⟧ = 𝕌-irrel (𝕌-cumu (m≤m⊔n _ n₁) S≈S′) S≈S′₁ inp

        return : {a b : D} →
                 a ≈ b ∈ El _ (𝕌-cumu (m≤m⊔n _ n₁) S≈S′) →
                 -------------------------------------------------------
                 ΠRT T (⟦σ⟧ ↦ a) T (⟦δ⟧ ↦ b) (𝕌 (_ ⊔ n₁))
        return inp
          with record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ } ← proj₁ (helper′ inp) = record
                           { ↘⟦T⟧ = ↘⟦T⟧
                           ; ↘⟦T′⟧ = ↘⟦T′⟧
                           ; T≈T′ = 𝕌-cumu (m≤n⊔m _ _) T≈T′
                           }

        result : {a b : D} (inp : a ≈ b ∈ El _ (𝕌-cumu (m≤m⊔n _ n₁) S≈S′)) →
                 -------------------------------------------------------------------------------------
                 Π̂ (Λ t ⟦σ⟧) a ((Λ (t [ q σ ]) ρ′)) b (El _ (ΠRT.T≈T′ (return inp)))
        result {a} {b} inp
          with helper′ inp
        ...  | record { T≈T′ = T≈T′ }
             , record { ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ } = record
                          { ↘fa = Λ∙ ↘⟦t⟧
                          ; ↘fa′ = Λ∙ (⟦[]⟧ (⟦q⟧ ↘⟦δ⟧) ↘⟦t′⟧)
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
           rewrite ⟦⟧-det ↘⟦S⟧ ↘⟦S⟧₁
                 | ⟦⟧-det ↘⟦S′⟧ ↘⟦S′⟧₁
              with record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ } ← Trel (𝕌-irrel S≈S′₁ iS s≈s′)
                 | record { ↘fa = ↘fa ; ↘fa′ = ↘fa′ ; fa≈fa′ = fa≈fa′ } ← r≈r′ (𝕌-irrel S≈S′₁ iS s≈s′) = record
                                    { ↘⟦T⟧ = ⟦[]⟧ (⟦,⟧ ↘⟦σ⟧ (⟦[]⟧ ↘⟦σ⟧ ↘⟦s⟧)) ↘⟦T⟧
                                    ; ↘⟦T′⟧ = ⟦[]⟧ (⟦,⟧ ↘⟦δ⟧ (⟦[]⟧ ↘⟦δ⟧ ↘⟦s′⟧)) ↘⟦T′⟧
                                    ; T≈T′ = T≈T′
                                    }
                                  , record
                                    { ↘⟦t⟧ = ⟦[]⟧ ↘⟦σ⟧ (⟦$⟧ ↘⟦r⟧ ↘⟦s⟧ ↘fa)
                                    ; ↘⟦t′⟧ = ⟦$⟧ (⟦[]⟧ ↘⟦δ⟧ ↘⟦r′⟧) (⟦[]⟧ ↘⟦δ⟧ ↘⟦s′⟧) ↘fa′
                                    ; t≈t′ = fa≈fa′
                                    }
