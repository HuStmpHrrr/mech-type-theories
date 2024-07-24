{-# OPTIONS --without-K --safe #-}

open import Level hiding (_⊔_)
open import Axiom.Extensionality.Propositional

-- Semantic judgments for Π types
module NonCumulative.Completeness.Pi (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Data.Nat
open import Data.Nat.Properties

open import Lib
open import NonCumulative.Completeness.LogRel
open import NonCumulative.Completeness.Substitutions fext
open import NonCumulative.Completeness.Terms fext

open import NonCumulative.Semantics.Properties.PER fext


Π-[]′ : ∀ {i j k} →
        Γ ⊨s σ ∶ Δ →
        Δ ⊨ S ∶[ 1 + i ] Se i →
        (S ↙ i) ∷ Δ ⊨ T ∶[ 1 + j ] Se j →
        k ≡ max i j →
        -------------------------------------------------
        Γ ⊨ Π (S ↙ i) (T ↙ j) [ σ ] ≈ Π (S [ σ ] ↙ i) (T [ q (S ↙ i) σ ] ↙ j) ∶[ 1 + k ] Se k
Π-[]′ {_} {σ} {_} {S} {T} {i} {j} {k} (⊨Γ , ⊨Δ , ⊨σ) (⊨Δ₁ , ⊨S) (∷-cong ⊨Δ₂ rel _ , ⊨T) refl = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 -------------------------------------------------------------------------------------
                 Σ (RelTyp _ (Se k) ρ (Se k) ρ′)
                 λ rel → RelExp (Π (S ↙ i) (T ↙ j) [ σ ]) ρ (Π (S [ σ ] ↙ i) (T [ q (S ↙ i) σ ] ↙ j)) ρ′ (El _ (RelTyp.T≈T′ rel))
        helper {ρ} {ρ′} ρ≈ρ′ = help
          where module σ = RelSubst (⊨σ ρ≈ρ′)
                help : Σ (RelTyp _ (Se k) ρ (Se k) ρ′)
                       λ rel → RelExp (Π (S ↙ i) (T ↙ j) [ σ ]) ρ (Π (S [ σ ] ↙ i) (T [ q (S ↙ i) σ ] ↙ j)) ρ′ (El _ (RelTyp.T≈T′ rel))
                help
                  with ⊨S (⊨-irrel ⊨Δ ⊨Δ₁ σ.σ≈δ)
                ...  | record { ⟦T⟧ = .(U i) ; ⟦T′⟧ = .(U i) ; ↘⟦T⟧ = (⟦Se⟧ .i) ; ↘⟦T′⟧ = (⟦Se⟧ .i) ; T≈T′ = U eq _ }
                     , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
                     rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym eq)) = record
                        { ⟦T⟧   = U k
                        ; ⟦T′⟧  = U k
                        ; ↘⟦T⟧  = ⟦Se⟧ k
                        ; ↘⟦T′⟧ = ⟦Se⟧ k
                        ; T≈T′  = U′
                        }
                     , record
                         { ⟦t⟧   = Π i ⟦t⟧ (T ↙ j) σ.⟦σ⟧
                         ; ⟦t′⟧  = Π i ⟦t′⟧ (T [ q (S ↙ i) σ ] ↙ j) ρ′
                         ; ↘⟦t⟧  = ⟦[]⟧ σ.↘⟦σ⟧ (⟦Π⟧ ↘⟦t⟧)
                         ; ↘⟦t′⟧ = ⟦Π⟧ (⟦[]⟧ σ.↘⟦δ⟧ ↘⟦t′⟧)
                         ; t≈t′  = subst (Π _ _ _ _ ≈ Π _ _ (T [ _ ] ↙ j) _ ∈_) (sym (𝕌-≡-gen _ λ z → ≤-trans z (≤-reflexive refl))) (result t≈t′)
                         }
                  where result : ⟦t⟧ ≈ ⟦t′⟧ ∈ 𝕌 i →
                                 ------------------------------------------
                                 Π i ⟦t⟧ (T ↙ j) σ.⟦σ⟧ ≈ Π i ⟦t′⟧ (T [ q (S ↙ i) σ ] ↙ j) ρ′ ∈ 𝕌 k
                        result S≈ = Π-𝕌 S≈ step refl
                          where step : a ≈ a′ ∈ El i S≈ →
                                       -----------------------------------------------------------
                                       ΠRT T (σ.⟦σ⟧ ↦ a) (T [ q (S ↙ i) σ ]) (ρ′ ↦ a′) (𝕌 j)
                                step {a} {a′} a≈a′
                                  with σ≈δ₁ ← ⊨-irrel ⊨Δ ⊨Δ₂ σ.σ≈δ = answer
                                  where insert : a ≈ a′ ∈ El _ (RelTyp.T≈T′ (rel σ≈δ₁))
                                        insert
                                          with record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ } ← rel σ≈δ₁
                                             rewrite ⟦⟧-det ↘⟦T′⟧ ↘⟦t′⟧
                                                   | ⟦⟧-det ↘⟦T⟧ ↘⟦t⟧ = 𝕌-irrel S≈ T≈T′ a≈a′

                                        answer : ΠRT T (σ.⟦σ⟧ ↦ a) (T [ q (S ↙ i) σ ]) (ρ′ ↦ a′) (𝕌 j)
                                        answer
                                          with ⊨T {σ.⟦σ⟧ ↦ a} {σ.⟦δ⟧ ↦ a′} (σ≈δ₁ , insert)
                                        ...  | record { ⟦T⟧ = .(U j) ; ⟦T′⟧ = .(U j) ; ↘⟦T⟧ = (⟦Se⟧ .j) ; ↘⟦T′⟧ = (⟦Se⟧ .j) ; T≈T′ = U eq _ }
                                             , re = record
                                                      { ⟦T⟧   = re.⟦t⟧
                                                      ; ⟦T′⟧  = re.⟦t′⟧
                                                      ; ↘⟦T⟧  = re.↘⟦t⟧
                                                      ; ↘⟦T′⟧ = ⟦[]⟧ (⟦q⟧ σ.↘⟦δ⟧) re.↘⟦t′⟧
                                                      ; T≈T′  = subst (re.⟦t⟧ ≈ re.⟦t′⟧ ∈_) (𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym eq))) re.t≈t′
                                                      }
                                          where module re = RelExp re


Π-cong′ : ∀ {i j k} →
          Γ ⊨ S ≈ S′ ∶[ 1 + i ] Se i →
          (S ↙ i) ∷ Γ ⊨ T ≈ T′ ∶[ 1 + j ] Se j →
          k ≡ max i j →
          ----------------------------------
          Γ ⊨ Π (S ↙ i) (T ↙ j) ≈ Π (S′ ↙ i) (T′ ↙ j) ∶[ 1 + k ] Se k
Π-cong′ {_} {S} {S′} {T} {T′} {i} {j} {k} (⊨Γ , S≈S′) (∷-cong ⊨Γ₁ rel _ , T≈T′) refl = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 ----------------------------------------------------------------
                 Σ (RelTyp _ (Se k) ρ (Se k) ρ′)
                 λ rel → RelExp (Π (S ↙ i) (T ↙ j)) ρ (Π (S′ ↙ i) (T′ ↙ j)) ρ′ (El _ (RelTyp.T≈T′ rel))
        helper {ρ} {ρ′} ρ≈ρ′
          with S≈S′ ρ≈ρ′
        ...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U eq _ }
             , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
             rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym eq)) = record
                                                 { ↘⟦T⟧  = ⟦Se⟧ _
                                                 ; ↘⟦T′⟧ = ⟦Se⟧ _
                                                 ; T≈T′  = U′
                                                 }
                                             , record
                                                 { ↘⟦t⟧  = ⟦Π⟧ ↘⟦t⟧
                                                 ; ↘⟦t′⟧ = ⟦Π⟧ ↘⟦t′⟧
                                                 ; t≈t′  = subst (Π _ _ _ _ ≈ Π _ _ _ _ ∈_) (sym (𝕌-≡-gen _ λ z → ≤-trans z (≤-reflexive refl))) (Π-𝕌 t≈t′ result refl)
                                                 }
          where result : a ≈ a′ ∈ El _ t≈t′ →
                         ------------------------------------------------
                         ΠRT T (ρ ↦ a) T′ (ρ′ ↦ a′) (𝕌 j)
                result {a} {a′} a≈a′
                  with ρ≈ρ′₁ ← ⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ′ = answer
                  where insert : a ≈ a′ ∈ El _ (RelTyp.T≈T′ (rel ρ≈ρ′₁))
                        insert
                          with record { ⟦T⟧ = ⟦T⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; T≈T′ = T≈T′ } ← rel ρ≈ρ′₁
                             rewrite ⟦⟧-det ↘⟦T⟧ ↘⟦t⟧ = El-one-sided t≈t′ T≈T′ a≈a′

                        answer : ΠRT T (ρ ↦ a) T′ (ρ′ ↦ a′) (𝕌 j)
                        answer
                          with T≈T′ {ρ ↦ a} {ρ′ ↦ a′} (ρ≈ρ′₁ , insert)
                        ...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U eq _ }
                             , re = record
                                      { ↘⟦T⟧  = re.↘⟦t⟧
                                      ; ↘⟦T′⟧ = re.↘⟦t′⟧
                                      ; T≈T′  = subst (re.⟦t⟧ ≈ re.⟦t′⟧ ∈_) (𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym eq))) re.t≈t′
                                      }
                          where module re = RelExp re

Λ-cong′ : ∀ {i j k} →
            (S ↙ i) ∷ Γ ⊨ t ≈ t′ ∶[ j ] T →
            k ≡ max i j →
            -----------------------
            Γ ⊨ Λ (S ↙ i) t ≈ Λ (S′ ↙ i) t′ ∶[ k ] Π (S ↙ i) (T ↙ j)
Λ-cong′ {S} {_} {t} {t′} {T} {_} {i} {j} {k} (∷-cong ⊨Γ rel _ , t≈t′) refl = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 ----------------------------------------------------------
                 Σ (RelTyp (max i j) (Π (S ↙ i) (T ↙ j)) ρ (Π (S ↙ i) (T ↙ j)) ρ′)
                 λ rel → RelExp (Λ (S ↙ i) t) ρ (Λ (S′ ↙ i) t′) ρ′ (El _ (RelTyp.T≈T′ rel))
        helper {ρ} {ρ′} ρ≈ρ′
          with rel ρ≈ρ′
        ... | record { ⟦T⟧ = ⟦S⟧ ; ⟦T′⟧ = ⟦S⟧′ ; ↘⟦T⟧ = ↘⟦S⟧ ; ↘⟦T′⟧ = ↘⟦S⟧′ ; T≈T′ = S≈S′ }
          = record
            { ⟦T⟧   = Π i S.⟦T⟧ (T ↙ j) ρ
            ; ⟦T′⟧  = Π i S.⟦T′⟧ (T ↙ j) ρ′
            ; ↘⟦T⟧  = ⟦Π⟧ S.↘⟦T⟧
            ; ↘⟦T′⟧ = ⟦Π⟧ S.↘⟦T′⟧
            ; T≈T′  = proj₁ result
            }
          , record
            { ⟦t⟧   = Λ t ρ
            ; ⟦t′⟧  = Λ t′ ρ′
            ; ↘⟦t⟧  = ⟦Λ⟧ t
            ; ↘⟦t′⟧ = ⟦Λ⟧ t′
            ; t≈t′  = proj₂ result
            }
             where module S = RelTyp (rel ρ≈ρ′)
                   T≈T′ : S.⟦T⟧ ≈ S.⟦T′⟧ ∈ PERDef.𝕌 i _
                   T≈T′ = subst (λ f → S.⟦T⟧ ≈ S.⟦T′⟧ ∈ PERDef.𝕌 i (λ {j′} → f {j′})) (sym (𝕌-wf-gen i λ l<i → (≤-trans l<i (≤-trans (m≤m⊔n i j) (≤-reflexive refl))))) S.T≈T′

                   Πres : a ≈ b ∈ El i S.T≈T′ →
                          Σ (ΠRT T (ρ ↦ a) T (ρ′ ↦ b) (𝕌 j)) (λ res → Π̂ (Λ t ρ) a (Λ t′ ρ′) b (El j (ΠRT.T≈T′ res)))
                   Πres {a} {b} a≈b
                     with t≈t′ {ρ ↦ a} {ρ′ ↦ b} (ρ≈ρ′ , a≈b)
                   ...  | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
                        , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
                        = record
                          { ↘⟦T⟧  = ↘⟦T⟧
                          ; ↘⟦T′⟧ = ↘⟦T′⟧
                          ; T≈T′  = T≈T′
                          }
                        , record
                          { fa     = ⟦t⟧
                          ; fa′    = ⟦t′⟧
                          ; ↘fa    = Λ∙ ↘⟦t⟧
                          ; ↘fa′   = Λ∙ ↘⟦t′⟧
                          ; fa≈fa′ = t≈t′
                          }

                   result : Σ (Π i S.⟦T⟧ (T ↙ j) ρ ≈ Π i S.⟦T′⟧ (T ↙ j) ρ′ ∈ 𝕌 k) (λ R → Λ t ρ ≈ Λ t′ ρ′ ∈ El k R)
                   result = Π-bundle S.T≈T′ Πres refl


$-cong′ : ∀ {i j k} →
          Γ ⊨ r ≈ r′ ∶[ k ] Π (S ↙ i) (T ↙ j) →
          Γ ⊨ s ≈ s′ ∶[ i ] S →
          k ≡ max i j →
          -------------------------------
          Γ ⊨ r $ s ≈ r′ $ s′ ∶[ j ] T [| s ∶ S ↙ i ]
$-cong′ {_} {r} {r′} {S} {T} {s} {s′} {i} {j} {k} (⊨Γ , r≈r′) (⊨Γ₁ , s≈s′) refl = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 -----------------------------------------
                 Σ (RelTyp j (T [| s ∶ S ↙ i ]) ρ (T [| s ∶ S ↙ i ]) ρ′)
                 λ rel → RelExp (r $ s) ρ (r′ $ s′) ρ′ (El j (RelTyp.T≈T′ rel))
        helper {ρ} {ρ′} ρ≈ρ′
          with ρ≈ρ ← ⊨-irrel ⊨Γ ⊨Γ₁ (⟦⟧ρ-refl ⊨Γ ⊨Γ ρ≈ρ′)
             | ρ′≈ρ ← ⊨-irrel ⊨Γ ⊨Γ₁ (⟦⟧ρ-sym′ ⊨Γ ρ≈ρ′)
          with r≈r′ ρ≈ρ′
             | s≈s′ ρ≈ρ
             | s≈s′ ρ′≈ρ
             | s≈s′ (⊨-irrel ⊨Γ ⊨Γ₁ ρ≈ρ′)
        ...  | record { ↘⟦T⟧ = ⟦Π⟧ ↘⟦S⟧ ; ↘⟦T′⟧ = ⟦Π⟧ ↘⟦S⟧′ ; T≈T′ = Π eq iA RT _ _ }
             , record { ⟦t⟧ = ⟦r⟧ ; ⟦t′⟧ = ⟦r′⟧ ; ↘⟦t⟧ = ↘⟦r⟧ ; ↘⟦t′⟧ = ↘⟦r′⟧ ; t≈t′ = r≈r′ }
             | record { ⟦T⟧ = ⟦T⟧₁ ; ⟦T′⟧ = ⟦T′⟧₁ ; ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦T′⟧ = ↘⟦T′⟧₁ ; T≈T′ = T≈T′₁ }
             , record { ⟦t⟧ = ⟦t⟧₁ ; ⟦t′⟧ = ⟦t′⟧₁ ; ↘⟦t⟧ = ↘⟦t⟧₁ ; ↘⟦t′⟧ = ↘⟦t′⟧₁ ; t≈t′ = t≈t′₁ }
             | record { ⟦T⟧ = ⟦T⟧₂ ; ⟦T′⟧ = ⟦T′⟧₂ ; ↘⟦T⟧ = ↘⟦T⟧₂ ; ↘⟦T′⟧ = ↘⟦T′⟧₂ ; T≈T′ = T≈T′₂ }
             , record { ⟦t⟧ = ⟦t⟧₂ ; ⟦t′⟧ = ⟦t′⟧₂ ; ↘⟦t⟧ = ↘⟦t⟧₂ ; ↘⟦t′⟧ = ↘⟦t′⟧₂ ; t≈t′ = t≈t′₂ }
             | record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
             , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
             rewrite 𝕌-wf-gen i (ΠI≤ eq)
             rewrite 𝕌-wf-gen j (ΠO≤ eq)
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


Λ-β′ : ∀ {i j} →
       (S ↙ i) ∷ Γ ⊨ t ∶[ j ] T →
       Γ ⊨ s ∶[ i ] S →
       ----------------------------------
       Γ ⊨ Λ (S ↙ i) t $ s ≈ (t [| s ∶ S ↙ i ]) ∶[ j ] T [| s ∶ S ↙ i ]
Λ-β′ {S} {_} {t} {T} {s} {i} {j} (∷-cong ⊨Γ rel _ , ⊨t) (⊨Γ₁ , ⊨s) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 Σ (RelTyp j (T [| s ∶ S ↙ i ]) ρ (T [| s ∶ S ↙ i ]) ρ′)
                 λ rel → RelExp (Λ (S ↙ i) t $ s) ρ (t [| s ∶ S ↙ i ]) ρ′ (El j (RelTyp.T≈T′ rel))
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

            helper′ : Σ (RelTyp j (T [| s ∶ S ↙ i ]) ρ (T [| s ∶ S ↙ i ]) ρ′)
                      λ rel → RelExp (Λ (S ↙ i) t $ s) ρ (t [| s ∶ S ↙ i ]) ρ′ (El j (RelTyp.T≈T′ rel))
            helper′
              with ⊨t (ρ≈ρ′ , s≈s′₁)
            ...  | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
                 , record { ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ } = record
                                         { ↘⟦T⟧  = ⟦[]⟧ (⟦,⟧ ⟦I⟧ ↘⟦s⟧) ↘⟦T⟧
                                         ; ↘⟦T′⟧ = ⟦[]⟧ ((⟦,⟧ ⟦I⟧ ↘⟦s′⟧)) ↘⟦T′⟧
                                         ; T≈T′  = T≈T′
                                         }
                                       , record
                                         { ↘⟦t⟧  = ⟦$⟧ (⟦Λ⟧ _) ↘⟦s⟧ (Λ∙ ↘⟦t⟧)
                                         ; ↘⟦t′⟧ = ⟦[]⟧ (⟦,⟧ ⟦I⟧ ↘⟦s′⟧) ↘⟦t′⟧
                                         ; t≈t′  = t≈t′
                                         }

Λ-η′ : ∀ {i j k} →
       Γ ⊨ t ∶[ k ] Π (S ↙ i) (T ↙ j) →
       k ≡ max i j →
       ----------------------------------
       Γ ⊨ t ≈ Λ (S ↙ i) (t [ wk ] $ v 0) ∶[ k ] Π (S ↙ i) (T ↙ j)
Λ-η′ {_} {t} {S} {T} {i} {j} {k} (⊨Γ , ⊨t) refl = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 -----------------------------------------------------------
                 Σ (RelTyp k (Π (S ↙ i) (T ↙ j)) ρ (Π (S ↙ i) (T ↙ j)) ρ′)
                 λ rel → RelExp t ρ (Λ (S ↙ i) (t [ wk ] $ v 0)) ρ′ (El _ (RelTyp.T≈T′ rel))
        helper {ρ} {ρ′} ρ≈ρ′
          with ⊨t ρ≈ρ′
        ...  | record { ↘⟦T⟧ = ⟦Π⟧ ↘⟦S⟧ ; ↘⟦T′⟧ = ⟦Π⟧ ↘⟦S⟧′ ; T≈T′ = Π eq iS T≈T′ _ _ }
             , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
             rewrite 𝕌-wf-gen i (ΠI≤′ i j eq)
             rewrite 𝕌-wf-gen j (ΠO≤′ i j eq) = record
                                              { ↘⟦T⟧  = ⟦Π⟧ ↘⟦S⟧
                                              ; ↘⟦T′⟧ = ⟦Π⟧ ↘⟦S⟧′
                                              ; T≈T′  = proj₁ bund
                                              }
                                              , record
                                              { ↘⟦t⟧  = ↘⟦t⟧
                                              ; ↘⟦t′⟧ = ⟦Λ⟧ _
                                              ; t≈t′  = proj₂ bund
                                              }
          where
            helper′ : {a b : D} (inp : a ≈ b ∈ El _ iS) →
                      -----------------------------------------------------------------------------------
                      Π̂ (⟦t⟧) a ((Λ (t [ wk ] $ v 0) ρ′)) b (El _ (ΠRT.T≈T′ (T≈T′ inp)))
            helper′ {a} {b} inp
              with record { ↘fa = ↘fa ; ↘fa′ = ↘fa′ ; fa≈fa′ = fa≈fa′ } ← t≈t′ inp = record
                                       { ↘fa    = ↘fa
                                       ; ↘fa′   = Λ∙ (⟦$⟧ (⟦[]⟧ ⟦wk⟧ ↘⟦t′⟧) (⟦v⟧ 0) ↘fa′)
                                       ; fa≈fa′ = fa≈fa′
                                       }

            bund = Π-bundle iS (λ a≈b → T≈T′ a≈b , helper′ a≈b) eq

curry-helper-T : ∀ {i} → ⊨ (S ↙ i) ∷ Γ → Exp → Exp → Typ → Set
curry-helper-T {i = i} ⊨SΓ@(∷-cong ⊨Γ Srel _) t t′ T =
  ∀ {j} → (∀ {ρ ρ′} (ρ≈ρ′ : ρ ≈ ρ′ ∈ ⟦ ⊨SΓ ⟧ρ) → Σ (RelTyp j T ρ T ρ′) λ rel → let open RelTyp rel in RelExp t ρ t′ ρ′ (El _ T≈T′)) →
  ∀ {ρ ρ′} (ρ≈ρ′ : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ) → ∀ {a b} → a ≈ b ∈ El i (RelTyp.T≈T′ (Srel ρ≈ρ′)) →
  Σ (RelTyp j T (ρ ↦ a) T (ρ′ ↦ b)) λ rel → let open RelTyp rel in RelExp t (ρ ↦ a) t′ (ρ′ ↦ b) (El _ T≈T′)

curry-helper : ∀ {i} (⊨SΓ : ⊨ (S ↙ i) ∷ Γ) → curry-helper-T ⊨SΓ t t′ T
curry-helper {i = i} ⊨SΓ@(∷-cong ⊨Γ Srel _) orig ρ≈ρ′ a≈b = orig (ρ≈ρ′ , a≈b)


Λ-[]′ :  ∀ {i j k} →
         Γ ⊨s σ ∶ Δ →
         (S ↙ i) ∷ Δ ⊨ t ∶[ j ] T →
         k ≡ max i j →
         --------------------------------------------
         Γ ⊨ Λ (S ↙ i) t [ σ ] ≈ Λ (S [ σ ] ↙ i) (t [ q (S ↙ i) σ ]) ∶[ k ] Π (S ↙ i) (T ↙ j) [ σ ]
Λ-[]′ {_} {σ} {_} {S} {t} {T} {i} {j} {k} (⊨Γ , ⊨Δ , ⊨σ) (⊨SΔ@(∷-cong ⊨Δ₁ Srel₁ _) , ⊨t) refl = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 ------------------------------------------------------------------------------
                 Σ (RelTyp k (Π (S ↙ i) (T ↙ j) [ σ ]) ρ (Π (S ↙ i) (T ↙ j) [ σ ]) ρ′)
                 λ rel → RelExp (Λ (S ↙ i) t [ σ ]) ρ (Λ (S [ σ ] ↙ i) (t [ q (S ↙ i) σ ])) ρ′ (El _ (RelTyp.T≈T′ rel))
        helper {ρ} {ρ′} ρ≈ρ′
          with record { ⟦σ⟧ = ⟦σ⟧ ; ⟦δ⟧ = ⟦δ⟧ ; ↘⟦σ⟧ = ↘⟦σ⟧ ; ↘⟦δ⟧ = ↘⟦δ⟧ ; σ≈δ = σ≈δ } ← ⊨σ ρ≈ρ′
          with σ≈δ₁ ← ⊨-irrel ⊨Δ ⊨Δ₁ σ≈δ
             | record { ↘⟦T⟧ = ↘⟦S⟧ ; ↘⟦T′⟧ = ↘⟦S′⟧ ; T≈T′ = S≈S′ } ← Srel₁ (⊨-irrel ⊨Δ ⊨Δ₁ σ≈δ)
             | ⊨t′ ← curry-helper ⊨SΔ ⊨t (⊨-irrel ⊨Δ ⊨Δ₁ σ≈δ) = record
                          { ↘⟦T⟧  = ⟦[]⟧ ↘⟦σ⟧ (⟦Π⟧ ↘⟦S⟧)
                          ; ↘⟦T′⟧ = ⟦[]⟧ ↘⟦δ⟧ (⟦Π⟧ ↘⟦S′⟧)
                          ; T≈T′  = proj₁ bund
                          }
                        , record
                          { ↘⟦t⟧  = ⟦[]⟧ ↘⟦σ⟧ (⟦Λ⟧ _)
                          ; ↘⟦t′⟧ = ⟦Λ⟧ _
                          ; t≈t′  = proj₂ bund
                          }
          where helper′ : a ≈ b ∈ El i S≈S′ →
                          Σ (ΠRT T (⟦σ⟧ ↦ a) T (⟦δ⟧ ↦ b) (𝕌 j))
                          λ res → Π̂ (Λ t ⟦σ⟧) a (Λ (t [ q (S ↙ i) σ ]) ρ′) b (El j (ΠRT.T≈T′ res))
                helper′ {a} {b} a≈b
                  with ⊨t′ a≈b
                ... | record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
                    , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
                    = record
                    { ⟦T⟧   = ⟦T⟧
                    ; ⟦T′⟧  = ⟦T′⟧
                    ; ↘⟦T⟧  = ↘⟦T⟧
                    ; ↘⟦T′⟧ = ↘⟦T′⟧
                    ; T≈T′  = T≈T′
                    }
                    , record
                    { fa     = ⟦t⟧
                    ; fa′    = ⟦t′⟧
                    ; ↘fa    = Λ∙ ↘⟦t⟧
                    ; ↘fa′   = Λ∙ (⟦[]⟧ (⟦q⟧ ↘⟦δ⟧) ↘⟦t′⟧)
                    ; fa≈fa′ = t≈t′
                    }

                bund = Π-bundle S≈S′ helper′ refl

$-[]′ : ∀ {i j k} →
        Γ ⊨s σ ∶ Δ →
        Δ ⊨ r ∶[ k ] Π (S ↙ i) (T ↙ j) →
        Δ ⊨ s ∶[ i ] S →
        k ≡ max i j →
        ---------------------------------------------------------
        Γ ⊨ (r $ s) [ σ ] ≈ r [ σ ] $ s [ σ ] ∶[ j ] T [ σ , s [ σ ] ∶ S ↙ i ]
$-[]′ {_} {σ} {_} {r} {S} {T} {s} {i} {j} {k} (⊨Γ , ⊨Δ , ⊨σ) (⊨Δ₁ , ⊨r) (⊨Δ₂ , ⊨s) refl = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ →
                 Σ (RelTyp j (T [ σ , s [ σ ] ∶ S ↙ i ]) ρ (T [ σ , s [ σ ] ∶ S ↙ i ]) ρ′)
                 λ rel → RelExp ((r $ s) [ σ ]) ρ (r [ σ ] $ s [ σ ]) ρ′ (El j (RelTyp.T≈T′ rel))
        helper {ρ} {ρ′} ρ≈ρ′
          with record { ⟦σ⟧ = ⟦σ⟧ ; ⟦δ⟧ = ⟦δ⟧ ; ↘⟦σ⟧ = ↘⟦σ⟧ ; ↘⟦δ⟧ = ↘⟦δ⟧ ; σ≈δ = σ≈δ } ← ⊨σ ρ≈ρ′
          with ⊨r (⊨-irrel ⊨Δ ⊨Δ₁ σ≈δ)
             | ⊨s (⊨-irrel ⊨Δ ⊨Δ₂ σ≈δ)
        ...  | record { ↘⟦T⟧ = ⟦Π⟧ ↘⟦S⟧ ; ↘⟦T′⟧ = ⟦Π⟧ ↘⟦S′⟧ ; T≈T′ = Π eq iS Trel _ _ }
             , record { ⟦t⟧ = ⟦r⟧ ; ⟦t′⟧ = ⟦r′⟧ ; ↘⟦t⟧ = ↘⟦r⟧ ; ↘⟦t′⟧ = ↘⟦r′⟧ ; t≈t′ = r≈r′ }
             | record { ⟦T⟧ = ⟦S⟧₁ ; ⟦T′⟧ = ⟦S′⟧₁ ; ↘⟦T⟧ = ↘⟦S⟧₁ ; ↘⟦T′⟧ = ↘⟦S′⟧₁ ; T≈T′ = S≈S′₁ }
             , record { ⟦t⟧ = ⟦s⟧ ; ⟦t′⟧ = ⟦s′⟧ ; ↘⟦t⟧ = ↘⟦s⟧ ; ↘⟦t′⟧ = ↘⟦s′⟧ ; t≈t′ = s≈s′ }
             rewrite 𝕌-wf-gen i (ΠI≤ eq)
             rewrite 𝕌-wf-gen j (ΠO≤ eq)
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
