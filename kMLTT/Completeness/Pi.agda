{-# OPTIONS --without-K --safe #-}

open import Level using ()
open import Axiom.Extensionality.Propositional

module kMLTT.Completeness.Pi (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Data.Nat.Properties

open import Lib
open import kMLTT.Completeness.LogRel

open import kMLTT.Semantics.Properties.Domain fext
open import kMLTT.Semantics.Properties.Evaluation fext
open import kMLTT.Semantics.Properties.PER fext


Π-[]′ : ∀ {i} →
        Γ ⊨s σ ∶ Δ →
        Δ ⊨ S ∶ Se i →
        (S ∺ Δ) ⊨ T ∶ Se i →
        -------------------------------------------------
        Γ ⊨ Π S T [ σ ] ≈ Π (S [ σ ]) (T [ q σ ]) ∶ Se i
Π-[]′ {_} {σ} {_} {S} {T} {i} (⊨Γ , ⊨Δ , ⊨σ) (⊨Δ₁ , ⊨S) (∷-cong ⊨Δ₂ rel , ⊨T) = ⊨Γ , helper
  where helper : ρ ≈ ρ′ ∈ ⟦ ⊨Γ ⟧ρ → Σ (RelTyp (Se i) ρ (Se i) ρ′) (λ rel → RelExp (Π S T [ σ ]) ρ (Π (S [ σ ]) (T [ q σ ])) ρ′ (El∞ (RelTyp.T≈T′ rel)))
        helper {ρ} {ρ′} ρ≈ρ′ = help
          where module σ = RelSubsts (⊨σ ρ≈ρ′)
                help : Σ (RelTyp (Se i) ρ (Se i) ρ′) (λ rel → RelExp (Π S T [ σ ]) ρ (Π (S [ σ ]) (T [ q σ ])) ρ′ (El∞ (RelTyp.T≈T′ rel)))
                help
                  with ⊨S (⊨-irrel ⊨Δ ⊨Δ₁ σ.σ≈δ)
                ...  | rt@record { ⟦T⟧ = .(U i) ; ⟦T′⟧ = .(U i) ; ↘⟦T⟧ = (⟦Se⟧ .i) ; ↘⟦T′⟧ = (⟦Se⟧ .i) ; T≈T′ = _ , PERDef.U i<j eq }
                     , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
                     = record
                        { ⟦T⟧   = U i
                        ; ⟦T′⟧  = U i
                        ; ↘⟦T⟧  = ⟦Se⟧ i
                        ; ↘⟦T′⟧ = ⟦Se⟧ i
                        ; T≈T′  = -, PERDef.U i<j eq
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
                          where step : (κ : UnMoT) → a ≈ a′ ∈ El i (𝕌-mon κ S≈) → ΠRT T (σ.⟦σ⟧ [ κ ] ↦ a) (T [ q σ ]) (ρ′ [ κ ] ↦ a′) (𝕌 i)
                                step {a} {a′} κ a≈a′
                                  with subst₂ (_≈_∈ ⟦ ⊨Δ₂ ⟧ρ) (sym (drop-↦ _ _)) (sym (drop-↦ _ _)) (⊨-irrel ⊨Δ ⊨Δ₂ (⟦⟧ρ-mon ⊨Δ κ σ.σ≈δ))
                                ...  | σ≈δ₁ = answer
                                  where insert : a ≈ a′ ∈ El∞ (RelTyp.T≈T′ (rel σ≈δ₁))
                                        insert
                                          with rel σ≈δ₁
                                        ...  | record { ⟦T⟧ = ⟦T⟧ ; ⟦T′⟧ = ⟦T′⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = j , T≈T′ }
                                             rewrite ⟦⟧-det (subst (⟦ S ⟧_↘ ⟦T⟧) (drop-↦ _ _) ↘⟦T⟧) (⟦⟧-mon κ ↘⟦t⟧)
                                                   | ⟦⟧-det (subst (⟦ S ⟧_↘ ⟦T′⟧) (drop-↦ _ _) ↘⟦T′⟧) (⟦⟧-mon κ ↘⟦t′⟧) = 𝕌-irrel (𝕌-mon κ S≈) T≈T′ a≈a′

                                        answer : ΠRT T (σ.⟦σ⟧ [ κ ] ↦ a) (T [ q σ ]) (ρ′ [ κ ] ↦ a′) (𝕌 i)
                                        answer
                                          with ⊨T {σ.⟦σ⟧ [ κ ] ↦ a} {σ.⟦δ⟧ [ κ ] ↦ a′} (σ≈δ₁ , insert)
                                        ...  | record { ⟦T⟧ = .(U i) ; ⟦T′⟧ = .(U i) ; ↘⟦T⟧ = (⟦Se⟧ .i) ; ↘⟦T′⟧ = (⟦Se⟧ .i) ; T≈T′ = _ , PERDef.U i<j eq }
                                             , re = record
                                                      { ⟦T⟧   = re.⟦t⟧
                                                      ; ⟦T′⟧  = re.⟦t′⟧
                                                      ; ↘⟦T⟧  = re.↘⟦t⟧
                                                      ; ↘⟦T′⟧ = ⟦[]⟧ (⟦,⟧ (⟦∘⟧ (⟦p⟧ ⟦I⟧) (subst (⟦ σ ⟧s_↘ σ.⟦δ⟧ [ κ ]) (sym (drop-↦ _ _)) (⟦⟧s-mon κ σ.↘⟦δ⟧))) (⟦v⟧ 0)) re.↘⟦t′⟧
                                                      ; T≈T′  = subst (re.⟦t⟧ ≈ re.⟦t′⟧ ∈_) (𝕌-wellfounded-≡-𝕌 _ i<j) re.t≈t′
                                                      }
                                          where module re = RelExp re


-- -- Π-cong     : ∀ {i} →
-- --              Γ ⊨ S ≈ S′ ∶ Se i →
-- --              S ∺ Γ ⊨ T ≈ T′ ∶ Se i →
-- --              --------------------------
-- --              Γ ⊨ Π S T ≈ Π S′ T′ ∶ Se i

-- -- Λ-cong     : S ∺ Γ ⊨ t ≈ t′ ∶ T →
-- --              -----------------------
-- --              Γ ⊨ Λ t ≈ Λ t′ ∶ Π S T
-- -- $-cong     : Γ ⊨ r ≈ r′ ∶ Π S T →
-- --              Γ ⊨ s ≈ s′ ∶ S →
-- --              -------------------------------
-- --              Γ ⊨ r $ s ≈ r′ $ s′ ∶ T [| s ]
-- -- Λ-[]       : Γ ⊨s σ ∶ Δ →
-- --              S ∺ Δ ⊨ t ∶ T →
-- --              --------------------------------------------
-- --              Γ ⊨ Λ t [ σ ] ≈ Λ (t [ q σ ]) ∶ Π S T [ σ ]
-- -- $-[]       : Γ ⊨s σ ∶ Δ →
-- --              Δ ⊨ r ∶ Π S T →
-- --              Δ ⊨ s ∶ S →
-- --              ---------------------------------------------------------
-- --              Γ ⊨ (r $ s) [ σ ] ≈ r [ σ ] $ s [ σ ] ∶ T [ σ , s [ σ ] ]
-- -- Λ-β        : S ∺ Γ ⊨ t ∶ T →
-- --              Γ ⊨ s ∶ S →
-- --              ----------------------------------
-- --              Γ ⊨ Λ t $ s ≈ t [| s ] ∶ T [| s ]
-- -- Λ-η        : Γ ⊨ t ∶ Π S T →
-- --              ----------------------------------
-- --              Γ ⊨ t ≈ Λ (t [ wk ] $ v 0) ∶ Π S T
