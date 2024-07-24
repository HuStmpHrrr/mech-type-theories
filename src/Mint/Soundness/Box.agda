{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

-- Semantic judgments for □ types
module Mint.Soundness.Box (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Data.Nat.Properties as ℕₚ

open import Mint.Statics.Properties
open import Mint.Semantics.Properties.Domain fext
open import Mint.Semantics.Properties.Evaluation fext
open import Mint.Semantics.Properties.PER fext
open import Mint.Completeness.Consequences fext
open import Mint.Soundness.Realizability fext
open import Mint.Soundness.Cumulativity fext
open import Mint.Soundness.LogRel
open import Mint.Soundness.ToSyntax fext
open import Mint.Soundness.Properties.LogRel fext
open import Mint.Soundness.Properties.Substitutions fext


σ；1∼extρ : (⊩Γ : ⊩ Γ) → Δ ⊢s σ ∶ ⊩Γ ® ρ → [] ∷⁺ Δ ⊢s σ ； 1 ∶ ⊩κ ⊩Γ ® (ext ρ 1)
σ；1∼extρ ⊩Γ σ∼ρ = record
                { ⊢σ = s-； L.[ [] ] ⊢σ (⊢κ ⊢Δ) refl
                ; Ψs⁻ = L.[ [] ]
                ; Γ≡ = refl
                ; ≈σ∥ = s-≈-refl ⊢σ
                ; O≡ = refl
                ; len≡ = refl
                ; step = σ∼ρ
                }
  where
        ⊢σ = s®⇒⊢s ⊩Γ σ∼ρ
        ⊢Δ = proj₁ (presup-s ⊢σ)

□-wf′ : ∀ {i} →
        [] ∷⁺ Γ ⊩ T ∶ Se i →
        --------------------
        Γ ⊩ □ T ∶ Se i
□-wf′ {Γ} {T} {i} ⊩T
  with ⊩T
... | record { ⊩Γ = ⊩κ ⊩Γ ; lvl = lvl ; krip = Tkrip } = record { ⊩Γ = ⊩Γ ; krip = krip }
  where
    ⊢T = ⊩⇒⊢-tm ⊩T
    ⊢Γ = ⊩⇒⊢ ⊩Γ

    krip : ∀ {Δ σ ρ} →
           Δ ⊢s σ ∶ ⊩Γ ® ρ →
           --------------------
           GluExp _ Δ (□ T) (Se i) σ ρ
    krip {Δ} {σ} {ρ} σ∼ρ
      with Tkrip (σ；1∼extρ ⊩Γ σ∼ρ)
    ...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦T⟧ ; T∈𝕌 = U i<lvl _ ; t∼⟦t⟧ = T∼⟦T⟧ }
        with T∼⟦T⟧
    ...    | record { t∶T = t∶T ; T≈ = T≈ ; A∈𝕌 = A∈𝕌 ; rel = Trel } = record
                  { ↘⟦T⟧ = ⟦Se⟧ _
                  ; ↘⟦t⟧ = ⟦□⟧ ↘⟦T⟧
                  ; T∈𝕌 = U′ i<lvl
                  ; t∼⟦t⟧ = record
                            { t∶T = t[σ] (□-wf ⊢T) ⊢σ
                            ; T≈ = lift-⊢≈-Se (Se-[] _ ⊢σ) i<lvl
                            ; A∈𝕌 = □ λ κ → 𝕌-mon κ A∈𝕌
                            ; rel = rel
                            }
                  }
      where
        ⊢σ = s®⇒⊢s ⊩Γ σ∼ρ

        rel : Glu-wellfounded lvl i<lvl Δ (sub (□ T) σ) (□ (λ κ → 𝕌-mon κ A∈𝕌))
        rel
          rewrite Glu-wellfounded-≡ i<lvl = record
                                            { T≈ = □-[] ⊢σ ⊢T
                                            ; krip = λ {_} {δ} Ψs ⊢ΨsΔ ⊢δ → ®-mon′ A∈𝕌 Trel (r-； Ψs ⊢δ (s-≈-refl (s-； Ψs (⊢r⇒⊢s ⊢δ) ⊢ΨsΔ refl)) refl)
                                            }

□-I′ : [] ∷⁺ Γ ⊩ t ∶ T →
       -----------------
       Γ ⊩ box t ∶ □ T
□-I′ {_} {t} {T} ⊩t
  with ⊩⇒⊢-both ⊩t
...  | ⊢T , ⊢t
    with ⊩t
...    | record { ⊩Γ = ⊩κ ⊩Γ ; lvl = lvl ; krip = tkrip } = record { ⊩Γ = ⊩Γ ; krip = krip }
  where
    krip : ∀ {Δ σ ρ} →
           Δ ⊢s σ ∶ ⊩Γ ® ρ →
           --------------------
           GluExp _ Δ (box t) (□ T) σ ρ
    krip {Δ} {σ} {ρ} σ∼ρ
      with tkrip (σ；1∼extρ ⊩Γ σ∼ρ)
    ...  | record { ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ } = record
                            { ↘⟦T⟧ = ⟦□⟧ ↘⟦T⟧
                            ; ↘⟦t⟧ = ⟦box⟧ ↘⟦t⟧
                            ; T∈𝕌 = □ λ κ → 𝕌-mon κ T∈𝕌
                            ; t∼⟦t⟧ = record
                                      { t∶T = t[σ] (□-I ⊢t) ⊢σ
                                      ; a∈El = λ m κ → record
                                                       { ↘ua = box↘ _
                                                       ; ↘ub = box↘ _
                                                       ; ua≈ub = subst
                                                                   (λ a → a ≈ a ∈ El _ (𝕌-mon (ins κ m) T∈𝕌))
                                                                   (sym (D-ins-ins ⟦t⟧ κ m))
                                                                   (El-mon T∈𝕌 (ins κ m) (𝕌-mon (ins κ m) T∈𝕌) (®El⇒∈El T∈𝕌 t∼⟦t⟧))
                                                       }
                                      ; T≈ = □-[] ⊢σ ⊢T
                                      ; krip = helper
                                      }
                            }
      where
        ⊢σ = s®⇒⊢s ⊩Γ σ∼ρ
        ⊢Δ = proj₁ (presup-s ⊢σ)
        ⊢σ；1 = s-； L.[ [] ] ⊢σ (⊢κ ⊢Δ) refl
        ⊢t[σ；1] = t[σ] ⊢t ⊢σ；1
        ⊢T[σ；1] = t[σ]-Se ⊢T ⊢σ；1

        helper : ∀ {Δ′ δ} (Ψs : L.List Ctx) →
                 ⊢ Ψs ++⁺ Δ′ →
                 Δ′ ⊢r δ ∶ Δ →
                 □Krip Ψs Δ′ (box t [ σ ]) (T [ σ ； 1 ]) δ (box ⟦t⟧)
                 (λ σ₁ n → _⊢_∶_®[ lvl ]_∈El (𝕌-mon (ins (mt σ₁) n) T∈𝕌))
        helper {Δ′} {δ} Ψs ⊢ΨsΔ′ ⊢δ = record
                                      { ↘ua = box↘ _
                                      ; rel = subst
                                                (_ ⊢ _ ∶ _ ®[ _ ]_∈El _)
                                                (sym (D-ins-ins ⟦t⟧ (mt δ) (len Ψs)))
                                                (®El-resp-≈
                                                  _
                                                  (®El-mon′
                                                    _
                                                    t∼⟦t⟧
                                                    (r-； Ψs ⊢δ (；-cong Ψs (s-≈-refl ⊢δ′) ⊢ΨsΔ′ refl) refl))
                                                  helper′)
                                      }
          where
            ⊢δ′ = ⊢r⇒⊢s ⊢δ
            δ；Ψs≈ = ；-cong Ψs (s-≈-refl ⊢δ′) ⊢ΨsΔ′ refl

            helper′ : Ψs ++⁺ Δ′ ⊢ t [ σ ； 1 ] [ δ ； len Ψs ] ≈ unbox (len Ψs) (box t [ σ ] [ δ ]) ∶ T [ σ ； 1 ] [ δ ； len Ψs ]
            helper′
              with unbox-[] L.[ [] ] (conv (t[σ] (□-I ⊢t) ⊢σ) (□-[] ⊢σ ⊢T)) (s-； Ψs ⊢δ′ ⊢ΨsΔ′ refl) refl
            ...  | eq rewrite +-identityʳ (len Ψs) =
              begin t [ σ ； 1 ] [ δ ； len Ψs ]                 ≈˘⟨ []-cong ([I] ⊢t[σ；1]) δ；Ψs≈ ⟩
                    t [ σ ； 1 ] [ I ] [ δ ； len Ψs ]           ≈⟨ []-cong (≈-conv ([]-cong (≈-refl ⊢t[σ；1]) (s-≈-sym (I；1≈I ⊢Δ))) ([I] ⊢T[σ；1])) δ；Ψs≈ ⟩
                    t [ σ ； 1 ] [ I ； 1 ] [ δ ； len Ψs ]       ≈˘⟨ []-cong (≈-conv (□-β L.[ [] ] ⊢t[σ；1] (⊢κ ⊢Δ) refl) ([I；1] ⊢T[σ；1])) δ；Ψs≈ ⟩
                    unbox 1 (box (t [ σ ； 1 ])) [ δ ； len Ψs ] ≈˘⟨ []-cong (≈-conv (unbox-cong L.[ [] ] (≈-conv (box-[] ⊢σ ⊢t) (□-[] ⊢σ ⊢T)) (⊢κ ⊢Δ) refl) ([I；1] ⊢T[σ；1])) δ；Ψs≈ ⟩
                    unbox 1 (box t [ σ ]) [ δ ； len Ψs ]       ≈⟨ eq ⟩
                    unbox (len Ψs) (box t [ σ ] [ δ ]) ∎
              where
                open ER

-- This requires extra [] ∷⁺ Γ ⊩ T ∶ Se i
-- as we don't have a semantic inversion on □ yet.
□-E′ : ∀ {i n} Ψs →
       [] ∷⁺ Γ ⊩ T ∶ Se i →
       Γ ⊩ t ∶ □ T →
       ⊩ Ψs ++⁺ Γ →
       len Ψs ≡ n →
       -----------------------------------
       Ψs ++⁺ Γ ⊩ unbox n t ∶ T [ I ； n ]
□-E′ {Γ = Γ@(_ ∷ _)} {T} {t} {i} {n} Ψs ⊩T ⊩t ⊩ΨsΓ refl
  with ⊩T | ⊩t | ⊩⇒⊢-both ⊩t
...  | record { ⊩Γ = ⊩κ ⊩Γ ; lvl = lvl ; krip = Tkrip }
     | record { ⊩Γ = ⊩Γ₁ ; lvl = lvl₁ ; krip = tkrip₁ }
     | ⊢□T , ⊢t = record { ⊩Γ = ⊩ΨsΓ ; krip = krip }
  where
    ⊢T : [] ∷⁺ Γ ⊢ T ∶ Se lvl₁
    ⊢T = □-inv ⊢□T

    ⊢Γ₁ = ⊩⇒⊢ ⊩Γ₁
    Ψs<ΨsΓ = subst (len Ψs <_) (sym (length-++⁺ Ψs Γ)) (m<m+n _ {len Γ} 0<1+n)

    krip : ∀ {Δ σ ρ} →
           Δ ⊢s σ ∶ ⊩ΨsΓ ® ρ →
           --------------------
           GluExp _ Δ (unbox n t) (T [ I ； n ]) σ ρ
    krip {Δ} {σ} {ρ} σ∼ρ
      with s®⇒⊢s ⊩ΨsΓ σ∼ρ | ∥-s®′ Ψs ⊩ΨsΓ σ∼ρ | s®-resp-O _ ⊩ΨsΓ σ∼ρ Ψs<ΨsΓ
    ...  | ⊢σ
         | Ψs′ , Δ′ , refl , Ψs′≡Oσ , ⊩Γ₂ , σ∥∼ρ∥
         | Oσ≡Oρ
        with presup-s ⊢σ | tkrip₁ (s®-irrel ⊩Γ₂ ⊩Γ₁ σ∥∼ρ∥)
    ...    | ⊢Δ , _
           | record { ⟦T⟧ = □ ⟦T⟧ ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ⟦□⟧ ↘⟦T⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; T∈𝕌 = □ T∈𝕌 ; t∼⟦t⟧ = t∼⟦t⟧ }
          with t∼⟦t⟧
    ...      | record { GT = GT ; t∶T = t∶T ; a∈El = a∈El ; T≈ = T≈ ; krip = □krip }
            with □krip Ψs′ ⊢Δ (⊢rI (proj₁ (presup-s (s®⇒⊢s ⊩Γ₂ σ∥∼ρ∥))))
    ...        | record { ↘ua = ↘ua ; rel = ∼ua }
              rewrite D-ap-vone ⟦t⟧ = record
                                     { ↘⟦T⟧ = ⟦[]⟧ (⟦；⟧ ⟦I⟧) (subst (⟦ T ⟧_↘ ⟦T⟧ [ Ψs′vone ]) (trans (cong (λ n → (ext (ρ ∥ len Ψs) 1) [ ins vone n ]) Ψs′≡Oρ) (ext1-mon (ρ ∥ len Ψs) Oρ)) (⟦⟧-mon Ψs′vone ↘⟦T⟧))
                                     ; ↘⟦t⟧ = ⟦unbox⟧ (len Ψs) ↘⟦t⟧ (subst (unbox∙_, _ ↘ _) Ψs′≡Oρ ↘ua)
                                     ; t∼⟦t⟧ = ®El-resp-≈
                                                 _
                                                 (®El-resp-T≈ _ (®El-cumu _ ∼ua (m≤n⊔m _ _)) GT[I；Ψs′]≈T[I；Ψs][σ])
                                                 (subst (λ n → _ ⊢ unbox n _ ≈ _ ∶ _) (sym Ψs′≡Oσ) unbox[t[σ∥][I]]≈unbox[t][σ])
                                     }
      where
        Ψs′vone = ins vone (len Ψs′)
        Oσ = O σ (len Ψs)
        Oρ = O ρ (len Ψs)
        Ψs′≡Oρ = trans Ψs′≡Oσ Oσ≡Oρ
        ⊢σ∥ = ∥-⊢s″ Ψs′ Ψs ⊢σ Ψs′≡Oσ
        ⊢Δ′ = ⊢⇒∥⊢ Ψs′ ⊢Δ

        unbox[t[σ∥][I]]≈unbox[t][σ] : Δ ⊢ unbox Oσ (t [ σ ∥ len Ψs ] [ I ]) ≈ unbox (len Ψs) t [ σ ] ∶ T [ I ； len Ψs ] [ σ ]
        unbox[t[σ∥][I]]≈unbox[t][σ] =
          begin unbox Oσ (t [ σ ∥ len Ψs ] [ I ]) ≈⟨ ≈-conv
                                                       (unbox-cong Ψs′ ([I] (conv (t[σ] ⊢t ⊢σ∥) (□-[] ⊢σ∥ ⊢T))) ⊢Δ Ψs′≡Oσ)
                                                       (begin
                                                         _ ≈˘⟨ subst (λ x → _ ⊢ _ [ _ ； x ] ≈ _ [ _ ； x ] ∶ _) Ψs′≡Oσ ([]-∘-；′ Ψs′ ⊢Δ ⊢T ⊢σ∥) ⟩
                                                         _ ≈⟨ []-cong-Se″ ⊢T (；-cong Ψs′ (s-≈-sym (I-∘ ⊢σ∥)) ⊢Δ Ψs′≡Oσ) ⟩
                                                         _ ≈⟨ []-；-∘ Ψs ⊢T (s-I ⊢Γ₁) ⊢σ ⟩
                                                         _ ∎) ⟩
                unbox Oσ (t [ σ ∥ len Ψs ])       ≈˘⟨ ≈-conv
                                                        (unbox-[] Ψs ⊢t ⊢σ refl)
                                                        (≈-trans
                                                           ([]-cong-Se″ ⊢T (；-cong Ψs′ (s-≈-sym (I-∘ ⊢σ∥)) ⊢Δ Ψs′≡Oσ))
                                                           ([]-；-∘ Ψs ⊢T (s-I ⊢Γ₁) ⊢σ)) ⟩
                unbox (len Ψs) t [ σ ] ∎
          where
            open ER

        GT[I；Ψs′]≈T[σ∥；1][I；Ψs′] : Δ ⊢ GT [ I ； len Ψs′ ] ≈ T [ σ ∥ len Ψs ； 1 ] [ I ； len Ψs′ ] ∶ Se (max lvl lvl₁)
        GT[I；Ψs′]≈T[σ∥；1][I；Ψs′]
          with Tkrip (s®-irrel (⊩κ ⊩Γ₂) (⊩κ ⊩Γ) (s®； L.[ [] ] (⊢κ ⊢Δ′) ⊩Γ₂ σ∥∼ρ∥ refl))
        ...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦T⟧₁ ; T∈𝕌 = U i<lvl _ ; t∼⟦t⟧ = T∼⟦T⟧₁ }
            rewrite ⟦⟧-det ↘⟦T⟧₁ ↘⟦T⟧
                  | Glu-wellfounded-≡ i<lvl
              with T∼⟦T⟧₁
        ...      | record { A∈𝕌 = ⟦T⟧∈𝕌₁ ; rel = T∼⟦T⟧₁ } = ®⇒≈
                                                               _
                                                               (®-cumu _ (®El⇒® _ ∼ua) (m≤n⊔m _ _))
                                                               (®-one-sided
                                                                  _
                                                                  _
                                                                  (®-cumu
                                                                     _
                                                                     (®-mon′
                                                                        _
                                                                        (®-cumu _ T∼⟦T⟧₁ (<⇒≤ i<lvl))
                                                                        (r-； Ψs′ (⊢rI ⊢Δ′) (；-cong Ψs′ (I-≈ ⊢Δ′) ⊢Δ refl) refl))
                                                                     (m≤m⊔n _ lvl₁)))

        GT[I；Ψs′]≈T[I；Ψs][σ] : Δ ⊢ GT [ I ； len Ψs′ ] ≈ T [ I ； len Ψs ] [ σ ] ∶ Se (max lvl lvl₁)
        GT[I；Ψs′]≈T[I；Ψs][σ] =
          begin GT [ I ； len Ψs′ ]                    ≈⟨ GT[I；Ψs′]≈T[σ∥；1][I；Ψs′] ⟩
                T [ σ ∥ len Ψs ； 1 ] [ I ； len Ψs′ ] ≈˘⟨ lift-⊢≈-Se-max′ ([]-∘-；′ Ψs′ ⊢Δ ⊢T ⊢σ∥) ⟩
                T [ σ ∥ len Ψs ； len Ψs′ ]            ≈˘⟨ lift-⊢≈-Se-max′ ([]-cong-Se″ ⊢T (；-cong Ψs′ (I-∘ ⊢σ∥) ⊢Δ refl)) ⟩
                T [ (I ∘ σ ∥ len Ψs) ； len Ψs′ ]      ≈⟨ subst (λ n → _ ⊢ _ [ _ ； n ] ≈ _ ∶ _) (sym Ψs′≡Oσ) (lift-⊢≈-Se-max′ ([]-；-∘ Ψs ⊢T (s-I ⊢Γ₁) ⊢σ)) ⟩
                T [ I ； len Ψs ] [ σ ]                ∎
          where
            open ER
