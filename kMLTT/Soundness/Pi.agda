{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Soundness.Pi (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Data.Nat.Properties as ℕₚ

open import kMLTT.Statics.Properties
open import kMLTT.Semantics.Properties.Domain fext
open import kMLTT.Semantics.Properties.Evaluation fext
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Completeness.Consequences fext
open import kMLTT.Completeness.Fundamental fext
open import kMLTT.Soundness.Cumulativity fext
open import kMLTT.Soundness.LogRel
open import kMLTT.Soundness.ToSyntax fext
open import kMLTT.Soundness.Properties.LogRel fext
open import kMLTT.Soundness.Properties.Substitutions fext


Π-wf′ : ∀ {i} →
        Γ ⊩ S ∶ Se i →
        S ∺ Γ ⊩ T ∶ Se i →
        --------------------
        Γ ⊩ Π S T ∶ Se i
Π-wf′ {Γ} {S} {T} {i} ⊩S ⊩T
  with ⊩S | ⊩⇒⊢-tm ⊩S | ⊩T | ⊩⇒⊢-tm ⊩T
...  | record { ⊩Γ = ⊩Γ ; lvl = lvl ; krip = Skrip }
     | ⊢S
     | record { ⊩Γ = (⊩∺ ⊩Γ₁ ⊢S₁ gS) ; lvl = lvl₁ ; krip = Tkrip₁ }
     | ⊢T
    with fundamental-⊢t ⊢T
...    | ∺-cong ⊨Γ₁ Srel₁ , n₁ , Trel₁ = record { ⊩Γ = ⊩Γ ; krip = krip }
  where
    krip : ∀ {Δ σ ρ} →
           Δ ⊢s σ ∶ ⊩Γ ® ρ →
           GluExp lvl Δ (Π S T) (Se i) σ ρ
    krip {Δ} {σ} {ρ} σ∼ρ
      with Skrip σ∼ρ | s®⇒⟦⟧ρ ⊩Γ σ∼ρ
    ...  | record { ⟦t⟧ = ⟦S⟧ ; ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦S⟧ ; T∈𝕌 = U i<lvl _ ; t∼⟦t⟧ = S∼⟦S⟧ }
         | ⊨Γ , ρ∈
          with S∼⟦S⟧
    ...      | record { t∶T = t∶S ; T≈ = S≈ ; A∈𝕌 = S∈𝕌 ; rel = S∼⟦S⟧ } = record
                { ↘⟦T⟧ = ⟦Se⟧ _
                ; ↘⟦t⟧ = ⟦Π⟧ ↘⟦S⟧
                ; T∈𝕌 = U′ i<lvl
                ; t∼⟦t⟧ = record
                          { t∶T = t[σ] (Π-wf ⊢S ⊢T) ⊢σ
                          ; T≈ = lift-⊢≈-Se (Se-[] _ ⊢σ) i<lvl
                          ; A∈𝕌 = Π (λ κ → 𝕌-mon κ S∈𝕌) ΠRTT
                          ; rel = subst (λ f → f _ _ (Π (λ κ → 𝕌-mon κ S∈𝕌) ΠRTT)) (sym (Glu-wellfounded-≡ i<lvl)) rel
                          }
                }
      where
        ⊢σ = s®⇒⊢s ⊩Γ σ∼ρ
        ⊢Δ = proj₁ (presup-s ⊢σ)

        ΠRTT : {a a′ : D} (κ : UMoT) →
               a ≈ a′ ∈ El _ (𝕌-mon κ S∈𝕌) →
               ΠRT T (ρ [ κ ] ↦ a) T (ρ [ κ ] ↦ a′) (𝕌 i)
        ΠRTT {a} {a′} κ a≈a′ = helper
          where
            ρ[κ]≈ρ[κ]′₁ : drop (ρ [ κ ] ↦ a) ≈ drop (ρ [ κ ] ↦ a′) ∈ ⟦ ⊨Γ₁ ⟧ρ
            ρ[κ]≈ρ[κ]′₁
              rewrite drop-↦ (ρ [ κ ]) a
                    | drop-↦ (ρ [ κ ]) a′ = ⟦⟧ρ-mon ⊨Γ₁ κ (⊨-irrel ⊨Γ ⊨Γ₁ ρ∈)

            a≈a′₁ : a ≈ a′ ∈ El _ (RelTyp.T≈T′ (Srel₁ ρ[κ]≈ρ[κ]′₁))
            a≈a′₁
              with Srel₁ ρ[κ]≈ρ[κ]′₁
            ...  | record { ↘⟦T⟧ = ↘⟦S⟧₁ ; ↘⟦T′⟧ = ↘⟦S′⟧₁ ; T≈T′ = S≈S′ }
                rewrite drop-↦ (ρ [ κ ]) a
                      | drop-↦ (ρ [ κ ]) a′
                      | ⟦⟧-det ↘⟦S⟧₁ (⟦⟧-mon κ ↘⟦S⟧) = El-one-sided (𝕌-mon κ S∈𝕌) S≈S′ a≈a′

            helper : ΠRT T (ρ [ κ ] ↦ a) T (ρ [ κ ] ↦ a′) (𝕌 i)
            helper
              with Trel₁ (ρ[κ]≈ρ[κ]′₁ , a≈a′₁)
            ...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₁ _ }
                 , record { ↘⟦t⟧ = ↘⟦T⟧ ; ↘⟦t′⟧ = ↘⟦T′⟧ ; t≈t′ = T≈T′ }
                rewrite 𝕌-wellfounded-≡-𝕌 _ i<n₁ = record
                                                   { ↘⟦T⟧ = ↘⟦T⟧
                                                   ; ↘⟦T′⟧ = ↘⟦T′⟧
                                                   ; T≈T′ = T≈T′
                                                   }

        rel : Δ ⊢ Π S T [ σ ] ®[ i ] Π (λ κ → 𝕌-mon κ S∈𝕌) ΠRTT
        rel = record
              { ⊢OT = t[σ]-Se ⊢T (⊢q ⊢σ ⊢S)
              ; T≈ = Π-[] ⊢σ ⊢S ⊢T
              ; krip = helper
              }
          where
            helper : ∀ {Δ′ δ} →
                     Δ′ ⊢r δ ∶ Δ →
                     ΠRel i Δ′ (S [ σ ]) (T [ q σ ]) δ (λ κ → 𝕌-mon κ S∈𝕌)
                       (λ σ₁ → _⊢_®[ i ] 𝕌-mon (mt σ₁) S∈𝕌)
                       (λ σ₁ a∈ → _⊢_®[ i ] ΠRT.T≈T′ (ΠRTT (mt σ₁) a∈))
                       (λ σ₁ → _⊢_∶_®[ i ]_∈El 𝕌-mon (mt σ₁) S∈𝕌)
            helper {Δ′} {δ} ⊢δ = record
                                { IT-rel = ®-mon S∈𝕌 S∈𝕌′ (subst (λ f → f _ _ _) (Glu-wellfounded-≡ i<lvl) S∼⟦S⟧) ⊢δ
                                ; OT-rel = helper′
                                }
              where
                S∈𝕌′ = 𝕌-mon (mt δ) S∈𝕌
                ⊢δ′ = ⊢r⇒⊢s ⊢δ

                helper′ : ∀ {s a} →
                          Δ′ ⊢ s ∶ S [ σ ] [ δ ] ®[ i ] a ∈El S∈𝕌′ →
                          (a∈ : a ∈′ El _ S∈𝕌′) →
                          Δ′ ⊢ T [ q σ ] [ δ , s ] ®[ i ] ΠRT.T≈T′ (ΠRTT (mt δ) a∈)
                helper′ {s} {a} s∼a a∈
                  with gS (s®-mon ⊩Γ₁ ⊢δ (s®-irrel ⊩Γ ⊩Γ₁ σ∼ρ)) | s®-cons (⊩∺ ⊩Γ₁ ⊢S₁ gS) {t = s} {a} (s®-mon ⊩Γ₁ ⊢δ (s®-irrel ⊩Γ ⊩Γ₁ σ∼ρ))
                ...  | record { ↘⟦T⟧ = ↘⟦S⟧₁ ; T∈𝕌 = S∈𝕌₁ ; T∼⟦T⟧ = S∼⟦S⟧₁ } | f
                    rewrite ⟦⟧-det ↘⟦S⟧₁ (⟦⟧-mon (mt δ) ↘⟦S⟧)
                      with ΠRTT (mt δ) a∈
                         | Tkrip₁ (f (®El-master S∈𝕌′ S∈𝕌₁ S∈𝕌′ S∼⟦S⟧₁ s∼a ([∘]-Se ⊢S ⊢σ ⊢δ′)))
                ...      | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
                         | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦T⟧₁ ; T∈𝕌 = U i<lvl₁ _ ; t∼⟦t⟧ = T∼⟦T⟧₁ }
                        rewrite Glu-wellfounded-≡ i<lvl₁
                              | ⟦⟧-det ↘⟦T⟧₁ ↘⟦T⟧
                          with T∼⟦T⟧₁
                ...          | record { A∈𝕌 = T∈𝕌 ; rel = rel } = ®-one-sided T∈𝕌 T≈T′ (®-resp-≈ T∈𝕌 rel T[σ∘δ,s]≈T[σ∘wk,v0][δ,s])
                  where
                    T[σ∘δ,s]≈T[σ∘wk,v0][δ,s] : Δ′ ⊢ T [ (σ ∘ δ) , s ] ≈ T [ (σ ∘ wk) , v 0 ] [ δ , s ] ∶ Se i
                    T[σ∘δ,s]≈T[σ∘wk,v0][δ,s] =
                      begin T [ (σ ∘ δ) , s ]                ≈˘⟨ []-cong-Se″ ⊢T (q∘,≈∘, ⊢σ ⊢S ⊢δ′ ⊢s) ⟩
                            T [ ((σ ∘ wk) , v 0) ∘ (δ , s) ] ≈˘⟨ [∘]-Se
                                                                    ⊢T
                                                                    (s-,
                                                                       (s-∘ (s-wk ⊢S[σ]Δ) ⊢σ)
                                                                       ⊢S
                                                                       (conv (vlookup ⊢S[σ]Δ here) ([∘]-Se ⊢S ⊢σ (s-wk ⊢S[σ]Δ))))
                                                                    (s-, ⊢δ′ (t[σ]-Se ⊢S ⊢σ) ⊢s) ⟩
                            T [ (σ ∘ wk) , v 0 ] [ δ , s ]   ∎
                      where
                        open ER

                        ⊢s = ®El⇒tm (𝕌-mon (mt δ) S∈𝕌) s∼a
                        ⊢S[σ]Δ = ⊢∺ ⊢Δ (t[σ]-Se ⊢S ⊢σ)

Λ-I′ : ∀ {i} →
       Γ ⊩ S ∶ Se i →
       S ∺ Γ ⊩ t ∶ T →
       ------------------
       Γ ⊩ Λ t ∶ Π S T
Λ-I′ ⊩S ⊩t = {!!}

Λ-E′ : ∀ {i} →
       Γ ⊩ T ∶ Se i →
       Γ ⊩ r ∶ Π S T →
       Γ ⊩ s ∶ S →
       ---------------------
       Γ ⊩ r $ s ∶ T [| s ]
Λ-E′ ⊩T ⊩r ⊩s = {!!}
