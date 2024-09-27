{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

-- Semantic judgments for Π types
module NonCumulative.Soundness.Pi (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂) where

open import Lib
open import Data.Nat.Properties as ℕₚ

open import NonCumulative.Statics.Ascribed.Misc
open import NonCumulative.Statics.Ascribed.Refl
open import NonCumulative.Statics.Ascribed.Properties.Subst
open import NonCumulative.Statics.Ascribed.Properties
open import NonCumulative.Statics.Ascribed.Presup
open import NonCumulative.Statics.Ascribed.Properties
open import NonCumulative.Semantics.Properties.PER fext
open import NonCumulative.Completeness.Fundamental fext
open import NonCumulative.Soundness.Realizability fext
open import NonCumulative.Soundness.LogRel
open import NonCumulative.Soundness.ToSyntax fext
open import NonCumulative.Soundness.Properties.LogRel fext
open import NonCumulative.Soundness.Properties.Bundle fext
open import NonCumulative.Soundness.Properties.Substitutions fext


Π-wf′ : ∀ {i j k} →
        i ≡ max j k →
        Γ ⊩ S ∶[ 1 + j ] Se j →
        (S ↙ j) ∷ Γ ⊩ T ∶[ 1 + k ] Se k →
        --------------------
        Γ ⊩ Π (S ↙ j) (T ↙ k) ∶[ 1 + i ] Se i
Π-wf′ {Γ} {S} {T} {i} {j} {k} refl ⊩S ⊩T
  with ⊩S | ⊩⇒⊢-tm ⊩S | ⊩T | ⊩⇒⊢-tm ⊩T
...  | record { ⊩Γ = ⊩Γ ; krip = Skrip }
     | ⊢S
     | record { ⊩Γ = (⊩∷ ⊩Γ₁ ⊢S₁ gluS) ; krip = Tkrip₁ }
     | ⊢T
    with fundamental-⊢t ⊢T
...    | ∷-cong ⊨Γ₁ Srel₁ _ , Trel₁ = record { ⊩Γ = ⊩Γ ; krip = krip }
  where
    krip : ∀ {Δ σ ρ} →
           Δ ⊢s σ ∶ ⊩Γ ® ρ →
           GluExp (1 + i) Δ (Π (S ↙ j) (T ↙ k)) (Se i) σ ρ
    krip {Δ} {σ} {ρ} σ∼ρ
      with Skrip σ∼ρ | s®⇒⟦⟧ρ ⊩Γ σ∼ρ
    ...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦S⟧ ; T∈𝕌 = U 1+j≡1+j j≡j ; t∼⟦t⟧ = S∼⟦S⟧ }
         | ⊨Γ , ρ∈
          with S∼⟦S⟧
    ...      | record { A∈𝕌 = S∈𝕌 ; rel = S∼⟦S⟧ }
            rewrite 𝕌-wf-gen (max j k) (U≤ refl)
                  | Glu-wellfounded-≡ (≤-reflexive (sym 1+j≡1+j)) = record
                { ↘⟦T⟧ = ⟦Se⟧ _
                ; ↘⟦t⟧ = ⟦Π⟧ ↘⟦S⟧
                ; T∈𝕌 = U′
                ; t∼⟦t⟧ = ®El-𝕌-𝕌 (Π-𝕌 S∈𝕌 ΠRTT refl) U′ (record
                    { t∶T = t[σ] (Π-wf ⊢S ⊢T refl) ⊢σ
                    ; T≈ = Se-[] _ ⊢σ
                    ; A∈𝕌 = Π-𝕌 S∈𝕌 ΠRTT refl
                    ; rel = ®-Π-𝕌 refl S∈𝕌 ΠRTT (Π-𝕌 S∈𝕌 ΠRTT refl) (record
                      { IT = _
                      ; OT = _
                      ; ⊢IT = t[σ]-Se ⊢S ⊢σ
                      ; ⊢OT = t[σ]-Se ⊢T (⊢q ⊢Δ ⊢σ ⊢S)
                      ; T≈ = Π-[] ⊢σ ⊢S ⊢T refl
                      ; krip = helper })
                    })
                }
      where
        ⊢σ = s®⇒⊢s ⊩Γ σ∼ρ
        ⊢Δ = proj₁ (presup-s ⊢σ)

        ΠRTT : {a a′ : D} →
               a ≈ a′ ∈ El _ S∈𝕌 →
               ΠRT T (ρ ↦ a) T (ρ ↦ a′) (𝕌 k)
        ΠRTT {a} {a′} a≈a′ = helper
          where
            ρ≈′ : ρ ∈′ ⟦ ⊨Γ₁ ⟧ρ
            ρ≈′ = ⊨-irrel ⊨Γ ⊨Γ₁ ρ∈

            a≈a′₁ : a ≈ a′ ∈ El _ (RelTyp.T≈T′ (Srel₁ ρ≈′))
            a≈a′₁
              with Srel₁ ρ≈′
            ...  | record { ↘⟦T⟧ = ↘⟦S⟧₁ ; ↘⟦T′⟧ = ↘⟦S′⟧₁ ; T≈T′ = S≈S′ }
                 rewrite ⟦⟧-det ↘⟦S⟧₁ ↘⟦S⟧ = El-one-sided S∈𝕌 S≈S′ a≈a′

            helper : ΠRT T (ρ ↦ a) T (ρ ↦ a′) (𝕌 k)
            helper
              with Trel₁ (ρ≈′ , a≈a′₁)
            ...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U 1+k≡1+k _ }
                 , record { ↘⟦t⟧ = ↘⟦T⟧ ; ↘⟦t′⟧ = ↘⟦T′⟧ ; t≈t′ = T≈T′ }
                 rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym 1+k≡1+k)) = record
                  { ↘⟦T⟧ = ↘⟦T⟧
                  ; ↘⟦T′⟧ = ↘⟦T′⟧
                  ; T≈T′ = T≈T′
                  }
        helper : ∀ {Δ′ τ} →
                    Δ′ ⊢w τ ∶ Δ →
                    ΠRel j Δ′ (S [ σ ]) (T [ q (S ↙ j) σ ]) τ (𝕌-wellfounded j) S∈𝕌
                      (_⊢_®[ j ] S∈𝕌)
                      (λ a∈ → _⊢_®[ k ] ΠRT.T≈T′ (ΠRTT a∈))
                      (_⊢_∶_®[ j ]_∈El S∈𝕌)
        helper {Δ′} {τ} ⊢τ = record
          { IT-rel = ®-mon _ _ S∼⟦S⟧ ⊢τ
          ; OT-rel = λ s® a∈ → helper′ s® a∈
          }
          where
            ⊢τ′ = ⊢w⇒⊢s ⊢τ

            helper′ : ∀ {s a} →
                      Δ′ ⊢ s ∶ S [ σ ] [ τ ] ®[ j ] a ∈El S∈𝕌 →
                      (a∈ : a ∈′ El _ S∈𝕌) →
                      Δ′ ⊢ T [ q (S ↙ j) σ ] [ τ , s ∶ S [ σ ] ↙ j ] ®[ k ] ΠRT.T≈T′ (ΠRTT a∈)
            helper′ {s} {a} s®a a∈
              with gluS (s®-mon ⊩Γ₁ ⊢τ (s®-irrel ⊩Γ ⊩Γ₁ σ∼ρ)) | s®-cons (⊩∷ ⊩Γ₁ ⊢S₁ gluS) {t = s} {a} (s®-mon ⊩Γ₁ ⊢τ (s®-irrel ⊩Γ ⊩Γ₁ σ∼ρ))
            ...  | record { ↘⟦T⟧ = ↘⟦S⟧₁ ; T∈𝕌 = S∈𝕌₁ ; T∼⟦T⟧ = S∼⟦S⟧₁ }
                 | f
                rewrite ⟦⟧-det ↘⟦S⟧₁ ↘⟦S⟧
                  with ΠRTT a∈
                     | Tkrip₁ (f ( ®El-≡ _ _ (®El-resp-T≈ _ s®a ([∘]-Se ⊢S ⊢σ ⊢τ′)) refl ))
            ...      | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
                     | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦T⟧₁ ; T∈𝕌 = U 1+k≡1+k _ ; t∼⟦t⟧ = T∼⟦T⟧₁ }
                    rewrite ⟦⟧-det ↘⟦T⟧₁ ↘⟦T⟧ | Glu-wellfounded-≡ (≤-reflexive (sym 1+k≡1+k))
                      with T∼⟦T⟧₁
            ...          | record { A∈𝕌 = T∈𝕌 ; rel = rel } = ®-one-sided T∈𝕌 T≈T′ (®-resp-≈ _ rel T[σ∘τ,s]≈T[σ∘wk,v0][τ,s])
              where
                T[σ∘τ,s]≈T[σ∘wk,v0][τ,s] : Δ′ ⊢ T [ (σ ∘ τ) , s ∶ S ↙ j ] ≈ T [ (σ ∘ wk) , v 0 ∶ S ↙ j ] [ τ , s ∶ S [ σ ] ↙ j ] ∶[ 1 + k ] Se k
                T[σ∘τ,s]≈T[σ∘wk,v0][τ,s] = begin
                    -- module parameter j is not used by q∘,≈∘, . picking any number is fine
                    T [ (σ ∘ τ) , s ∶ S ↙ j ]                                  ≈˘⟨ []-cong-Se‴ ⊢T (q∘,≈∘, {j = 0} ⊢σ ⊢S ⊢τ′ ⊢s) ⟩
                    T [ ((σ ∘ wk) , v 0 ∶ S ↙ j) ∘ (τ ,  s ∶ S [ σ ] ↙ j) ]   ≈˘⟨ [∘]-Se ⊢T (
                                                                                                  s-, (s-∘ (s-wk ⊢S[σ]Δ) ⊢σ) ⊢S
                                                                                                      (conv (vlookup ⊢S[σ]Δ here) ([∘]-Se ⊢S ⊢σ (s-wk ⊢S[σ]Δ))))
                                                                                                      (s-, ⊢τ′ (t[σ]-Se ⊢S ⊢σ) ⊢s) ⟩
                    T [ (σ ∘ wk) , v 0 ∶ S ↙ j ] [ τ , s ∶ S [ σ ] ↙ j ]
                  ∎
                  where
                    open ER

                    ⊢s = ®El⇒tm S∈𝕌 s®a
                    ⊢S[σ]Δ = ⊢∷ ⊢Δ (t[σ]-Se ⊢S ⊢σ)

Λ-I′ : ∀ {i j k} →
    i ≡ max j k →
    (S ↙ j) L.∷ Γ ⊩ t ∶[ k ] T →
    Γ ⊩ Λ (S ↙ j) t ∶[ i ] Π (S ↙ j) (T ↙ k)
Λ-I′ {S} {Γ} {t} {T} {i} {j} {k} refl ⊩t
  with ⊩t | ⊩⇒⊢-both ⊩t
...  | record { ⊩Γ = (⊩∷ ⊩Γ ⊢S gluS) ; krip = tkrip₁ }
     | ⊢T , ⊢t
    with fundamental-⊢t ⊢T | fundamental-⊢t ⊢t
...    | ∷-cong ⊨Γ₁ Srel₁ _ , Trel₁
       | ∷-cong ⊨Γ₂ Srel₂ _ , trel₂ = record { ⊩Γ = ⊩Γ ; krip = krip }
  where
    krip : ∀ {Δ σ ρ} →
           Δ ⊢s σ ∶ ⊩Γ ® ρ →
           GluExp i Δ (Λ (S ↙ j) t) (Π (S ↙ j) (T ↙ k)) σ ρ
    krip {Δ} {σ} {ρ} σ®ρ
      with gluS σ®ρ | s®⇒⟦⟧ρ ⊩Γ σ®ρ
    ...  | record { ⟦T⟧ = ⟦S⟧ ; ↘⟦T⟧ = ↘⟦S⟧ ; T∈𝕌 = S∈𝕌 ; T∼⟦T⟧ = S∼⟦S⟧ }
         | ⊨Γ , ρ∈ = record
            { ⟦T⟧ = _
            ; ⟦t⟧ = _
            ; ↘⟦T⟧ = ⟦Π⟧ ↘⟦S⟧
            ; ↘⟦t⟧ = ⟦Λ⟧ t
            ; T∈𝕌 = Π-𝕌 S∈𝕌 ΠRTT refl
            ; t∼⟦t⟧ = ®El-Π-𝕌 refl S∈𝕌 ΠRTT (Π-𝕌 S∈𝕌 ΠRTT refl) (record
              { t∶T = t[σ] (Λ-I ⊢S ⊢t refl) ⊢σ
              ; a∈El = Λt∈′El
              ; IT = _
              ; OT = _
              ; ⊢IT = t[σ]-Se ⊢S ⊢σ
              ; ⊢OT = t[σ]-Se ⊢T (⊢q ⊢Δ ⊢σ ⊢S)
              ; T≈ = Π-[] ⊢σ ⊢S ⊢T refl
              ; krip = Λrel
              })
            }
      where
        ⊢σ = s®⇒⊢s ⊩Γ σ®ρ
        ⊢Δ = proj₁ (presup-s ⊢σ)

        ΠRTT : {a a′ : D} →
              a ≈ a′ ∈ El j S∈𝕌 →
              ΠRT T (ρ ↦ a) T (ρ ↦ a′) (𝕌 k)
        ΠRTT {a} {a′} a≈a′ = helper
          where
            ρ≈′ : ρ ∈′ ⟦ ⊨Γ₁ ⟧ρ
            ρ≈′ = ⊨-irrel ⊨Γ ⊨Γ₁ ρ∈

            a≈a′₁ : a ≈ a′ ∈ El _ (RelTyp.T≈T′ (Srel₁ ρ≈′))
            a≈a′₁
              with Srel₁ ρ≈′
            ...  | record { ↘⟦T⟧ = ↘⟦S⟧₁ ; ↘⟦T′⟧ = ↘⟦S′⟧₁ ; T≈T′ = S≈S′ }
                 rewrite ⟦⟧-det ↘⟦S⟧₁ ↘⟦S⟧ = El-one-sided S∈𝕌 S≈S′ a≈a′

            helper : ΠRT T (ρ ↦ a) T (ρ ↦ a′) (𝕌 k)
            helper
              with Trel₁ (ρ≈′ , a≈a′₁)
            ...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U 1+k≡1+k _ }
                 , record { ↘⟦t⟧ = ↘⟦T⟧ ; ↘⟦t′⟧ = ↘⟦T′⟧ ; t≈t′ = T≈T′ }
                 rewrite 𝕌-wellfounded-≡-𝕌 _ (≤-reflexive (sym 1+k≡1+k)) = record
                    { ⟦T⟧ = _
                    ; ⟦T′⟧ = _
                    ; ↘⟦T⟧ = ↘⟦T⟧
                    ; ↘⟦T′⟧ = ↘⟦T′⟧
                    ; T≈T′ = T≈T′
                    }
        Λt∈′El : {a a′ : D} (a≈a′ : a ≈ a′ ∈ El _ S∈𝕌) →
                  Π̂ (Λ t ρ) a (Λ t ρ) a′ (El _ (ΠRT.T≈T′ (ΠRTT a≈a′)))
        Λt∈′El {a} {a′} a≈a′ = helper
          where
            ρ≈″ : ρ ∈′ ⟦ ⊨Γ₂ ⟧ρ
            ρ≈″ = ⊨-irrel ⊨Γ ⊨Γ₂ ρ∈

            a≈a′₂ : a ≈ a′ ∈ El _ (RelTyp.T≈T′ (Srel₂ ρ≈″))
            a≈a′₂
              with Srel₂ ρ≈″
            ...  | record { ↘⟦T⟧ = ↘⟦S⟧₂ ; ↘⟦T′⟧ = ↘⟦S′⟧₂ ; T≈T′ = S≈S′ }
                 rewrite ⟦⟧-det ↘⟦S⟧₂ ↘⟦S⟧ = El-one-sided S∈𝕌 S≈S′ a≈a′

            helper : Π̂ (Λ t ρ) a (Λ t ρ) a′ (El _ (ΠRT.T≈T′ (ΠRTT a≈a′)))
            helper
              with ΠRTT a≈a′
                  | trel₂ (ρ≈″ , a≈a′₂)
            ...   | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
                  | record { ↘⟦T⟧ = ↘⟦T⟧₂ ; ↘⟦T′⟧ = ↘⟦T′⟧₂ ; T≈T′ = T≈T′₂ }
                  , record { ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ }
                  rewrite ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₂
                        | ⟦⟧-det ↘⟦T′⟧ ↘⟦T′⟧₂ = record
                          { ↘fa = Λ∙ ↘⟦t⟧
                          ; ↘fa′ = Λ∙ ↘⟦t′⟧
                          ; fa≈fa′ = 𝕌-irrel T≈T′₂ T≈T′ t≈t′
                          }

        Λrel : ∀ {Δ′ τ} →
              Δ′ ⊢w τ ∶ Δ →
              ΛRel j Δ′ (Λ (S ↙ j) t [ σ ]) (S [ σ ]) (T [ q (S ↙ j) σ ]) τ (Λ t ρ) (𝕌-wellfounded j) S∈𝕌
                (_⊢_®[ j ] S∈𝕌)
                (_⊢_∶_®[ j ]_∈El S∈𝕌)
                (λ a∈ → _⊢_∶_®[ k ]_∈El ΠRT.T≈T′ (ΠRTT a∈))
        Λrel {Δ′} {τ} ⊢τ = record
          { IT-rel = ®-mon _ _ S∼⟦S⟧ ⊢τ
          ; ap-rel = helper
          }
          where
            ⊢τ′ = ⊢w⇒⊢s ⊢τ
            ⊢Δ′ = proj₁ (presup-s ⊢τ′)

            helper : ∀ {s b} →
                          Δ′ ⊢ s ∶ S [ σ ] [ τ ] ®[ j ] b ∈El S∈𝕌 →
                          (b∈ : b ∈′ El j S∈𝕌) →
                          ΛKripke Δ′ ((Λ (S ↙ j) t) [ σ ] [ τ ] $ s)
                                    (T [ q (S ↙ j) σ ] [ τ , s ∶ sub S σ ↙ j ])
                                    (Λ t ρ) b
                                    (_⊢_∶_®[ k ]_∈El ΠRT.T≈T′ (ΠRTT b∈))
            helper {s} {b} s®b b∈
              with gluS (s®-mon ⊩Γ ⊢τ σ®ρ) | s®-cons (⊩∷ ⊩Γ ⊢S gluS) {t = s} {b} (s®-mon ⊩Γ ⊢τ σ®ρ)
            ...  | record { ↘⟦T⟧ = ↘⟦S⟧₁ ; T∈𝕌 = S∈𝕌₁ ; T∼⟦T⟧ = S∼⟦S⟧₁ }
                  | f
                rewrite ⟦⟧-det ↘⟦S⟧₁ ↘⟦S⟧
                  with ΠRTT b∈
                      | tkrip₁ (f (®El-≡ _ _ (®El-resp-T≈ _ s®b ([∘]-Se ⊢S ⊢σ ⊢τ′)) refl))
            ...       | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
                      | record { ↘⟦T⟧ = ↘⟦T⟧₁ ; ↘⟦t⟧ = ↘⟦t⟧₁ ; T∈𝕌 = T∈𝕌₁ ; t∼⟦t⟧ = t∼⟦t⟧₁ }
                    rewrite ⟦⟧-det ↘⟦T⟧₁ ↘⟦T⟧ = record
                      { fa = _
                      ; ↘fa = Λ∙ ↘⟦t⟧₁
                      ; ®fa = ®El-one-sided _ _ (®El-resp-T≈ _ (®El-resp-≈ _ t∼⟦t⟧₁ t[σ∘τ,s]≈Λt[σ][τ]$s) ([]-q-∘-, ⊢T ⊢σ ⊢τ′ ⊢s))
                      }
              where
                open ER
                ⊢s = ®El⇒tm S∈𝕌 s®b
                ⊢σ∘τ = s-∘ ⊢τ′ ⊢σ
                ⊢s′ = conv ⊢s ([∘]-Se ⊢S ⊢σ ⊢τ′)
                ⊢s″ = conv ⊢s′ ([]-cong-Se‴ ⊢S (s-≈-sym (∘-I ⊢σ∘τ)))
                ⊢S[σ∘τ] = t[σ]-Se ⊢S ⊢σ∘τ
                ⊢T[qσ∘τ] = t[σ]-Se ⊢T (⊢q ⊢Δ′ ⊢σ∘τ ⊢S)
                σ∘τ∘I,s≈σ∘τ,s = ,-cong (∘-I ⊢σ∘τ) ⊢S (≈-refl ⊢S) (≈-refl ⊢s″)

                t[q[σ∘τ]][|s]≈Λt[σ][τ]$s : Δ′ ⊢ t [ q (S ↙ j) (σ ∘ τ) ] [| s ∶ S [ σ ∘ τ ] ↙ j ] ≈ (Λ (S ↙ j) t) [ σ ] [ τ ] $ s ∶[ k ] T [ q (S ↙ j) (σ ∘ τ) ] [| s ∶ S [ σ ∘ τ ] ↙ j ]
                t[q[σ∘τ]][|s]≈Λt[σ][τ]$s = begin
                    t [ q (S ↙ j) (σ ∘ τ) ] [| s ∶ S [ σ ∘ τ ] ↙ j ] ≈˘⟨ Λ-β ⊢S[σ∘τ] ⊢T[qσ∘τ] (t[σ] ⊢t (⊢q ⊢Δ′ ⊢σ∘τ ⊢S)) ⊢s′ ⟩
                    Λ (S [ σ ∘ τ ] ↙ j) (t [ q (S ↙ j) (σ ∘ τ) ]) $ s ≈˘⟨ $-cong ⊢S[σ∘τ] ⊢T[qσ∘τ] (≈-conv (Λ-[] ⊢σ∘τ ⊢S ⊢t refl) (Π-[] ⊢σ∘τ ⊢S ⊢T refl)) (≈-refl ⊢s′) refl ⟩
                    (Λ (S ↙ j) t [ σ ∘ τ ]) $ s ≈⟨ $-cong ⊢S[σ∘τ] ⊢T[qσ∘τ] (≈-conv ([∘] ⊢τ′ ⊢σ (Λ-I ⊢S ⊢t refl)) (Π-[] ⊢σ∘τ ⊢S ⊢T refl)) (≈-refl ⊢s′) refl ⟩
                    Λ (S ↙ j) t [ σ ] [ τ ] $ s
                  ∎

                t[σ∘τ,s]≈Λt[σ][τ]$s : Δ′ ⊢ t [ (σ ∘ τ) , s ∶ S ↙ j ] ≈ (Λ (S ↙ j) t) [ σ ] [ τ ] $ s ∶[ k ] T [ (σ ∘ τ) , s ∶ S ↙ j ]
                t[σ∘τ,s]≈Λt[σ][τ]$s =
                  begin
                      t [ (σ ∘ τ) , s ∶ S ↙ j ]              ≈˘⟨ ≈-conv ([]-cong (≈-refl ⊢t) σ∘τ∘I,s≈σ∘τ,s) ([]-cong-Se‴ ⊢T σ∘τ∘I,s≈σ∘τ,s) ⟩
                      t [ ((σ ∘ τ) ∘ I) , s ∶ S ↙ j  ]       ≈˘⟨ ≈-conv ([]-q-, ⊢σ∘τ ⊢S (s-I ⊢Δ′) (conv ⊢s′ (≈-sym ([I] (t[σ]-Se ⊢S ⊢σ∘τ)))) ⊢t) ([]-cong-Se‴ ⊢T σ∘τ∘I,s≈σ∘τ,s) ⟩
                      t [ q (S ↙ j) (σ ∘ τ) ] [| s ∶ S [ σ ∘ τ ] ↙ j ] ≈⟨ ≈-conv t[q[σ∘τ]][|s]≈Λt[σ][τ]$s (≈-sym ([]-q-∘-,′ ⊢T ⊢σ∘τ ⊢s′)) ⟩
                      (Λ (S ↙ j) t) [ σ ] [ τ ] $ s
                  ∎

Λ-E′ : ∀ {i j k} →
       i ≡ max j k →
       (S ↙ j) ∷ Γ ⊩ T ∶[ 1 + k ] Se k →
       Γ ⊩ r ∶[ i ] Π (S ↙ j) (T ↙ k) →
       Γ ⊩ s ∶[ j ] S →
       ---------------------
       Γ ⊩ r $ s ∶[ k ] T [| s ∶ S ↙ j ]
Λ-E′ {S} {_} {T} {r} {s} {i} {j} {k} refl ⊩T@record { ⊩Γ = ⊩SΓ@(⊩∷ {i = j} ⊩Γ ⊢S Skrip) ; krip = Tkrip } ⊩r ⊩s = record
  { ⊩Γ   = ⊩Γ
  ; krip = helper
  }
  where
    module r = _⊩_∶[_]_ ⊩r
    module s = _⊩_∶[_]_ ⊩s
    ⊢T = ⊩⇒⊢-tm ⊩T
    ⊢r = ⊩⇒⊢-tm ⊩r
    ⊢s = ⊩⇒⊢-tm ⊩s

    helper : Δ ⊢s σ ∶ ⊩Γ ® ρ → GluExp k Δ (r $ s) (T [| s ∶ S ↙ j ]) σ ρ
    helper {Δ} {σ} {ρ} σ®ρ
      with s®⇒⊢s ⊩Γ σ®ρ | s.krip (s®-irrel ⊩Γ s.⊩Γ σ®ρ) | r.krip (s®-irrel ⊩Γ r.⊩Γ σ®ρ)
    ...  | ⊢σ
          | record { ⟦T⟧ = ⟦S⟧ ; ⟦t⟧ = ⟦s⟧ ; ↘⟦T⟧ = ↘⟦S⟧ ; ↘⟦t⟧ = ↘⟦s⟧ ; T∈𝕌 = S∈𝕌 ; t∼⟦t⟧ = s∼⟦s⟧ }
          | record { ⟦T⟧ = .(Π _ _ (T ↙ _) ρ) ; ⟦t⟧ = ⟦r⟧ ; ↘⟦T⟧ = ⟦Π⟧ ↘⟦S⟧′ ; ↘⟦t⟧ = ↘⟦r⟧ ; T∈𝕌 = Π i≡′maxjk jA RT _ _ ; t∼⟦t⟧ = r∼⟦r⟧ }
        rewrite ⟦⟧-det ↘⟦S⟧′ ↘⟦S⟧
        with Skrip σ®ρ | s®-cons ⊩SΓ σ®ρ
    ...    | record { ↘⟦T⟧ = ↘⟦S⟧″ ; T∈𝕌 = S∈𝕌′ ; T∼⟦T⟧ = S∼⟦S⟧ } | cons
           rewrite ⟦⟧-det ↘⟦S⟧″ ↘⟦S⟧
           with Tkrip (cons (®El-≡ _ _ s∼⟦s⟧ refl))
    ...       | record { ⟦T⟧ = .(U k) ; ⟦t⟧ = ⟦t⟧ ; ↘⟦T⟧ = ⟦Se⟧ .k ; ↘⟦t⟧ = ↘⟦T⟧ ; T∈𝕌 = U 1+k≡1+k _ ; t∼⟦t⟧ = T∼⟦T⟧ }
              rewrite 𝕌-wf-gen j (ΠI≤′ j k i≡′maxjk)
                    | 𝕌-wf-gen k (ΠO≤′ j k i≡′maxjk)
                    | Glu-wf-gen j (ΠI≤′ j k i≡′maxjk)
                    | Glu-wf-gen k (ΠO≤′ j k i≡′maxjk)
                    | Glu-wellfounded-≡ (≤-reflexive (sym 1+k≡1+k)) = helper′

      where
        ⊢Δ = proj₁ (presup-s ⊢σ)
        module Λ where
          open GluΛ r∼⟦r⟧ public
          open ΛRel (krip (⊢wI ⊢Δ)) public

        module U = GluU T∼⟦T⟧

        s®a = ®El-≡ _ _ (®El-resp-T≈ _ s∼⟦s⟧ (®⇒≈ _ (®-≡ _ _ S∼⟦S⟧ refl) Λ.IT-rel)) refl
        a∈ = ®El⇒∈El jA s®a

        helper′ : GluExp k Δ (r $ s) (sub T (I , s ∶ S ↙ j)) σ ρ
        helper′
          with Λ.ap-rel s®a a∈
        ...  | record { fa = fa ; ↘fa = ↘fa ; ®fa = ®fa }
             with RT a∈
        ...     | record { ↘⟦T⟧ = ↘⟦T⟧′ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
                rewrite ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧
                      | ⟦⟧-det ↘⟦T′⟧ ↘⟦T⟧ = record
            { ⟦T⟧ = _
            ; ⟦t⟧ = _
            ; ↘⟦T⟧ = ⟦[]⟧ (⟦,⟧ ⟦I⟧ ↘⟦s⟧) ↘⟦T⟧
            ; ↘⟦t⟧ = ⟦$⟧ ↘⟦r⟧ ↘⟦s⟧ ↘fa
            ; T∈𝕌 = U.A∈𝕌
            ; t∼⟦t⟧ = ®El-≡ _ _ (®El-resp-T≈ _ (®El-resp-≈ _ ®fa r[σ]$s[σ]≈r$s[σ]) OT≈T) refl
            }

          where
            open ER

            T∼A : Δ ⊢ T [| s ∶ S ↙ j ] [ σ ] ®[ k ] U.A∈𝕌
            T∼A = ®-resp-≈ U.A∈𝕌 U.rel (≈-sym ([]-I,-∘ ⊢T ⊢σ ⊢s))

            IT≈S : Δ ⊢ S [ σ ] ≈ Λ.IT [ I ] ∶[ 1 + j ] Se j
            IT≈S = ®⇒≈ _ (®-≡ _ _ S∼⟦S⟧ refl) Λ.IT-rel

            OT≈T : Δ ⊢ Λ.OT [| s [ σ ] ∶ Λ.IT ↙ j ] ≈ T [| s ∶ S ↙ j ] [ σ ] ∶[ ℕ.suc k ] Se k
            OT≈T = ®⇒≈ _ (®-≡ _ _ (®El⇒® _ ®fa) refl) T∼A

            r[σ]$s[σ]≈r$s[σ] : Δ ⊢ r [ σ ] [ I ] $ s [ σ ] ≈ (r $ s) [ σ ] ∶[ k ] Λ.OT [| s [ σ ] ∶ Λ.IT ↙ j ]
            r[σ]$s[σ]≈r$s[σ] =
              begin
                r [ σ ] [ I ] $ s [ σ ] ≈⟨ $-cong Λ.⊢IT Λ.⊢OT ([I] (conv (t[σ] ⊢r ⊢σ) Λ.T≈)) (≈-refl (conv (t[σ] ⊢s ⊢σ) (≈-trans IT≈S ([I] Λ.⊢IT)))) refl ⟩
                r [ σ ] $ s [ σ ] ≈˘⟨ ≈-conv ($-[] ⊢S ⊢T ⊢σ ⊢r ⊢s refl) (≈-sym (≈-trans OT≈T ([]-I,-∘ ⊢T ⊢σ ⊢s))) ⟩
                (r $ s) [ σ ]
              ∎