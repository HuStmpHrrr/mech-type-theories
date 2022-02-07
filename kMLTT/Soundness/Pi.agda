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
Λ-I′ {Γ} {S} {t} {T} {i} ⊩S ⊩t
  with ⊩S | ⊩⇒⊢-tm ⊩S | ⊩t | ⊩⇒⊢-both ⊩t
...  | record { ⊩Γ = ⊩Γ ; lvl = lvl ; krip = Skrip }
     | ⊢S
     | record { ⊩Γ = (⊩∺ ⊩Γ₁ ⊢S₁ gS) ; lvl = lvl₁ ; krip = tkrip₁ }
     | ⊢T , ⊢t
    with fundamental-⊢t ⊢T
...    | ∺-cong ⊨Γ₁ Srel₁ , n₁ , Trel₁ = record { ⊩Γ = ⊩Γ ; krip = krip }
  where
    krip : ∀ {Δ σ ρ} →
           Δ ⊢s σ ∶ ⊩Γ ® ρ →
           GluExp (max lvl lvl₁) Δ (Λ t) (Π S T) σ ρ
    krip {Δ} {σ} {ρ} σ∼ρ
      with Skrip σ∼ρ | s®⇒⟦⟧ρ ⊩Γ σ∼ρ
    ...  | record { ⟦t⟧ = ⟦S⟧ ; ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦t⟧ = ↘⟦S⟧ ; T∈𝕌 = U i<lvl _ ; t∼⟦t⟧ = S∼⟦S⟧ }
         | ⊨Γ , ρ∈
          with S∼⟦S⟧
    ...      | record { t∶T = t∶S ; T≈ = S≈ ; A∈𝕌 = S∈𝕌 ; rel = S∼⟦S⟧ } = record
                                                                            { ↘⟦T⟧ = ⟦Π⟧ ↘⟦S⟧
                                                                            ; ↘⟦t⟧ = ⟦Λ⟧ _
                                                                            ; T∈𝕌 = Π (λ κ → 𝕌-mon κ S∈𝕌′) ΠRTT
                                                                            ; t∼⟦t⟧ = {!!}
                                                                            }
      where
        -- What a weird Agda bug...
        S∈𝕌′ = 𝕌-cumu (≤-trans (<⇒≤ i<lvl) (m≤m⊔n _ _)) S∈𝕌

        ΠRTT : {a a′ : D} (κ : UMoT) →
               a ≈ a′ ∈ El _ (𝕌-mon κ S∈𝕌′) →
               ΠRT T (ρ [ κ ] ↦ a) T (ρ [ κ ] ↦ a′) (𝕌 (max lvl lvl₁))
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
                      | ⟦⟧-det ↘⟦S⟧₁ (⟦⟧-mon κ ↘⟦S⟧) = {!El-one-sided (𝕌-mon κ S∈𝕌) S≈S′!} -- El-one-sided (𝕌-mon κ S∈𝕌) S≈S′ a≈a′

            helper : ΠRT T (ρ [ κ ] ↦ a) T (ρ [ κ ] ↦ a′) (𝕌 (max lvl lvl₁))
            helper = {!!}
            --   with Trel₁ (ρ[κ]≈ρ[κ]′₁ , a≈a′₁)
            -- ...  | record { ↘⟦T⟧ = ⟦Se⟧ _ ; ↘⟦T′⟧ = ⟦Se⟧ _ ; T≈T′ = U i<n₁ _ }
            --      , record { ↘⟦t⟧ = ↘⟦T⟧ ; ↘⟦t′⟧ = ↘⟦T′⟧ ; t≈t′ = T≈T′ }
            --     rewrite 𝕌-wellfounded-≡-𝕌 _ i<n₁ = record
            --                                        { ↘⟦T⟧ = ↘⟦T⟧
            --                                        ; ↘⟦T′⟧ = ↘⟦T′⟧
            --                                        ; T≈T′ = 𝕌-cumu (m≤n⊔m _ _) T≈T′
            --                                        }

            -- helper : ΠRT T (ρ [ κ ] ↦ a) T (ρ [ κ ] ↦ a′) (𝕌 n₁)
            -- helper
            --   with trel₁ (ρ[κ]≈ρ[κ]′₁ , a≈a′₁)
            -- ...  | rt
            --      , record { ⟦t⟧ = ⟦t⟧ ; ⟦t′⟧ = ⟦t′⟧ ; ↘⟦t⟧ = ↘⟦t⟧ ; ↘⟦t′⟧ = ↘⟦t′⟧ ; t≈t′ = t≈t′ } = record { RelTyp rt }

Λ-E′ : ∀ {i} →
       S ∺ Γ ⊩ T ∶ Se i →
       Γ ⊩ r ∶ Π S T →
       Γ ⊩ s ∶ S →
       ---------------------
       Γ ⊩ r $ s ∶ T [| s ]
Λ-E′ {S} {_} {T} {r} {s} {i} ⊩T@record { ⊩Γ = ⊩SΓ@(⊩∺ {i = j} ⊩Γ ⊢S Skrip) ; lvl = _ ; krip = Tkrip } ⊩r ⊩s = record
  { ⊩Γ   = ⊩Γ
  ; lvl  = i
  ; krip = {!!}
  }
  where module r = _⊩_∶_ ⊩r
        module s = _⊩_∶_ ⊩s
        ⊢T = ⊩⇒⊢-tm ⊩T
        ⊢r = ⊩⇒⊢-tm ⊩r
        ⊢s = ⊩⇒⊢-tm ⊩s

        helper : Δ ⊢s σ ∶ ⊩Γ ® ρ → GluExp i Δ (r $ s) (T [| s ]) σ ρ
        helper {Δ} {σ} {ρ} σ∼ρ
          with s®⇒⊢s ⊩Γ σ∼ρ | s.krip (s®-irrel ⊩Γ s.⊩Γ σ∼ρ) | r.krip (s®-irrel ⊩Γ r.⊩Γ σ∼ρ)
        ...  | ⊢σ
             | record { ⟦T⟧ = ⟦S⟧ ; ⟦t⟧ = ⟦s⟧ ; ↘⟦T⟧ = ↘⟦S⟧ ; ↘⟦t⟧ = ↘⟦s⟧ ; T∈𝕌 = S∈𝕌 ; t∼⟦t⟧ = s∼⟦s⟧ }
             | record { ⟦T⟧ = .(Π _ T ρ) ; ⟦t⟧ = ⟦r⟧ ; ↘⟦T⟧ = ⟦Π⟧ ↘⟦S⟧′ ; ↘⟦t⟧ = ↘⟦r⟧ ; T∈𝕌 = Π iA RT ; t∼⟦t⟧ = r∼⟦r⟧ }
             rewrite ⟦⟧-det ↘⟦S⟧′ ↘⟦S⟧
             with Skrip σ∼ρ | s®-cons ⊩SΓ σ∼ρ
        ...     | record { ↘⟦T⟧ = ↘⟦S⟧″ ; T∈𝕌 = S∈𝕌′ ; T∼⟦T⟧ = S∼⟦S⟧ } | cons
                rewrite ⟦⟧-det ↘⟦S⟧″ ↘⟦S⟧
                with Tkrip (cons (®El-irrel S∈𝕌 S∈𝕌′ S∼⟦S⟧ s∼⟦s⟧))
        ...        | record { ⟦t⟧ = ⟦T⟧ ; ↘⟦T⟧ = ⟦Se⟧ .i ; ↘⟦t⟧ = ↘⟦T⟧ ; T∈𝕌 = U i< _ ; t∼⟦t⟧ = T∼⟦T⟧ }
                   rewrite Glu-wellfounded-≡ i< = {!!}
          where ⊢Δ = proj₁ (presup-s ⊢σ)
                module Λ where
                  open GluΛ r∼⟦r⟧ public
                  open ΛRel (krip (⊢rI ⊢Δ)) public

                  ⊢IT : Δ ⊢ IT ∶ Se _
                  ⊢IT = ®Π-wf iA RT (®El⇒® (Π iA RT) r∼⟦r⟧)

                module U = GluU T∼⟦T⟧

                pair : Δ ⊢ S [ σ ] ≈ Λ.IT [ I ] ∶ Se (max j r.lvl) × Δ ⊢ s [ σ ] ∶ Λ.IT [ I ] ®[ r.lvl ] ⟦s⟧ ∈El (iA vone)
                pair
                  with iA vone | Λ.IT-rel
                ...  | R | IT-rel
                     rewrite D-ap-vone ⟦S⟧ = eq
                                           , ®El-master S∈𝕌 R Rcumu IT-rel s∼⟦s⟧ eq
                  where Rcumu = 𝕌-cumu (m≤n⊔m j r.lvl) R
                        eq    = ®⇒≈ Rcumu
                                    (®-one-sided (𝕌-cumu (m≤m⊔n j r.lvl) S∈𝕌′) Rcumu (®-cumu S∈𝕌′ S∼⟦S⟧ (m≤m⊔n j r.lvl)))
                                    (®-cumu R IT-rel (m≤n⊔m j r.lvl))

                eq₁ : Δ ⊢ S [ σ ] ≈ Λ.IT [ I ] ∶ Se (max j r.lvl)
                eq₁ = proj₁ pair
                s∼a : Δ ⊢ s [ σ ] ∶ Λ.IT [ I ] ®[ r.lvl ] ⟦s⟧ ∈El (iA vone)
                s∼a = proj₂ pair

                a∈ : ⟦s⟧ ∈′ El r.lvl (iA vone)
                a∈ = ®El⇒∈El (iA vone) s∼a

                help : GluExp i Δ (r $ s) (T [| s ]) σ ρ
                help
                  with Λ.ap-rel s∼a a∈
                ...  | record { fa = fa ; ↘fa = ↘fa ; ®fa = ®fa }
                     rewrite D-ap-vone ⟦r⟧
                     with RT vone a∈
                ...     | record { ↘⟦T⟧ = ↘⟦T⟧′ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
                        rewrite ρ-ap-vone ρ
                              | ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧
                              | ⟦⟧-det ↘⟦T′⟧ ↘⟦T⟧ = record
                  { ⟦T⟧   = ⟦T⟧
                  ; ⟦t⟧   = fa
                  ; ↘⟦T⟧  = ⟦[]⟧ (⟦,⟧ ⟦I⟧ ↘⟦s⟧) ↘⟦T⟧
                  ; ↘⟦t⟧  = ⟦$⟧ ↘⟦r⟧ ↘⟦s⟧ ↘fa
                  ; T∈𝕌   = U.A∈𝕌
                  ; t∼⟦t⟧ = ®El-master T≈T′ U.A∈𝕌 A∈k T∼A (®El-resp-≈ T≈T′ ®fa eq₃) eq₂
                  }
                    where open ER
                          T∼A : Δ ⊢ T [| s ] [ σ ] ®[ i ] U.A∈𝕌
                          T∼A = ®-resp-≈ U.A∈𝕌 U.rel (≈-sym ([]-I,-∘ ⊢T ⊢σ ⊢s))

                          k   = max i r.lvl
                          i≤k = m≤m⊔n i r.lvl
                          l≤k = m≤n⊔m i r.lvl
                          A∈k = 𝕌-cumu i≤k U.A∈𝕌

                          eq₂ : Δ ⊢ Λ.OT [ I , s [ σ ] ] ≈ T [| s ] [ σ ] ∶ Se _
                          eq₂ = ®⇒≈ A∈k (®-one-sided (𝕌-cumu l≤k T≈T′) A∈k (®-cumu T≈T′ (®El⇒® T≈T′ ®fa) l≤k)) (®-cumu U.A∈𝕌 T∼A i≤k)

                          eq₃ : Δ ⊢ r [ σ ] [ I ] $ s [ σ ] ≈ (r $ s) [ σ ] ∶ Λ.OT [| s [ σ ] ]
                          eq₃ = begin
                            r [ σ ] [ I ] $ s [ σ ] ≈⟨ $-cong ([I] (conv (t[σ] ⊢r ⊢σ) Λ.T≈)) (≈-refl (conv (t[σ] ⊢s ⊢σ) (≈-sym ([I]-≈ˡ-Se (≈-sym eq₁))))) ⟩
                            r [ σ ] $ s [ σ ]       ≈˘⟨ ≈-conv ($-[] ⊢σ ⊢r ⊢s) (≈-sym (≈-trans eq₂ ([]-I,-∘ (lift-⊢-Se-max ⊢T) ⊢σ ⊢s))) ⟩
                            (r $ s) [ σ ]           ∎
