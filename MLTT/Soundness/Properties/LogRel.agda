{-# OPTIONS --without-K --safe #-}

open import Level hiding (_⊔_)
open import Axiom.Extensionality.Propositional

-- Properties of the gluing models for terms and types
module MLTT.Soundness.Properties.LogRel (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Lib
open import Data.Nat
open import Data.Nat.Properties as ℕₚ

open import MLTT.Statics.Properties
open import MLTT.Semantics.Readback
open import MLTT.Semantics.Properties.PER fext
open import MLTT.Soundness.LogRel

open import MLTT.Soundness.Properties.NoFunExt.LogRel public


-- The gluing model for natural numbers is monotonic w.r.t. restricted weakening.
®Nat-mon : Γ ⊢ t ∶N® a ∈Nat → Δ ⊢w σ ∶ Γ → Δ ⊢ t [ σ ] ∶N® a ∈Nat
®Nat-mon (ze t≈) ⊢σ                             = ze (≈-trans ([]-cong-N′ t≈ (⊢w⇒⊢s ⊢σ)) (ze-[] (⊢w⇒⊢s ⊢σ)))
®Nat-mon (su t≈ t∼a) ⊢σ                         = su (≈-trans ([]-cong-N′ t≈ ⊢σ′) (su-[] ⊢σ′ (®Nat⇒∶Nat t∼a (proj₂ (presup-s ⊢σ′))))) (®Nat-mon t∼a ⊢σ)
  where ⊢σ′ = ⊢w⇒⊢s ⊢σ
®Nat-mon {_} {t} {_} {Δ} {σ} (ne {c} c∈ rel) ⊢σ = ne c∈ helper
  where helper : Δ′ ⊢w τ ∶ Δ → Δ′ ⊢ t [ σ ] [ τ ] ≈ Ne⇒Exp (proj₁ (c∈ (len Δ′))) ∶ N
        helper {Δ′} {τ} ⊢τ
          with c∈ (len Δ′) | c∈ (len Δ′) | rel (⊢w-∘ ⊢σ ⊢τ)
        ...  | u , ↘u , _ | u′ , ↘u′ , _ | tστ≈
             rewrite Re-det ↘u ↘u′ = ≈-trans ([∘]-N (®Nat⇒∶Nat (ne c∈ rel) (proj₂ (presup-s (⊢w⇒⊢s ⊢σ)))) (⊢w⇒⊢s ⊢σ) (⊢w⇒⊢s ⊢τ)) tστ≈


-- Helpers to get rid of the knot
Glu-wellfounded-≡′ : ∀ {i i′ j} (j<i : j < i) (j<i′ : j < i′) → (λ {A B} → Glu-wellfounded i j<i {A} {B}) ≡ Glu-wellfounded i′ j<i′
Glu-wellfounded-≡′ (s≤s j<i) (s≤s j′<i) = cong (Glu._⊢_®_ _) (implicit-extensionality fext
                                                             λ {j′} → fext λ j′<j → Glu-wellfounded-≡′ (≤-trans j′<j j<i) (≤-trans j′<j j′<i))

Glu-wellfounded-≡ : ∀ {i j} (j<i : j < i) → (λ {A B} → Glu-wellfounded i j<i {A} {B}) ≡ _⊢_®[ j ]_
Glu-wellfounded-≡ (s≤s j<i) = cong (Glu._⊢_®_ _) (implicit-extensionality fext λ {j′} → fext (λ j′<j → Glu-wellfounded-≡′ (≤-trans j′<j j<i) j′<j))

-- If t and a are related, then t is well-typed.
®El⇒tm : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
           Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
           ---------------------------
           Γ ⊢ t ∶ T
®El⇒tm (ne C≈C′) (ne _ , glu) = GluNe.t∶T glu
®El⇒tm N (t∼a , T≈N)          = conv (®Nat⇒∶Nat t∼a (proj₁ (presup-≈ T≈N))) (≈-sym T≈N)
®El⇒tm (U j<i eq) t∼a         = GluU.t∶T t∼a
®El⇒tm (Π iA RT) t∼a          = GluΛ.t∶T t∼a


-- If t and a are related, then a is in the El PER model.
®El⇒∈El : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
          Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
          -----------------------------
          a ∈′ El i A≈B
®El⇒∈El (ne C≈C′) (a∈⊥ , _)       = a∈⊥
®El⇒∈El N (t∼a , _)               = ®Nat⇒∈Nat t∼a
®El⇒∈El (U j<i eq) t∼a
  rewrite 𝕌-wellfounded-≡-𝕌 _ j<i = GluU.A∈𝕌 t∼a
®El⇒∈El (Π iA RT) t∼a             = GluΛ.a∈El t∼a

-- If t and a are related, then their types are also related.
®El⇒® : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
        Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
        ----------------------------
        Γ ⊢ T ®[ i ] A≈B
®El⇒® (ne C≈C′) (ne c∈ , glu) = ⊢T , λ ⊢σ → proj₁ (krip ⊢σ)
  where open GluNe glu
®El⇒® N (_ , T≈N)             = T≈N
®El⇒® (U j<i eq) t∼a          = GluU.T≈ t∼a
®El⇒® (Π iA RT) t∼a           = record
  { IT   = IT
  ; OT   = OT
  ; ⊢OT  = ⊢OT
  ; T≈   = T≈
  ; krip = λ {_} {σ} ⊢σ →
    let open ΛRel (krip ⊢σ)
    in record
    { IT-rel = IT-rel
    ; OT-rel = λ s∼a a∈ →
      let open ΛKripke (ap-rel s∼a a∈)
      in ®El⇒® (ΠRT.T≈T′ (RT a∈)) ®fa
    }
  }
  where open GluΛ t∼a


-- If t and a are related, then the type of t is well-formed.
®El⇒ty : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
           Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
           ---------------------------
           Γ ⊢ T ∶ Se i
®El⇒ty A≈B t∼a = ®⇒ty A≈B (®El⇒® A≈B t∼a)


-- ®El respects term equivalence.
®El-resp-≈ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
             Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
             Γ ⊢ t ≈ t′ ∶ T →
             ----------------------------
             Γ ⊢ t′ ∶ T ®[ i ] a ∈El A≈B
®El-resp-≈ (ne C≈C′) (ne c∈ , glu) t≈t′ = ne c∈ , record
  { t∶T  = proj₁ (proj₂ (proj₂ (presup-≈ t≈t′)))
  ; ⊢T   = ⊢T
  ; krip = λ ⊢σ → proj₁ (krip ⊢σ) , ≈-trans ([]-cong (≈-sym t≈t′) (s-≈-refl (⊢w⇒⊢s ⊢σ))) (proj₂ (krip ⊢σ))
  }
  where open GluNe glu
®El-resp-≈ N (t∼a , T≈N) t≈t′           = ®Nat-resp-≈ t∼a (≈-conv t≈t′ T≈N) , T≈N
®El-resp-≈ (U j<i eq) t∼a t≈t′
  rewrite Glu-wellfounded-≡ j<i         = record
  { t∶T = proj₁ (proj₂ (proj₂ (presup-≈ t≈t′)))
  ; T≈  = T≈
  ; A∈𝕌 = A∈𝕌
  ; rel = ®-resp-≈ A∈𝕌 rel (≈-conv t≈t′ T≈)
  }
  where open GluU t∼a
®El-resp-≈ {i = i} (Π iA RT) t∼a t≈t′   = record
  { t∶T  = proj₁ (proj₂ (proj₂ (presup-≈ t≈t′)))
  ; a∈El = a∈El
  ; IT   = IT
  ; OT   = OT
  ; ⊢OT  = ⊢OT
  ; T≈   = T≈
  ; krip = λ {Δ} {σ} ⊢σ →
    let open ΛRel (krip ⊢σ)
    in record
    { IT-rel = IT-rel
    ; ap-rel = λ s∼b b∈ →
      let open ΛKripke (ap-rel s∼b b∈)
          ⊢σ′     = ⊢w⇒⊢s ⊢σ
          ⊢s      = ®El⇒tm _ s∼b
          ⊢Π      = proj₁ (proj₂ (proj₂ (presup-≈ T≈)))
          j , ⊢IT = inv-Π-wf′ ⊢Π
          k , ⊢OT = inv-Π-wf ⊢Π
      in record
      { fa  = fa
      ; ↘fa = ↘fa
      ; ®fa = ®El-resp-≈ (ΠRT.T≈T′ (RT b∈)) ®fa
                         (≈-conv ($-cong (≈-conv ([]-cong t≈t′ (s-≈-refl ⊢σ′))
                                                 (≈-trans ([]-cong-Se′ (lift-⊢≈-Se-max T≈) ⊢σ′)
                                                          (lift-⊢≈-Se-max′ {i = j ⊔ k} {i} (Π-[] ⊢σ′ (lift-⊢-Se-max ⊢IT) (lift-⊢-Se-max′ ⊢OT)))))
                                         (≈-refl ⊢s))
                                 (≈-trans ([∘]-Se ⊢OT (⊢q ⊢σ′ ⊢IT) (⊢I,t ⊢s))
                                          ([]-cong-Se″ ⊢OT (qI,≈, ⊢σ′ ⊢IT ⊢s))))
      }
    }
  }
  where open GluΛ t∼a


-- ®El respects context stack equivalence.
®El-resp-⊢≈ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
              Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
              ⊢ Γ ≈ Δ →
              ---------------------------
              Δ ⊢ t ∶ T ®[ i ] a ∈El A≈B
®El-resp-⊢≈ (ne C≈C′) (ne c∈⊥ , rel) Γ≈Δ = ne c∈⊥ , record
  { t∶T  = ctxeq-tm Γ≈Δ t∶T
  ; ⊢T   = ctxeq-tm Γ≈Δ ⊢T
  ; krip = λ ⊢σ → krip (⊢w-resp-⊢≈ʳ ⊢σ (⊢≈-sym Γ≈Δ))
  }
  where open GluNe rel
®El-resp-⊢≈ N (t∼a , T≈N) Γ≈Δ            = ®Nat-resp-⊢≈ t∼a Γ≈Δ , ctxeq-≈ Γ≈Δ T≈N
®El-resp-⊢≈ (U j<i eq) t∼a Γ≈Δ
  rewrite Glu-wellfounded-≡ j<i          = record
  { t∶T = ctxeq-tm Γ≈Δ t∶T
  ; T≈  = ctxeq-≈ Γ≈Δ T≈
  ; A∈𝕌 = A∈𝕌
  ; rel = ®-resp-⊢≈ A∈𝕌 rel Γ≈Δ
  }
  where open GluU t∼a
®El-resp-⊢≈ (Π iA RT) t∼a Γ≈Δ            = record
  { t∶T  = ctxeq-tm Γ≈Δ t∶T
  ; a∈El = a∈El
  ; IT   = IT
  ; OT   = OT
  ; ⊢OT  = ctxeq-tm (∷-cong Γ≈Δ (≈-refl (®Π-wf iA RT (®El⇒® (Π iA RT) t∼a)))) ⊢OT
  ; T≈   = ctxeq-≈ Γ≈Δ T≈
  ; krip = λ ⊢σ → krip (⊢w-resp-⊢≈ʳ ⊢σ (⊢≈-sym Γ≈Δ))
  }
  where open GluΛ t∼a


-- Symmetry of the witness of 𝕌 i
mutual
  ®-swap : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i)
           (B≈A : B ≈ A ∈ 𝕌 i) →
           Γ ⊢ T ®[ i ] A≈B →
           -----------------------
           Γ ⊢ T ®[ i ] B≈A
  ®-swap {_} {_} {Γ} {T} (ne C≈C′)  (ne C′≈C) (⊢T , rel) = ⊢T , helper
    where
      helper : Δ ⊢w σ ∶ Γ →
               -----------------------------------
               Δ ⊢ T [ σ ] ≈ Ne⇒Exp (proj₁ (C′≈C (len Δ))) ∶ Se _
      helper {Δ} {σ} ⊢σ
        with C≈C′ (len Δ) | C′≈C (len Δ) | rel ⊢σ
      ...  | _ , ↘u , _ | _ , _ , ↘u₁ | Tσ≈
           rewrite Re-det ↘u ↘u₁ = Tσ≈
  ®-swap                 N          N           T∼A        = T∼A
  ®-swap                 (U _ refl) (U _ _)     T∼A        = T∼A
  ®-swap {_} {_} {Γ}     (Π iA RT)  (Π iA′ RT′) T∼A        = record
                                                             { GluΠ T∼A
                                                             ; krip = krip′
                                                             }
    where
      open GluΠ T∼A

      krip′ : ∀ {Δ σ} →
              Δ ⊢w σ ∶ Γ →
              ------------------------------------
              ΠRel _ Δ IT OT σ iA′
                (_⊢_®[ _ ] iA′)
                (λ a∈ → _⊢_®[ _ ] ΠRT.T≈T′ (RT′ a∈))
                (_⊢_∶_®[ _ ]_∈El iA′)
      krip′ {Δ} {σ} ⊢σ = record
                         { IT-rel = ®-swap (iA) (iA′) IT-rel
                         ; OT-rel = OT-rel′
                         }
        where
          open ΠRel (krip ⊢σ)

          OT-rel′ : ∀ {s b} →
                   Δ ⊢ s ∶ IT [ σ ] ®[ _ ] b ∈El iA′ →
                   (b∈ : b ∈′ El _ iA′) →
                   -----------------------------------------------
                   Δ ⊢ OT [ σ , s ] ®[ _ ] ΠRT.T≈T′ (RT′ b∈)
          OT-rel′ s∼b b∈
            with El-sym iA′ iA b∈
          ...  | b∈′
              with RT b∈′ | RT′ b∈ | OT-rel (®El-swap iA′ iA s∼b) b∈′
          ...    | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
                 | record { ↘⟦T⟧ = ↘⟦T′⟧₁ ; ↘⟦T′⟧ = ↘⟦T⟧₁ ; T≈T′ = T′≈T }
                 | R
                rewrite ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₁
                      | ⟦⟧-det ↘⟦T′⟧ ↘⟦T′⟧₁ = ®-swap T≈T′ T′≈T R

  ®El-swap : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i)
             (B≈A : B ≈ A ∈ 𝕌 i) →
             Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
             ----------------------------
             Γ ⊢ t ∶ T ®[ i ] a ∈El B≈A
  ®El-swap {_} {_} {Γ} {t} {T}     (ne C≈C′)    (ne C′≈C)   (ne c∈ , glu) = ne c∈
                                                                          , record
                                                                            { GluNe glu
                                                                            ; krip = krip′
                                                                            }
    where
      open GluNe glu

      krip′ : Δ ⊢w σ ∶ Γ →
              ----------------------------------------
              Δ ⊢ T [ σ ] ≈ Ne⇒Exp (proj₁ (C′≈C (len Δ))) ∶ Se _
            × Δ ⊢ t [ σ ] ≈ Ne⇒Exp (proj₁ (c∈ (len Δ))) ∶ T [ σ ]
      krip′ {Δ} {σ} ⊢σ
        with C≈C′ (len Δ) | C′≈C (len Δ) | krip ⊢σ
      ...  | _ , ↘u , _ | _ , _ , ↘u₁ | Tσ≈ , tσ≈
           rewrite Re-det ↘u ↘u₁ = Tσ≈ , tσ≈
  ®El-swap                         N            N           t∼a          = t∼a
  ®El-swap                         (U j<i refl) (U j<i₁ _)  t∼a          = record
                                                                           { GluU (t∼a)
                                                                           ; rel = subst (λ f -> f _ _ A∈𝕌) (Glu-wellfounded-≡′ j<i j<i₁) rel
                                                                           }
    where
      open GluU (t∼a)
  ®El-swap {_} {_} {Γ} {t} {_} {a} (Π iA RT)    (Π iA′ RT′) t∼a          = record
                                                                           { GluΛ t∼a
                                                                           ; a∈El = El-sym (Π iA RT) (Π iA′ RT′) a∈El
                                                                           ; krip = krip′
                                                                           }
    where
      open GluΛ t∼a

      krip′ : ∀ {Δ σ} →
              Δ ⊢w σ ∶ Γ →
              ------------------------------------
              ΛRel _ Δ t IT OT σ a iA′
                (_⊢_®[ _ ] iA′)
                (_⊢_∶_®[ _ ]_∈El iA′)
                (λ b∈ → _⊢_∶_®[ _ ]_∈El ΠRT.T≈T′ (RT′ b∈))
      krip′ {Δ} {σ} ⊢σ = record
                         { IT-rel = ®-swap iA iA′ IT-rel
                         ; ap-rel = ap-rel′
                         }
        where
          open ΛRel (krip ⊢σ)

          ap-rel′ : ∀ {s b} →
                   Δ ⊢ s ∶ IT [ σ ] ®[ _ ] b ∈El iA′ →
                   (b∈ : b ∈′ El _ iA′) →
                   -----------------------------------------------
                   ΛKripke Δ (t [ σ ] $ s) (OT [ σ , s ]) a b (_⊢_∶_®[ _ ]_∈El ΠRT.T≈T′ (RT′ b∈))
          ap-rel′ s∼b b∈
            with El-sym iA′ iA b∈
          ...  | b∈′
              with RT b∈′ | RT′ b∈ | ap-rel (®El-swap iA′ iA s∼b) b∈′
          ...    | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
                 | record { ↘⟦T⟧ = ↘⟦T′⟧₁ ; ↘⟦T′⟧ = ↘⟦T⟧₁ ; T≈T′ = T′≈T }
                 | R
                rewrite ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₁
                      | ⟦⟧-det ↘⟦T′⟧ ↘⟦T′⟧₁ = record
                                              { Λkrip
                                              ; ®fa = ®El-swap T≈T′ T′≈T ®fa
                                              }
           where
             open module Λkrip = ΛKripke R


-- The witnesses in the gluing model for types and terms are irrelevant.
mutual

  ®-one-sided : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i)
                  (A≈B′ : A ≈ B′ ∈ 𝕌 i) →
                  Γ ⊢ T ®[ i ] A≈B →
                  -----------------------
                  Γ ⊢ T ®[ i ] A≈B′
  ®-one-sided {Γ = Γ} {T} {i} (ne C≈C′) (ne C≈C″) (⊢T , rel) = ⊢T , helper
    where helper : Δ ⊢w σ ∶ Γ → Δ ⊢ T [ σ ] ≈ Ne⇒Exp (proj₁ (C≈C″ (len Δ))) ∶ Se i
          helper {Δ} {σ} ⊢σ
            with C≈C′ (len Δ) | C≈C″ (len Δ) | rel ⊢σ
          ...  | u , ↘u , _ | u′ , ↘u′ , _ | Tσ≈
               rewrite Re-det ↘u ↘u′ = Tσ≈
  ®-one-sided N N T∼A                                        = T∼A
  ®-one-sided (U j<i eq) (U j′<i eq′) T∼A                    = T∼A
  ®-one-sided {Γ = Γ} {_} {i} (Π iA RT) (Π iA′ RT′) T∼A      = record
    { IT   = IT
    ; OT   = OT
    ; ⊢OT  = ⊢OT
    ; T≈   = T≈
    ; krip = λ {_} {σ} ⊢σ →
      let open ΠRel (krip ⊢σ)
      in record
      { IT-rel = ®-one-sided iA iA′ IT-rel
      ; OT-rel = helper ⊢σ
      }
    }
    where open GluΠ T∼A
          helper : Δ ⊢w σ ∶ Γ → Δ ⊢ s ∶ IT [ σ ] ®[ i ] a ∈El iA′ → (a∈ : a ∈′ El i iA′) → Δ ⊢ OT [ σ , s ] ®[ i ] (ΠRT.T≈T′ (RT′ a∈))
          helper {Δ} {σ} ⊢σ s∼a a∈
            with krip ⊢σ | El-one-sided iA′ iA a∈
          ...  | record { OT-rel = OT-rel } | a∈′
               with RT a∈′ | RT′ a∈ | OT-rel (®El-one-sided iA′ iA s∼a) a∈′
          ...     | record { ⟦T⟧ = ⟦T⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; T≈T′ = T≈T′ }
                  | record { ↘⟦T⟧ = ↘⟦T⟧′ ; T≈T′ = T≈T′₁ }
                  | OT∼
              rewrite ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧ = ®-one-sided T≈T′ T≈T′₁ OT∼

  ®El-one-sided : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i)
                  (A≈B′ : A ≈ B′ ∈ 𝕌 i) →
                  Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
                  ----------------------------
                  Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B′
  ®El-one-sided {Γ = Γ} {t} {T} {_} {i} (ne C≈C′) (ne C≈C″) (ne c∈ , glu) = ne c∈ , record
    { t∶T  = t∶T
    ; ⊢T   = ⊢T
    ; krip = helper
    }
    where open GluNe glu
          helper : Δ ⊢w σ ∶ Γ → Δ ⊢ T [ σ ] ≈ Ne⇒Exp (proj₁ (C≈C″ (len Δ))) ∶ Se i × Δ ⊢ t [ σ ] ≈ Ne⇒Exp (proj₁ (c∈ (len Δ))) ∶ T [ σ ]
          helper {Δ} {σ} ⊢σ
            with C≈C′ (len Δ) | C≈C″ (len Δ) | krip ⊢σ
          ...  | u , ↘u , _ | u′ , ↘u′ , _ | Tσ≈ , tσ≈
               rewrite Re-det ↘u ↘u′ = Tσ≈ , tσ≈
  ®El-one-sided N N t∼a                                                   = t∼a
  ®El-one-sided (U j<i eq) (U j′<i eq′) t∼a -- ((A∈ , T∼A) , T≈)
    rewrite Glu-wellfounded-≡ j<i
          | Glu-wellfounded-≡ j′<i                                        = record
    { t∶T = t∶T
    ; T≈  = T≈
    ; A∈𝕌 = A∈𝕌
    ; rel = rel
    }
    where open GluU t∼a
  ®El-one-sided {Γ = Γ} {t} {_} {f} {i} (Π iA RT) (Π iA′ RT′) t∼a         = record
    { t∶T  = t∶T
    ; a∈El = El-one-sided (Π iA RT) (Π iA′ RT′) a∈El
    ; IT   = IT
    ; OT   = OT
    ; ⊢OT  = ⊢OT
    ; T≈   = T≈
    ; krip = λ {_} {σ} ⊢σ →
      let open ΛRel (krip ⊢σ)
      in record
      { IT-rel = ®-one-sided iA iA′ IT-rel
      ; ap-rel = λ s∼b b∈ →
        let fa , ↘fa , ®fa = helper ⊢σ s∼b b∈
        in record
        { fa  = fa
        ; ↘fa = ↘fa
        ; ®fa = ®fa
        }
      }
    }
    where open GluΛ t∼a
          helper : Δ ⊢w σ ∶ Γ → Δ ⊢ s ∶ IT [ σ ] ®[ i ] a ∈El iA′ → (a∈ : a ∈′ El i iA′) →
                   ∃ λ fa → f ∙ a ↘ fa × Δ ⊢ t [ σ ] $ s ∶ OT [ σ , s ] ®[ i ] fa ∈El (ΠRT.T≈T′ (RT′ a∈))
          helper {Δ} {σ} ⊢σ s∼a a∈
            with krip ⊢σ | El-one-sided iA′ iA a∈
          ...  | record { ap-rel = ap-rel } | a∈′
               with RT a∈′ | RT′ a∈ | ap-rel (®El-one-sided iA′ iA s∼a) a∈′
          ...     | record { ⟦T⟧ = ⟦T⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; T≈T′ = T≈T′ }
                  | record { ↘⟦T⟧ = ↘⟦T⟧′ ; T≈T′ = T≈T′₁ }
                  | R
              rewrite ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧ = fa , ↘fa , ®El-one-sided T≈T′ T≈T′₁ ®fa
            where open ΛKripke R

®-one-sided′ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i)
               (A′≈B : A′ ≈ B ∈ 𝕌 i) →
               Γ ⊢ T ®[ i ] A≈B →
               ----------------------------
               Γ ⊢ T ®[ i ] A′≈B
®-one-sided′ A≈B A′≈B t∼a = ®-swap (𝕌-sym A′≈B) A′≈B (®-one-sided (𝕌-sym A≈B) (𝕌-sym A′≈B) (®-swap A≈B (𝕌-sym A≈B) t∼a))

®El-one-sided′ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i)
                 (A′≈B : A′ ≈ B ∈ 𝕌 i) →
                 Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
                 ----------------------------
                 Γ ⊢ t ∶ T ®[ i ] a ∈El A′≈B
®El-one-sided′ A≈B A′≈B t∼a = ®El-swap (𝕌-sym A′≈B) A′≈B (®El-one-sided (𝕌-sym A≈B) (𝕌-sym A′≈B) (®El-swap A≈B (𝕌-sym A≈B) t∼a))

-- The gluing model for types respect PER equivalence.
®-transport : ∀ {i} (A≈A′ : A ≈ A′ ∈ 𝕌 i)
              (B≈B′ : B ≈ B′ ∈ 𝕌 i) →
              A ≈ B ∈ 𝕌 i →
              Γ ⊢ T ®[ i ] A≈A′ →
              ----------------------------
              Γ ⊢ T ®[ i ] B≈B′
®-transport A≈A′ B≈B′ A≈B t∼a = ®-one-sided B≈A B≈B′ (®-swap A≈B B≈A (®-one-sided A≈A′ A≈B t∼a))
  where B≈A = 𝕌-sym A≈B

-- The gluing model for terms respect PER equivalence.
®El-transport : ∀ {i} (A≈A′ : A ≈ A′ ∈ 𝕌 i)
                 (B≈B′ : B ≈ B′ ∈ 𝕌 i) →
                 A ≈ B ∈ 𝕌 i →
                 Γ ⊢ t ∶ T ®[ i ] a ∈El A≈A′ →
                 ----------------------------
                 Γ ⊢ t ∶ T ®[ i ] a ∈El B≈B′
®El-transport A≈A′ B≈B′ A≈B t∼a = ®El-one-sided B≈A B≈B′ (®El-swap A≈B B≈A (®El-one-sided A≈A′ A≈B t∼a))
  where B≈A = 𝕌-sym A≈B

®-≡ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) (A′≈B′ : A′ ≈ B′ ∈ 𝕌 i) → Γ ⊢ T ®[ i ] A≈B → A ≡ A′ → Γ ⊢ T ®[ i ] A′≈B′
®-≡ A≈B A′≈B′ T∼A refl = ®-one-sided A≈B A′≈B′ T∼A

®El-≡ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) (A′≈B′ : A′ ≈ B′ ∈ 𝕌 i) → Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B → A ≡ A′ → Γ ⊢ t ∶ T ®[ i ] a ∈El A′≈B′
®El-≡ A≈B A′≈B′ t∼a refl = ®El-one-sided A≈B A′≈B′ t∼a

private
  IT-mon-helper : ∀ {i} (iA : A ≈ B ∈ 𝕌 i)
                   (RT : ∀ {a a′} →
                         a ≈ a′ ∈ El i iA →
                         ΠRT T′ (ρ ↦ a) T″ (ρ′ ↦ a′) (𝕌 i))
                   (iA′ : A ≈ B ∈ 𝕌 i)
                   (RT′ : ∀ {a a′} →
                          a ≈ a′ ∈ El i iA′ →
                          ΠRT T′ (ρ ↦ a) T″ (ρ′ ↦ a′) (𝕌 i)) →
                  Γ ⊢ T ∶ Se i →
                  Δ ⊢w σ ∶ Γ →
                  Δ′ ⊢w τ ∶ Δ →
                  Δ′ ⊢ T [ σ ∘ τ ] ®[ i ] iA  →
                  Δ′ ⊢ T [ σ ] [ τ ] ®[ i ] iA′
  IT-mon-helper {σ = σ} {Δ′ = Δ′} {τ} iA RT iA′ RT′ ⊢T ⊢σ ⊢τ T∼A = ®-one-sided iA iA′
                                                                               (®-resp-≈ iA T∼A (≈-sym ([∘]-Se ⊢T (⊢w⇒⊢s ⊢σ) (⊢w⇒⊢s ⊢τ))))


-- The gluing models for types and terms are monotonic.
®-mon : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i)
        (A≈B′ : A ≈ B ∈ 𝕌 i) →
        Γ ⊢ T ®[ i ] A≈B →
        Δ ⊢w σ ∶ Γ →
        -----------------------------------
        Δ ⊢ T [ σ ] ®[ i ] A≈B′
®-mon {_} {_} {_} {T} {Δ} {σ} {i} (ne {C} C≈C′) (ne C≈C′₁) (⊢T , rel) ⊢σ = t[σ]-Se ⊢T (⊢w⇒⊢s ⊢σ) , helper
  where helper : Δ′ ⊢w τ ∶ Δ → Δ′ ⊢ sub (sub T σ) τ ≈ Ne⇒Exp (proj₁ (C≈C′₁ (len Δ′))) ∶ Se i
        helper {Δ′} {τ} ⊢τ
          with C≈C′₁ (len Δ′) | C≈C′ (len Δ′) | rel (⊢w-∘ ⊢σ ⊢τ)
        ...  | u , ↘u , _ | u′ , ↘u′ , _ | Tστ≈
             rewrite Re-det ↘u ↘u′ = ≈-trans ([∘]-Se ⊢T (⊢w⇒⊢s ⊢σ) (⊢w⇒⊢s ⊢τ)) Tστ≈
®-mon N N T∼A ⊢σ                                                         = ≈-trans ([]-cong-Se′ T∼A (⊢w⇒⊢s ⊢σ)) (N-[] _ (⊢w⇒⊢s ⊢σ))
®-mon (U j<i eq) (U j′<i eq′) T∼A ⊢σ                                     = ≈-trans ([]-cong-Se′ T∼A (⊢w⇒⊢s ⊢σ)) (lift-⊢≈-Se (Se-[] _ (⊢w⇒⊢s ⊢σ)) j<i)
®-mon {Π A _ ρ} {_} {_} {_} {Δ} {σ} {i} (Π iA RT) (Π iA′ RT′) T∼A ⊢σ     = record
  { IT   = IT [ σ ]
  ; OT   = OT [ q σ ]
  ; ⊢OT  = t[σ]-Se ⊢OT (⊢q ⊢σ′ ⊢IT)
  ; T≈   = ≈-trans ([]-cong-Se′ T≈ (⊢w⇒⊢s ⊢σ)) (Π-[] (⊢w⇒⊢s ⊢σ) ⊢IT ⊢OT)
  ; krip = λ ⊢τ → record
    { IT-rel = IT-mon-helper iA RT iA′ RT′ ⊢IT ⊢σ ⊢τ (ΠRel.IT-rel (krip (⊢w-∘ ⊢σ ⊢τ)))
    ; OT-rel = helper′ ⊢τ
    }
  }
  where open GluΠ T∼A
        ⊢σ′ = ⊢w⇒⊢s ⊢σ
        ⊢IT = ®Π-wf iA RT T∼A
        helper′ : Δ′ ⊢w τ ∶ Δ → Δ′ ⊢ s ∶ IT [ σ ] [ τ ] ®[ i ] a ∈El iA′ → (a∈ : a ∈′ El i iA′) → Δ′ ⊢ OT [ q σ ] [ τ , s ] ®[ i ] (ΠRT.T≈T′ (RT′ a∈))
        helper′ {Δ′} {τ} {s} ⊢τ s∼a a∈
          with ΠRel.OT-rel (krip (⊢w-∘ ⊢σ ⊢τ))
             | ®El-resp-T≈ iA (®El-one-sided iA′ iA s∼a) ([∘]-Se ⊢IT ⊢σ′ (⊢w⇒⊢s ⊢τ))
             | El-one-sided iA′ iA a∈
        ...  | OT-rel | s∼a′ | a∈′
             with RT a∈′ | RT′ a∈ | OT-rel s∼a′ a∈′
        ...     | record { ⟦T⟧ = ⟦T⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; T≈T′ = T≈T′ }
                | record { ↘⟦T⟧ = ↘⟦T⟧′ ; T≈T′ = T≈T′₁ }
                | rel
                rewrite ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧ = ®-resp-≈ T≈T′₁ (®-≡ T≈T′ T≈T′₁ rel refl) ([]-q-∘-, ⊢OT ⊢σ′ ⊢τ′ ⊢s)
          where open ER
                ⊢τ′  = ⊢w⇒⊢s ⊢τ
                ⊢s   = ®El⇒tm iA′ s∼a

®El-mon : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i)
          (A≈B′ : A ≈ B ∈ 𝕌 i) →
          Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
          Δ ⊢w σ ∶ Γ →
          --------------------------------------
          Δ ⊢ t [ σ ] ∶ T [ σ ] ®[ i ] a ∈El A≈B′
®El-mon {_} {_} {_} {t} {T} {a} {Δ} {σ} {i} (ne {C} C≈C′) (ne C≈C′₁) (ne {c} c∈ , glu) ⊢σ
  = ne c∈ , record
  { t∶T  = t[σ] t∶T ⊢σ′
  ; ⊢T   = t[σ]-Se ⊢T ⊢σ′
  ; krip = helper
  }
  where open GluNe glu
        ⊢σ′ = ⊢w⇒⊢s ⊢σ
        helper : Δ′ ⊢w τ ∶ Δ → Δ′ ⊢ T [ σ ] [ τ ] ≈ Ne⇒Exp (proj₁ (C≈C′₁ (len Δ′))) ∶ Se i
                             × Δ′ ⊢ t [ σ ] [ τ ] ≈ Ne⇒Exp (proj₁ (c∈ (len Δ′))) ∶ T [ σ ] [ τ ]
        helper {Δ′} {τ} ⊢τ
          with C≈C′ (len Δ′) | C≈C′₁ (len Δ′)
             | c∈ (len Δ′)
             | krip (⊢w-∘ ⊢σ ⊢τ)
        ...  | V , ↘V , _ | V′ , ↘V′ , _  | u , ↘u , _ | Tστ≈ , tστ≈
             rewrite Re-det ↘V ↘V′ = ≈-trans ([∘]-Se ⊢T ⊢σ′ (⊢w⇒⊢s ⊢τ)) Tστ≈ , ≈-conv (≈-trans (≈-sym ([∘] (⊢w⇒⊢s ⊢τ) ⊢σ′ t∶T)) tστ≈) (≈-sym ([∘]-Se ⊢T ⊢σ′ (⊢w⇒⊢s ⊢τ)))
®El-mon N N (t∼a , T≈N) ⊢σ                                               = ®Nat-mon t∼a ⊢σ , ≈-trans ([]-cong-Se′ T≈N (⊢w⇒⊢s ⊢σ)) (N-[] _ (⊢w⇒⊢s ⊢σ))
®El-mon {_} {_} {σ} (U j<i eq) (U j′<i eq′) t∼a ⊢σ
  rewrite Glu-wellfounded-≡ j<i
        | Glu-wellfounded-≡ j′<i                                         = record
  { t∶T = t[σ] t∶T (⊢w⇒⊢s ⊢σ)
  ; T≈  = ≈-trans ([]-cong-Se′ T≈ (⊢w⇒⊢s ⊢σ)) (lift-⊢≈-Se (Se-[] _ (⊢w⇒⊢s ⊢σ)) j<i)
  ; A∈𝕌 = A∈𝕌
  ; rel = ®-mon A∈𝕌 A∈𝕌 rel ⊢σ
  }
  where open GluU t∼a
®El-mon {Π A _ ρ} {_} {_} {t} {_} {f} {Δ} {σ} {i} (Π iA RT) (Π iA′ RT′) t∼a ⊢σ = record
  { t∶T  = t[σ] t∶T ⊢σ′
  ; a∈El = El-one-sided (Π iA RT) (Π iA′ RT′) a∈El
  ; IT   = IT [ σ ]
  ; OT   = OT [ q σ ]
  ; ⊢OT  = t[σ]-Se ⊢OT ⊢qσ
  ; T≈   = ≈-trans ([]-cong-Se′ T≈ ⊢σ′) (Π-[] ⊢σ′ ⊢IT ⊢OT)
  ; krip = λ {_} {τ} ⊢τ →
    let open ΛRel (krip (⊢w-∘ ⊢σ ⊢τ))
    in record
    { IT-rel = IT-mon-helper iA RT iA′ RT′ ⊢IT ⊢σ ⊢τ IT-rel
    ; ap-rel = λ s∼a a∈ →
      let fa , ↘fa , ®fa = helper ⊢τ s∼a a∈
      in record
      { fa  = fa
      ; ↘fa = ↘fa
      ; ®fa = ®fa
      }
    }
  }
  where open GluΛ t∼a
        ⊢σ′ = ⊢w⇒⊢s ⊢σ
        ⊢IT = ®Π-wf iA RT (®El⇒® (Π iA RT) t∼a)
        ⊢qσ = ⊢q ⊢σ′ ⊢IT

        helper : Δ′ ⊢w τ ∶ Δ → Δ′ ⊢ s ∶ IT [ σ ] [ τ ] ®[ i ] a ∈El iA′ → (a∈ : a ∈′ El i iA′) →
                 ∃ λ fa → f ∙ a ↘ fa × Δ′ ⊢ t [ σ ] [ τ ] $ s ∶ OT [ q σ ] [ τ , s ] ®[ i ] fa ∈El ΠRT.T≈T′ (RT′ a∈)
        helper {Δ′} {τ} ⊢τ s∼a a∈
          with El-one-sided iA′ iA a∈
        ...  | a∈′
             with ΛRel.flipped-ap-rel (krip (⊢w-∘ ⊢σ ⊢τ)) a∈′
                | ®El-one-sided iA′ iA (®El-resp-T≈ iA′ s∼a ([∘]-Se ⊢IT ⊢σ′ (⊢w⇒⊢s ⊢τ)))
        ...     | rel | s∼a′
                with RT a∈′ | RT′ a∈
        ...        | record { ⟦T⟧ = ⟦T⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; T≈T′ = T≈T′ }
                   | record { ↘⟦T⟧ = ↘⟦T⟧′ ; T≈T′ = T≈T′₁ }
                   with rel s∼a′
        ...           | record { fa = fa ; ↘fa = ↘fa ; ®fa = ®fa }
                      rewrite ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧ = fa , ↘fa
                                                , ®El-one-sided T≈T′ T≈T′₁
                                                 (®El-resp-≈ T≈T′
                                                 (®El-resp-T≈ T≈T′ ®fa OT,≈)
                                                 (≈-conv ($-cong (≈-conv ([∘] ⊢τ′ ⊢σ′ t∶T) (≈-trans ([]-cong-Se′ T≈ ⊢στ) (Π-[] ⊢στ ⊢IT ⊢OT))) (≈-refl ⊢s′))
                                                         (≈-trans (≈-sym ([]-q-∘-,′ ⊢OT ⊢στ ⊢s′)) OT,≈)))
          where ⊢τ′  = ⊢w⇒⊢s ⊢τ
                ⊢s   = ®El⇒tm iA′ s∼a
                ⊢s′  = ®El⇒tm iA s∼a′
                ⊢στ  = s-∘ ⊢τ′ ⊢σ′
                OT,≈ = []-q-∘-, ⊢OT ⊢σ′ ⊢τ′ ⊢s

®-mon′ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
         Γ ⊢ T ®[ i ] A≈B →
         Δ ⊢w σ ∶ Γ →
         -----------------------------------
         Δ ⊢ T [ σ ] ®[ i ] A≈B
®-mon′ A≈B = ®-mon A≈B A≈B

®El-mon′ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
           Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
           Δ ⊢w σ ∶ Γ →
           --------------------------------------
           Δ ⊢ t [ σ ] ∶ T [ σ ] ®[ i ] a ∈El A≈B
®El-mon′ A≈B = ®El-mon A≈B A≈B
