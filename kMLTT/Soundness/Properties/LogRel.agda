{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Soundness.Properties.LogRel (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Data.Nat
open import Data.Nat.Properties as ℕₚ

open import kMLTT.Statics.Properties
open import kMLTT.Semantics.Readback
open import kMLTT.Semantics.Properties.Domain fext
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Soundness.LogRel

open import kMLTT.Soundness.Properties.NoFunExt.LogRel public


®Nat-mon : Γ ⊢ t ∶N® a ∈Nat → Δ ⊢r σ ∶ Γ → Δ ⊢ t [ σ ] ∶N® a [ mt σ ] ∈Nat
®Nat-mon (ze t≈) ⊢σ                             = ze (≈-trans ([]-cong-N′ t≈ (⊢r⇒⊢s ⊢σ)) (ze-[] (⊢r⇒⊢s ⊢σ)))
®Nat-mon (su t≈ t∼a) ⊢σ                         = su (≈-trans ([]-cong-N′ t≈ ⊢σ′) (su-[] ⊢σ′ (®Nat⇒∶Nat t∼a (proj₂ (presup-s ⊢σ′))))) (®Nat-mon t∼a ⊢σ)
  where ⊢σ′ = ⊢r⇒⊢s ⊢σ
®Nat-mon {_} {t} {_} {Δ} {σ} (ne {c} c∈ rel) ⊢σ = ne (Bot-mon (mt σ) c∈) helper
  where helper : Δ′ ⊢r τ ∶ Δ → Δ′ ⊢ t [ σ ] [ τ ] ≈ Ne⇒Exp (proj₁ (Bot-mon (mt σ) c∈ (map len Δ′) (mt τ))) ∶ N
        helper {Δ′} {τ} ⊢τ
          with c∈ (map L.length Δ′) (mt σ ø mt τ) | Bot-mon (mt σ) c∈ (map len Δ′) (mt τ) | rel (⊢r-∘ ⊢σ ⊢τ)
        ...  | u , ↘u , _ | u′ , ↘u′ , _ | tστ≈
             rewrite  Dn-comp c (mt σ) (mt τ)
                   | Re-det ↘u ↘u′ = ≈-trans ([∘]-N (®Nat⇒∶Nat (ne c∈ rel) (proj₂ (presup-s (⊢r⇒⊢s ⊢σ)))) (⊢r⇒⊢s ⊢σ) (⊢r⇒⊢s ⊢τ)) tστ≈

Glu-wellfounded-≡′ : ∀ {i i′ j} (j<i : j < i) (j<i′ : j < i′) → (λ {A B} → Glu-wellfounded i j<i {A} {B}) ≡ Glu-wellfounded i′ j<i′
Glu-wellfounded-≡′ (s≤s j<i) (s≤s j′<i) = cong (Glu._⊢_®_ _) (implicit-extensionality fext
                                                             λ {j′} → fext λ j′<j → Glu-wellfounded-≡′ (≤-trans j′<j j<i) (≤-trans j′<j j′<i))

Glu-wellfounded-≡ : ∀ {i j} (j<i : j < i) → (λ {A B} → Glu-wellfounded i j<i {A} {B}) ≡ _⊢_®[ j ]_
Glu-wellfounded-≡ (s≤s j<i) = cong (Glu._⊢_®_ _) (implicit-extensionality fext λ {j′} → fext (λ j′<j → Glu-wellfounded-≡′ (≤-trans j′<j j<i) j′<j))

®El⇒tm : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
           Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
           ---------------------------
           Γ ⊢ t ∶ T
®El⇒tm (ne C≈C′) (ne _ , glu) = GluNe.t∶T glu
®El⇒tm N (t∼a , T≈N)          = conv (®Nat⇒∶Nat t∼a (proj₁ (presup-≈ T≈N))) (≈-sym T≈N)
®El⇒tm (U j<i eq) t∼a         = GluU.t∶T t∼a
®El⇒tm (□ A≈B) t∼a            = Glubox.t∶T t∼a
®El⇒tm (Π iA RT) t∼a          = GluΛ.t∶T t∼a


®El⇒∈El : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
          Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
          -----------------------------
          a ∈′ El i A≈B
®El⇒∈El (ne C≈C′) (a∈⊥ , _)         = a∈⊥
®El⇒∈El N (t∼a , _)                 = ®Nat⇒∈Nat t∼a
®El⇒∈El (U j<i eq) t∼a
  rewrite 𝕌-wellfounded-≡-𝕌 _ j<i = GluU.A∈𝕌 t∼a
®El⇒∈El (□ A≈B) t∼a                 = Glubox.a∈El t∼a
®El⇒∈El (Π iA RT) t∼a               = GluΛ.a∈El t∼a

®El⇒® : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
        Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
        ----------------------------
        Γ ⊢ T ®[ i ] A≈B
®El⇒® (ne C≈C′) (ne c∈ , glu) = ⊢T , λ ⊢σ → proj₁ (krip ⊢σ)
  where open GluNe glu
®El⇒® N (_ , T≈N)             = T≈N
®El⇒® (U j<i eq) t∼a          = GluU.T≈ t∼a
®El⇒® (□ A≈B) t∼a             = record
  { GT   = GT
  ; T≈   = T≈
  ; krip = λ {_} {σ} Ψs ⊢σ →
    let open □Krip (krip Ψs ⊢σ)
    in ®El⇒® (A≈B (ins (mt σ) (len Ψs))) rel
  }
  where open Glubox t∼a
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
      in ®El⇒® (ΠRT.T≈T′ (RT (mt σ) a∈)) ®fa
    }
  }
  where open GluΛ t∼a


®El⇒ty : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
           Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
           ---------------------------
           Γ ⊢ T ∶ Se i
®El⇒ty A≈B t∼a = ®⇒ty A≈B (®El⇒® A≈B t∼a)


®El-resp-≈ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
             Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
             Γ ⊢ t ≈ t′ ∶ T →
             ----------------------------
             Γ ⊢ t′ ∶ T ®[ i ] a ∈El A≈B
®El-resp-≈ (ne C≈C′) (ne c∈ , glu) t≈t′ = ne c∈ , record
  { t∶T  = proj₁ (proj₂ (proj₂ (presup-≈ t≈t′)))
  ; ⊢T   = ⊢T
  ; krip = λ ⊢σ → proj₁ (krip ⊢σ) , ≈-trans ([]-cong (≈-sym t≈t′) (s-≈-refl (⊢r⇒⊢s ⊢σ))) (proj₂ (krip ⊢σ))
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
®El-resp-≈ {_} {_} {Γ} (□ A≈B) t∼a t≈t′ = record
  { GT   = GT
  ; t∶T  = proj₁ (proj₂ (proj₂ (presup-≈ t≈t′)))
  ; a∈El = a∈El
  ; T≈   = T≈
  ; krip = λ {Δ} {σ} Ψs ⊢σ →
    let open □Krip (krip Ψs ⊢σ)
        ⊢σ′     = ⊢r⇒⊢s ⊢σ
        ⊢ΨsΔ    = proj₁ (presup-tm (®El⇒tm (A≈B (ins (mt σ) (len Ψs))) rel))
        ⊢Δ      = ⊢⇒∥⊢ Ψs ⊢ΨsΔ
        ⊢IΨs    = s-； Ψs (s-I ⊢Δ) ⊢ΨsΔ refl
        ⊢□GT    = proj₁ (proj₂ (proj₂ (presup-≈ T≈)))
        _ , ⊢GT = inv-□-wf ⊢□GT
    in record
    { ua  = ua
    ; ↘ua = ↘ua
    ; rel = ®El-resp-≈ (A≈B (ins (mt σ) (len Ψs))) rel
                       (≈-conv (unbox-cong Ψs (≈-conv ([]-cong t≈t′ (s-≈-refl ⊢σ′)) (≈-trans ([]-cong-Se′ (lift-⊢≈-Se-max T≈) ⊢σ′) (□-[] ⊢σ′ (lift-⊢-Se-max′ ⊢GT))))
                                           ⊢ΨsΔ refl)
                               (≈-trans ([∘]-Se ⊢GT (s-； L.[ [] ] ⊢σ′ (⊢κ ⊢Δ) refl) ⊢IΨs)
                                        ([]-cong-Se″ ⊢GT (s-≈-trans (；-∘ L.[ [] ] ⊢σ′ ⊢IΨs refl)
                                                         (subst (λ n → Ψs ++⁺ Δ ⊢s (σ ∘ I) ； n ≈ σ ； len Ψs ∶ [] ∷⁺ Γ)
                                                                (sym (+-identityʳ _))
                                                                (；-cong Ψs (∘-I ⊢σ′) ⊢ΨsΔ refl))))))
    }
  }
  where open Glubox t∼a
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
          ⊢σ′     = ⊢r⇒⊢s ⊢σ
          ⊢s      = ®El⇒tm _ s∼b
          ⊢Π      = proj₁ (proj₂ (proj₂ (presup-≈ T≈)))
          j , ⊢IT = inv-Π-wf′ ⊢Π
          k , ⊢OT = inv-Π-wf ⊢Π
      in record
      { fa  = fa
      ; ↘fa = ↘fa
      ; ®fa = ®El-resp-≈ (ΠRT.T≈T′ (RT (mt σ) b∈)) ®fa
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


®El-resp-⊢≈ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
              Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
              ⊢ Γ ≈ Δ →
              ---------------------------
              Δ ⊢ t ∶ T ®[ i ] a ∈El A≈B
®El-resp-⊢≈ (ne C≈C′) (ne c∈⊥ , rel) Γ≈Δ = ne c∈⊥ , record
  { t∶T  = ctxeq-tm Γ≈Δ t∶T
  ; ⊢T   = ctxeq-tm Γ≈Δ ⊢T
  ; krip = λ ⊢σ → krip (⊢r-resp-⊢≈ʳ ⊢σ (⊢≈-sym Γ≈Δ))
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
®El-resp-⊢≈ (□ A≈B) t∼a Γ≈Δ              = record
  { GT   = GT
  ; t∶T  = ctxeq-tm Γ≈Δ t∶T
  ; a∈El = a∈El
  ; T≈   = ctxeq-≈ Γ≈Δ T≈
  ; krip = λ Ψs ⊢σ → krip Ψs (⊢r-resp-⊢≈ʳ ⊢σ (⊢≈-sym Γ≈Δ))
  }
  where open Glubox t∼a
®El-resp-⊢≈ (Π iA RT) t∼a Γ≈Δ            = record
  { t∶T  = ctxeq-tm Γ≈Δ t∶T
  ; a∈El = a∈El
  ; IT   = IT
  ; OT   = OT
  ; ⊢OT  = ctxeq-tm (∷-cong Γ≈Δ (≈-refl (®Π-wf iA RT (®El⇒® (Π iA RT) t∼a)))) ⊢OT
  ; T≈   = ctxeq-≈ Γ≈Δ T≈
  ; krip = λ ⊢σ → krip (⊢r-resp-⊢≈ʳ ⊢σ (⊢≈-sym Γ≈Δ))
  }
  where open GluΛ t∼a

mutual

  ®-one-sided : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i)
                  (A≈B′ : A ≈ B′ ∈ 𝕌 i) →
                  Γ ⊢ T ®[ i ] A≈B →
                  -----------------------
                  Γ ⊢ T ®[ i ] A≈B′
  ®-one-sided {Γ = Γ} {T} {i} (ne C≈C′) (ne C≈C″) (⊢T , rel) = ⊢T , helper
    where helper : Δ ⊢r σ ∶ Γ → Δ ⊢ T [ σ ] ≈ Ne⇒Exp (proj₁ (C≈C″ (map len Δ) (mt σ))) ∶ Se i
          helper {Δ} {σ} ⊢σ
            with C≈C′ (map len Δ) (mt σ) | C≈C″ (map len Δ) (mt σ) | rel ⊢σ
          ...  | u , ↘u , _ | u′ , ↘u′ , _ | Tσ≈
               rewrite Re-det ↘u ↘u′ = Tσ≈
  ®-one-sided N N T∼A                                        = T∼A
  ®-one-sided (U j<i eq) (U j′<i eq′) T∼A                    = T∼A
  ®-one-sided (□ A≈B) (□ A≈B′) T∼A                           = record
    { GT   = GT
    ; T≈   = T≈
    ; krip = λ {_} {σ} Ψs ⊢σ → ®-one-sided (A≈B (ins (mt σ) (len Ψs))) (A≈B′ (ins (mt σ) (len Ψs))) (krip Ψs ⊢σ)
    }
    where open Glu□ T∼A
  ®-one-sided {Γ = Γ} {_} {i} (Π iA RT) (Π iA′ RT′) T∼A      = record
    { IT   = IT
    ; OT   = OT
    ; ⊢OT  = ⊢OT
    ; T≈   = T≈
    ; krip = λ {_} {σ} ⊢σ →
      let open ΠRel (krip ⊢σ)
      in record
      { IT-rel = ®-one-sided (iA (mt σ)) (iA′ (mt σ)) IT-rel
      ; OT-rel = helper ⊢σ
      }
    }
    where open GluΠ T∼A
          helper : Δ ⊢r σ ∶ Γ → Δ ⊢ s ∶ IT [ σ ] ®[ i ] a ∈El iA′ (mt σ) → (a∈ : a ∈′ El i (iA′ (mt σ))) → Δ ⊢ OT [ σ , s ] ®[ i ] (ΠRT.T≈T′ (RT′ (mt σ) a∈))
          helper {Δ} {σ} ⊢σ s∼a a∈
            with krip ⊢σ | El-one-sided (iA′ (mt σ)) (iA (mt σ)) a∈
          ...  | record { OT-rel = OT-rel } | a∈′
               with RT (mt σ) a∈′ | RT′ (mt σ) a∈ | OT-rel (®El-one-sided (iA′ (mt σ)) (iA (mt σ)) s∼a) a∈′
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
          helper : Δ ⊢r σ ∶ Γ → Δ ⊢ T [ σ ] ≈ Ne⇒Exp (proj₁ (C≈C″ (map len Δ) (mt σ))) ∶ Se i × Δ ⊢ t [ σ ] ≈ Ne⇒Exp (proj₁ (c∈ (map len Δ) (mt σ))) ∶ T [ σ ]
          helper {Δ} {σ} ⊢σ
            with C≈C′ (map len Δ) (mt σ) | C≈C″ (map len Δ) (mt σ) | krip ⊢σ
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
  ®El-one-sided (□ A≈B) (□ A≈B′) t∼a                                      = record
    { GT   = GT
    ; t∶T  = t∶T
    ; a∈El = El-one-sided (□ A≈B) (□ A≈B′) a∈El
    ; T≈   = T≈
    ; krip = λ {_} {σ }Ψs ⊢σ →
      let open □Krip (krip Ψs ⊢σ)
      in record
      { ua  = ua
      ; ↘ua = ↘ua
      ; rel = ®El-one-sided (A≈B (ins (mt σ) (len Ψs))) (A≈B′ (ins (mt σ) (len Ψs))) rel
      }
    }
    where open Glubox t∼a
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
      { IT-rel = ®-one-sided (iA (mt σ)) (iA′ (mt σ)) IT-rel
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
          helper : Δ ⊢r σ ∶ Γ → Δ ⊢ s ∶ IT [ σ ] ®[ i ] a ∈El iA′ (mt σ) → (a∈ : a ∈′ El i (iA′ (mt σ))) →
                   ∃ λ fa → f [ mt σ ] ∙ a ↘ fa × Δ ⊢ t [ σ ] $ s ∶ OT [ σ , s ] ®[ i ] fa ∈El (ΠRT.T≈T′ (RT′ (mt σ) a∈))
          helper {Δ} {σ} ⊢σ s∼a a∈
            with krip ⊢σ | El-one-sided (iA′ (mt σ)) (iA (mt σ)) a∈
          ...  | record { ap-rel = ap-rel } | a∈′
               with RT (mt σ) a∈′ | RT′ (mt σ) a∈ | ap-rel (®El-one-sided (iA′ (mt σ)) (iA (mt σ)) s∼a) a∈′
          ...     | record { ⟦T⟧ = ⟦T⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; T≈T′ = T≈T′ }
                  | record { ↘⟦T⟧ = ↘⟦T⟧′ ; T≈T′ = T≈T′₁ }
                  | R
              rewrite ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧ = fa , ↘fa , ®El-one-sided T≈T′ T≈T′₁ ®fa
            where open ΛKripke R


®-≡ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) (A′≈B′ : A′ ≈ B′ ∈ 𝕌 i) → Γ ⊢ T ®[ i ] A≈B → A ≡ A′ → Γ ⊢ T ®[ i ] A′≈B′
®-≡ A≈B A′≈B′ T∼A refl = ®-one-sided A≈B A′≈B′ T∼A

®El-≡ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) (A′≈B′ : A′ ≈ B′ ∈ 𝕌 i) → Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B → A ≡ A′ → Γ ⊢ t ∶ T ®[ i ] a ∈El A′≈B′
®El-≡ A≈B A′≈B′ t∼a refl = ®El-one-sided A≈B A′≈B′ t∼a

private
  IT-mon-helper : ∀ {i} (iA : ∀ (κ : UMoT) → A [ κ ] ≈ B [ κ ] ∈ 𝕌 i)
                   (RT : ∀ {a a′} (κ : UMoT) →
                         a ≈ a′ ∈ El i (iA κ) →
                         ΠRT T′ (ρ [ κ ] ↦ a) T″ (ρ′ [ κ ] ↦ a′) (𝕌 i))
                   (iA′ : ∀ (κ : UMoT) → A [ mt σ ] [ κ ] ≈ B [ mt σ ] [ κ ] ∈ 𝕌 i)
                   (RT′ : ∀ {a a′} (κ : UMoT) →
                          a ≈ a′ ∈ El i (iA′ κ) →
                          ΠRT T′ (ρ [ mt σ ] [ κ ] ↦ a) T″ (ρ′ [ mt σ ] [ κ ] ↦ a′) (𝕌 i)) →
                  Γ ⊢ T ∶ Se i →
                  Δ ⊢r σ ∶ Γ →
                  Δ′ ⊢r τ ∶ Δ →
                  Δ′ ⊢ T [ σ ∘ τ ] ®[ i ] iA (mt (σ ∘ τ)) →
                  Δ′ ⊢ T [ σ ] [ τ ] ®[ i ] iA′ (mt τ)
  IT-mon-helper {σ = σ} {Δ′ = Δ′} {τ} iA RT iA′ RT′ ⊢T ⊢σ ⊢τ T∼A = ®-≡ (iA (mt (σ ∘ τ)))
                                                                       (iA′ (mt τ))
                                                                       (®-resp-≈ (iA (mt (σ ∘ τ))) T∼A (≈-sym ([∘]-Se ⊢T (⊢r⇒⊢s ⊢σ) (⊢r⇒⊢s ⊢τ))))
                                                                       (sym (D-comp _ (mt σ) (mt τ)))

®-mon : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i)
        (A≈Bσ : A [ mt σ ] ≈ B [ mt σ ] ∈ 𝕌 i) →
        Γ ⊢ T ®[ i ] A≈B →
        Δ ⊢r σ ∶ Γ →
        -----------------------------------
        Δ ⊢ T [ σ ] ®[ i ] A≈Bσ
®-mon {_} {_} {σ} {_} {T} {Δ} {i} (ne {C} C≈C′) (ne C≈C′σ) (⊢T , rel) ⊢σ = t[σ]-Se ⊢T (⊢r⇒⊢s ⊢σ) , helper
  where helper : Δ′ ⊢r τ ∶ Δ → Δ′ ⊢ sub (sub T σ) τ ≈ Ne⇒Exp (proj₁ (C≈C′σ (map len Δ′) (mt τ))) ∶ Se i
        helper {Δ′} {τ} ⊢τ
          with C≈C′σ (map len Δ′) (mt τ) | C≈C′ (map len Δ′) (mt (σ ∘ τ)) | rel (⊢r-∘ ⊢σ ⊢τ)
        ...  | u , ↘u , _ | u′ , ↘u′ , _ | Tστ≈
             rewrite Dn-comp C (mt σ) (mt τ)
                   | Re-det ↘u ↘u′ = ≈-trans ([∘]-Se ⊢T (⊢r⇒⊢s ⊢σ) (⊢r⇒⊢s ⊢τ)) Tστ≈
®-mon N N T∼A ⊢σ                                                         = ≈-trans ([]-cong-Se′ T∼A (⊢r⇒⊢s ⊢σ)) (N-[] _ (⊢r⇒⊢s ⊢σ))
®-mon (U j<i eq) (U j′<i eq′) T∼A ⊢σ                                     = ≈-trans ([]-cong-Se′ T∼A (⊢r⇒⊢s ⊢σ)) (lift-⊢≈-Se (Se-[] _ (⊢r⇒⊢s ⊢σ)) j<i)
®-mon {□ A} {□ B} {σ} {_} {_} {Δ} {i} (□ A≈B) (□ A≈Bσ) T∼A ⊢σ            = record
  { GT   = GT [ σ ； 1 ]
  ; T≈   = ≈-trans ([]-cong-Se′ T≈ ⊢σ′) (□-[] ⊢σ′ ⊢GT)
  ; krip = helper
  }
  where open Glu□ T∼A
        ⊢σ′ = ⊢r⇒⊢s ⊢σ
        ⊢GT = ®□⇒wf A≈B T∼A
        ⊢Δ  = proj₁ (presup-s ⊢σ′)
        ⊢Γ  = proj₂ (presup-s ⊢σ′)
        helper : ∀ Ψs → Δ′ ⊢r τ ∶ Δ → Ψs ++⁺ Δ′ ⊢ GT [ σ ； 1 ] [ τ ； len Ψs ] ®[ i ] A≈Bσ (ins (mt τ) (len Ψs))
        helper {Δ′} {τ} Ψs ⊢τ = ®-≡ (A≈B (ins (mt σ ø mt τ) (len Ψs)))
                                    (A≈Bσ (ins (mt τ) (len Ψs)))
                                    (®-resp-≈ (A≈B (ins (mt σ ø mt τ) (len Ψs))) GT[]∼ ([]-∘-； Ψs ⊢ΨsΔ′ ⊢GT ⊢σ′ ⊢τ′))
                                    (sym (D-ins-ins′ A (mt σ) (mt τ) (len Ψs)))
          where open ER
                ⊢τ′   = ⊢r⇒⊢s ⊢τ
                GT[]∼ = krip Ψs (⊢r-∘ ⊢σ ⊢τ)
                ⊢GT[] = ®⇒ty (A≈B (ins (mt (σ ∘ τ)) (len Ψs))) GT[]∼
                ⊢ΨsΔ′ = proj₁ (presup-tm ⊢GT[])
®-mon {Π A _ ρ} {_} {σ} {_} {_} {Δ} {i} (Π iA RT) (Π iA′ RT′) T∼A ⊢σ     = record
  { IT   = IT [ σ ]
  ; OT   = OT [ q σ ]
  ; ⊢OT  = t[σ]-Se ⊢OT (⊢q ⊢σ′ ⊢IT)
  ; T≈   = ≈-trans ([]-cong-Se′ T≈ (⊢r⇒⊢s ⊢σ)) (Π-[] (⊢r⇒⊢s ⊢σ) ⊢IT ⊢OT)
  ; krip = λ ⊢τ → record
    { IT-rel = IT-mon-helper iA RT iA′ RT′ ⊢IT ⊢σ ⊢τ (ΠRel.IT-rel (krip (⊢r-∘ ⊢σ ⊢τ)))
    ; OT-rel = helper′ ⊢τ
    }
  }
  where open GluΠ T∼A
        ⊢σ′ = ⊢r⇒⊢s ⊢σ
        ⊢IT = ®Π-wf iA RT T∼A
        helper′ : Δ′ ⊢r τ ∶ Δ → Δ′ ⊢ s ∶ IT [ σ ] [ τ ] ®[ i ] a ∈El (iA′ (mt τ)) → (a∈ : a ∈′ El i (iA′ (mt τ))) → Δ′ ⊢ OT [ q σ ] [ τ , s ] ®[ i ] (ΠRT.T≈T′ (RT′ (mt τ) a∈))
        helper′ {Δ′} {τ} {s} ⊢τ s∼a a∈
          with ΠRel.OT-rel (krip (⊢r-∘ ⊢σ ⊢τ))
             | ®El-resp-T≈ (iA (mt (σ ∘ τ))) (®El-≡ (iA′ (mt τ)) (iA (mt (σ ∘ τ))) s∼a (D-comp _ (mt σ) (mt τ))) ([∘]-Se ⊢IT ⊢σ′ (⊢r⇒⊢s ⊢τ))
             | El-transp (iA′ (mt τ)) (iA (mt (σ ∘ τ))) a∈ (D-comp _ (mt σ) (mt τ))
        ...  | OT-rel | s∼a′ | a∈′
             with RT (mt σ ø mt τ) a∈′ | RT′ (mt τ) a∈ | OT-rel s∼a′ a∈′
        ...     | record { ⟦T⟧ = ⟦T⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; T≈T′ = T≈T′ }
                | record { ↘⟦T⟧ = ↘⟦T⟧′ ; T≈T′ = T≈T′₁ }
                | rel
                rewrite ρ-comp ρ (mt σ) (mt τ)
                      | ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧ = ®-resp-≈ T≈T′₁ (®-≡ T≈T′ T≈T′₁ rel refl) ([]-q-∘-, ⊢OT ⊢σ′ ⊢τ′ ⊢s)
          where open ER
                ⊢τ′  = ⊢r⇒⊢s ⊢τ
                ⊢s   = ®El⇒tm (iA′ (mt τ)) s∼a


®El-mon : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i)
          (A≈Bσ : A [ mt σ ] ≈ B [ mt σ ] ∈ 𝕌 i) →
          Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
          Δ ⊢r σ ∶ Γ →
          --------------------------------------
          Δ ⊢ t [ σ ] ∶ T [ σ ] ®[ i ] a [ mt σ ] ∈El A≈Bσ
®El-mon {_} {_} {σ} {_} {t} {T} {a} {Δ} {i} (ne {C} C≈C′) (ne C≈C′σ) (ne {c} c∈ , glu) ⊢σ
  = ne (Bot-mon (mt σ) c∈) , record
  { t∶T  = t[σ] t∶T ⊢σ′
  ; ⊢T   = t[σ]-Se ⊢T ⊢σ′
  ; krip = helper
  }
  where open GluNe glu
        ⊢σ′ = ⊢r⇒⊢s ⊢σ
        helper : Δ′ ⊢r τ ∶ Δ → Δ′ ⊢ T [ σ ] [ τ ] ≈ Ne⇒Exp (proj₁ (C≈C′σ (map len Δ′) (mt τ))) ∶ Se i
                             × Δ′ ⊢ t [ σ ] [ τ ] ≈ Ne⇒Exp (proj₁ (Bot-mon (mt σ) c∈ (map len Δ′) (mt τ))) ∶ T [ σ ] [ τ ]
        helper {Δ′} {τ} ⊢τ
          with C≈C′ (map len Δ′) (mt σ ø mt τ) | C≈C′σ (map len Δ′) (mt τ)
             | c∈ (map len Δ′) (mt σ ø mt τ) | Bot-mon (mt σ) c∈ (map len Δ′) (mt τ)
             | krip (⊢r-∘ ⊢σ ⊢τ)
        ...  | V , ↘V , _ | V′ , ↘V′ , _  | u , ↘u , _ | u′ , ↘u′ , _ | Tστ≈ , tστ≈
             rewrite Dn-comp C (mt σ) (mt τ)
                   | Dn-comp c (mt σ) (mt τ)
                   | Re-det ↘V ↘V′
                   | Re-det ↘u ↘u′ = ≈-trans ([∘]-Se ⊢T ⊢σ′ (⊢r⇒⊢s ⊢τ)) Tστ≈ , ≈-conv (≈-trans (≈-sym ([∘] (⊢r⇒⊢s ⊢τ) ⊢σ′ t∶T)) tστ≈) (≈-sym ([∘]-Se ⊢T ⊢σ′ (⊢r⇒⊢s ⊢τ)))
®El-mon N N (t∼a , T≈N) ⊢σ                                               = ®Nat-mon t∼a ⊢σ , ≈-trans ([]-cong-Se′ T≈N (⊢r⇒⊢s ⊢σ)) (N-[] _ (⊢r⇒⊢s ⊢σ))
®El-mon {_} {_} {σ} (U j<i eq) (U j′<i eq′) t∼a ⊢σ
  rewrite Glu-wellfounded-≡ j<i
        | Glu-wellfounded-≡ j′<i                                         = record
  { t∶T = t[σ] t∶T (⊢r⇒⊢s ⊢σ)
  ; T≈  = ≈-trans ([]-cong-Se′ T≈ (⊢r⇒⊢s ⊢σ)) (lift-⊢≈-Se (Se-[] _ (⊢r⇒⊢s ⊢σ)) j<i)
  ; A∈𝕌 = 𝕌-mon (mt σ) A∈𝕌
  ; rel = ®-mon A∈𝕌 (𝕌-mon (mt σ) A∈𝕌) rel ⊢σ
  }
  where open GluU t∼a
®El-mon {_} {_} {σ} {_} {t} {_} {_} {Δ} {i} (□ A≈B) (□ A≈Bσ) t∼a ⊢σ      = record
  { GT   = GT [ σ ； 1 ]
  ; t∶T  = t[σ] t∶T ⊢σ′
  ; a∈El = El-mon (□ A≈B) (mt σ) (□ A≈Bσ) a∈El
  ; T≈   = ≈-trans ([]-cong-Se′ T≈ ⊢σ′) (□-[] ⊢σ′ ⊢GT)
  ; krip = λ {_} {τ} Ψs ⊢τ →
    let open □Krip (krip Ψs (⊢r-∘ ⊢σ ⊢τ))
    in record
    { ua  = ua
    ; ↘ua = subst (unbox∙ len Ψs ,_↘ ua) (sym (D-comp _ (mt σ) (mt τ))) ↘ua
    ; rel = helper Ψs ⊢τ
    }
  }
  where open Glubox t∼a
        ⊢σ′ = ⊢r⇒⊢s ⊢σ
        ⊢GT = ®□⇒wf A≈B (®El⇒® (□ A≈B) t∼a)
        helper : ∀ Ψs (⊢τ : Δ′ ⊢r τ ∶ Δ) → Ψs ++⁺ Δ′ ⊢ unbox (len Ψs) (t [ σ ] [ τ ]) ∶ GT [ σ ； 1 ] [ τ ； len Ψs ] ®[ i ] □Krip.ua (krip Ψs (⊢r-∘ ⊢σ ⊢τ)) ∈El A≈Bσ (ins (mt τ) (len Ψs))
        helper {Δ′} {τ} Ψs ⊢τ
          with krip Ψs (⊢r-∘ ⊢σ ⊢τ)
        ...  | record { ua = ua ; rel = rel }
             with A≈B (ins (mt (σ ∘ τ)) (len Ψs)) | A≈Bσ (ins (mt τ) (len Ψs))
        ...     | Aστ≈ | Aστ≈′
                with ®El-≡ Aστ≈ Aστ≈′ rel (sym (D-ins-ins′ _ (mt σ) (mt τ) (len Ψs)))
        ...        | res
                   rewrite D-ap-vone ua = ®El-resp-≈ Aστ≈′ (®El-resp-T≈ Aστ≈′ res GTστ；≈)
                                                     (≈-conv (unbox-cong Ψs (≈-conv ([∘] ⊢τ′ ⊢σ′ t∶T) (≈-trans ([]-cong-Se′ T≈ ⊢στ) (□-[] ⊢στ ⊢GT))) ⊢ΨsΔ′ refl)
                                                             (≈-trans (≈-sym ([]-∘-；′ Ψs ⊢ΨsΔ′ ⊢GT ⊢στ)) GTστ；≈))
          where ⊢ub     = ®El⇒tm Aστ≈ rel
                ⊢ΨsΔ′   = proj₁ (presup-tm ⊢ub)
                ⊢τ′     = ⊢r⇒⊢s ⊢τ
                ⊢στ     = s-∘ ⊢τ′ ⊢σ′
                GTστ；≈ = []-∘-； Ψs ⊢ΨsΔ′ ⊢GT ⊢σ′ ⊢τ′
®El-mon {Π A _ ρ} {_} {σ} {_} {t} {_} {f} {Δ} {i} (Π iA RT) (Π iA′ RT′) t∼a ⊢σ = record
  { t∶T  = t[σ] t∶T ⊢σ′
  ; a∈El = El-mon (Π iA RT) (mt σ) (Π iA′ RT′) a∈El
  ; IT   = IT [ σ ]
  ; OT   = OT [ q σ ]
  ; ⊢OT  = t[σ]-Se ⊢OT ⊢qσ
  ; T≈   = ≈-trans ([]-cong-Se′ T≈ ⊢σ′) (Π-[] ⊢σ′ ⊢IT ⊢OT)
  ; krip = λ {_} {τ} ⊢τ →
    let open ΛRel (krip (⊢r-∘ ⊢σ ⊢τ))
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
        ⊢σ′ = ⊢r⇒⊢s ⊢σ
        ⊢IT = ®Π-wf iA RT (®El⇒® (Π iA RT) t∼a)
        ⊢qσ = ⊢q ⊢σ′ ⊢IT

        helper : Δ′ ⊢r τ ∶ Δ → Δ′ ⊢ s ∶ IT [ σ ] [ τ ] ®[ i ] a ∈El (iA′ (mt τ)) → (a∈ : a ∈′ El i (iA′ (mt τ))) →
                 ∃ λ fa → f [ mt σ ] [ mt τ ] ∙ a ↘ fa × Δ′ ⊢ t [ σ ] [ τ ] $ s ∶ OT [ q σ ] [ τ , s ] ®[ i ] fa ∈El ΠRT.T≈T′ (RT′ (mt τ) a∈)
        helper {Δ′} {τ} ⊢τ s∼a a∈
          with El-transp (iA′ (mt τ)) (iA (mt σ ø mt τ)) a∈ (D-comp _ (mt σ) (mt τ))
        ...  | a∈′
             with ΛRel.flipped-ap-rel (krip (⊢r-∘ ⊢σ ⊢τ)) a∈′
                | ®El-≡ (iA′ (mt τ)) (iA (mt σ ø mt τ)) (®El-resp-T≈ (iA′ (mt τ)) s∼a ([∘]-Se ⊢IT ⊢σ′ (⊢r⇒⊢s ⊢τ))) (D-comp _ (mt σ) (mt τ))
        ...     | rel | s∼a′
                with iA (mt σ ø mt τ) | RT (mt σ ø mt τ) a∈′ | iA′ (mt τ) | RT′ (mt τ) a∈
        ...        | Aστ≈  | record { ⟦T⟧ = ⟦T⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; T≈T′ = T≈T′ }
                   | Aστ≈′ | record { ↘⟦T⟧ = ↘⟦T⟧′ ; T≈T′ = T≈T′₁ }
                   with rel s∼a′
        ...           | record { fa = fa ; ↘fa = ↘fa ; ®fa = ®fa }
                      rewrite ρ-comp ρ (mt σ) (mt τ)
                            | D-comp f (mt σ) (mt τ)
                            | ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧ = fa , ↘fa
                                                , ®El-one-sided T≈T′ T≈T′₁
                                                 (®El-resp-≈ T≈T′
                                                 (®El-resp-T≈ T≈T′ ®fa OT,≈)
                                                 (≈-conv ($-cong (≈-conv ([∘] ⊢τ′ ⊢σ′ t∶T) (≈-trans ([]-cong-Se′ T≈ ⊢στ) (Π-[] ⊢στ ⊢IT ⊢OT))) (≈-refl ⊢s′))
                                                         (≈-trans (≈-sym ([]-q-∘-,′ ⊢OT ⊢στ ⊢s′)) OT,≈)))
          where ⊢τ′  = ⊢r⇒⊢s ⊢τ
                ⊢s   = ®El⇒tm Aστ≈′ s∼a
                ⊢s′  = ®El⇒tm Aστ≈ s∼a′
                ⊢στ  = s-∘ ⊢τ′ ⊢σ′
                OT,≈ = []-q-∘-, ⊢OT ⊢σ′ ⊢τ′ ⊢s
