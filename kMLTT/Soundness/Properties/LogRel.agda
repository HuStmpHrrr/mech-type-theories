{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Soundness.Properties.LogRel (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Data.Nat
open import Data.Nat.Properties

open import kMLTT.Statics.Properties
open import kMLTT.Semantics.Readback
open import kMLTT.Semantics.Properties.Domain fext
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Soundness.LogRel

open import kMLTT.Soundness.Properties.NoFunExt.LogRel public


Glu-wellfounded-≡′ : ∀ {i i′ j} (j<i : j < i) (j<i′ : j < i′) → (λ {A B} → Glu-wellfounded i j<i {A} {B}) ≡ Glu-wellfounded i′ j<i′
Glu-wellfounded-≡′ (s≤s j<i) (s≤s j′<i) = cong (Glu._⊢_®_ _) (implicit-extensionality fext
                                                             λ {j′} → fext λ j′<j → Glu-wellfounded-≡′ (≤-trans j′<j j<i) (≤-trans j′<j j′<i))

Glu-wellfounded-≡ : ∀ {i j} (j<i : j < i) (A∈ : A ∈′ 𝕌 j) → (λ {A B} → Glu-wellfounded i j<i {A} {B}) ≡ _⊢_®[ j ]_
Glu-wellfounded-≡ {_} {suc i} {j} (s≤s j<i) A∈ = cong (Glu._⊢_®_ _) (implicit-extensionality fext
                                                                    λ {j′} → fext (λ j′<j → Glu-wellfounded-≡′ (≤-trans j′<j j<i) j′<j))

®El⇒tm : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) → Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B → Γ ⊢ t ∶ T
®El⇒tm (ne C≈C′) (ne _ , t∶T , _) = t∶T
®El⇒tm N (t∼a , T≈N)              = conv (®Nat⇒∶Nat t∼a (proj₁ (presup-≈ T≈N))) (≈-sym T≈N)
®El⇒tm (U j<i eq) ((A∈ , T∼A) , T≈)
  rewrite Glu-wellfounded-≡ j<i A∈ = conv (®⇒ty A∈ T∼A) (≈-sym T≈)
®El⇒tm (□ A≈B) t∼a                = Glubox.t∶T t∼a
®El⇒tm (Π iA RT) t∼a              = GluΛ.t∶T t∼a

®El⇒∈El : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) → Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B → a ∈′ El i A≈B
®El⇒∈El (ne C≈C′) (a∈⊥ , _)         = a∈⊥
®El⇒∈El N (t∼a , _)                 = ®Nat⇒∈Nat t∼a
®El⇒∈El (U j<i eq) ((A∈ , _) , _)
  rewrite 𝕌-wellfounded-≡-𝕌 _ j<i = A∈
®El⇒∈El (□ A≈B) t∼a                 = Glubox.a∈El t∼a
®El⇒∈El (Π iA RT) t∼a               = GluΛ.a∈El t∼a

®El⇒® : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) → Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B → Γ ⊢ T ®[ i ] A≈B
®El⇒® (ne C≈C′) (ne c≈c′ , _ , ⊢T , rel) = ⊢T , λ ⊢σ → proj₁ (rel ⊢σ)
®El⇒® N (_ , T≈N)                        = T≈N
®El⇒® (U j<i eq) (_ , T≈)                = T≈
®El⇒® (□ A≈B) t∼a                        = record
  { GT   = GT
  ; T≈   = T≈
  ; krip = λ {_} {σ} Ψs ⊢σ →
    let open □Krip (krip Ψs ⊢σ)
    in ®El⇒® (A≈B (ins (mt σ) (len Ψs))) rel 
  }
  where open Glubox t∼a
®El⇒® (Π iA RT) t∼a                      = record
  { IT   = IT
  ; OT   = OT
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

®El-resp-≈ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) → Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B → Γ ⊢ t ≈ t′ ∶ T → Γ ⊢ t′ ∶ T ®[ i ] a ∈El A≈B
®El-resp-≈ (ne C≈C′) (ne c≈c′ , ⊢t , ⊢T , rel) t≈t′ = ne c≈c′ , proj₁ (proj₂ (proj₂ (presup-≈ t≈t′))) , ⊢T , λ ⊢σ → proj₁ (rel ⊢σ) , ≈-trans ([]-cong (≈-sym t≈t′) (s-≈-refl (⊢r⇒⊢s ⊢σ))) (proj₂ (rel ⊢σ))
®El-resp-≈ N (t∼a , T≈N) t≈t′                       = ®Nat-resp-≈ t∼a (≈-conv t≈t′ T≈N) , T≈N
®El-resp-≈ (U j<i eq) ((A∈ , T∼A) , T≈) t≈t′
  rewrite Glu-wellfounded-≡ j<i A∈                  = (A∈ , ®̄-resp-≈ A∈ T∼A (≈-conv t≈t′ T≈)) , T≈
®El-resp-≈ {_} {_} {Γ} (□ A≈B) t∼a t≈t′             = record
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
®El-resp-≈ {i = i} (Π iA RT) t∼a t≈t′               = record
  { t∶T  = proj₁ (proj₂ (proj₂ (presup-≈ t≈t′)))
  ; a∈El = a∈El
  ; IT   = IT
  ; OT   = OT
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


mutual

  ®-one-sided : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) (A≈B′ : A ≈ B′ ∈ 𝕌 i) → Γ ⊢ T ®[ i ] A≈B → Γ ⊢ T ®[ i ] A≈B′
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

  ®El-one-sided : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) (A≈B′ : A ≈ B′ ∈ 𝕌 i) → Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B → Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B′
  ®El-one-sided {Γ = Γ} {t} {T} {_} {i} (ne C≈C′) (ne C≈C″) (ne c≈c′ , ⊢t , ⊢T , rel) = ne c≈c′ , ⊢t , ⊢T , helper
    where helper : Δ ⊢r σ ∶ Γ → Δ ⊢ T [ σ ] ≈ Ne⇒Exp (proj₁ (C≈C″ (map len Δ) (mt σ))) ∶ Se i × Δ ⊢ t [ σ ] ≈ Ne⇒Exp (proj₁ (c≈c′ (map len Δ) (mt σ))) ∶ T [ σ ]
          helper {Δ} {σ} ⊢σ
            with C≈C′ (map len Δ) (mt σ) | C≈C″ (map len Δ) (mt σ) | rel ⊢σ
          ...  | u , ↘u , _ | u′ , ↘u′ , _ | Tσ≈ , tσ≈
               rewrite Re-det ↘u ↘u′ = Tσ≈ , tσ≈
  ®El-one-sided N N t∼a                                                               = t∼a
  ®El-one-sided (U j<i eq) (U j′<i eq′) ((A∈ , T∼A) , T≈)
    rewrite Glu-wellfounded-≡ j<i A∈
          | Glu-wellfounded-≡ j′<i A∈                                                 = (A∈ , T∼A) , T≈
  ®El-one-sided (□ A≈B) (□ A≈B′) t∼a                                                  = record
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
  ®El-one-sided {Γ = Γ} {t} {_} {f} {i} (Π iA RT) (Π iA′ RT′) t∼a                     = record
    { t∶T  = t∶T
    ; a∈El = El-one-sided (Π iA RT) (Π iA′ RT′) a∈El
    ; IT   = IT
    ; OT   = OT
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


®-≡ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) (A′≈B′ : A′ ≈ B′ ∈ 𝕌 i) → Γ ⊢ T ®[ i ] A≈B → A ≡ A′ → B ≡ B′ → Γ ⊢ T ®[ i ] A′≈B′
®-≡ A≈B A′≈B′ T∼A refl refl = ®-one-sided A≈B A′≈B′ T∼A

®Π-wf′ : ∀ {i} →
        (iA : ∀ (κ : UMoT) → A [ κ ] ≈ A′ [ κ ] ∈ 𝕌 i)
        (RT : ∀ {a a′} (κ : UMoT) → a ≈ a′ ∈ El i (iA κ) → ΠRT T (ρ [ κ ] ↦ a) T′ (ρ′ [ κ ] ↦ a′) (𝕌 i)) →
        (T∼A : Γ ⊢ T″ ®[ i ] Π iA RT) →
        GluΠ.IT T∼A ∺ Γ ⊢ GluΠ.OT T∼A ∶ Se i
®Π-wf′ iA RT T∼A = {!®⇒ty ? (ΠRel.OT-rel (krip (r-p (⊢rI ?) (s-≈-sym (∘-I ?)))) ? ?)!}
  where open GluΠ T∼A

®-mon : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) → (A≈Bσ : A [ mt σ ] ≈ B [ mt σ ] ∈ 𝕌 i) → Γ ⊢ T ®[ i ] A≈B → Δ ⊢r σ ∶ Γ → Δ ⊢ T [ σ ] ®[ i ] A≈Bσ
®-mon {_} {_} {σ} {_} {T} {Δ} {i} (ne {C} C≈C′) (ne C≈C′σ) (⊢T , rel) ⊢σ = t[σ]-Se ⊢T (⊢r⇒⊢s ⊢σ) , helper
  where helper : Δ′ ⊢r τ ∶ Δ → Δ′ ⊢ sub (sub T σ) τ ≈ Ne⇒Exp (proj₁ (C≈C′σ (map len Δ′) (mt τ))) ∶ Se i
        helper {Δ′} {τ} ⊢τ
          with C≈C′σ (map len Δ′) (mt τ) | C≈C′ (map len Δ′) (mt (σ ∘ τ)) | rel (⊢r-∘ ⊢σ ⊢τ)
        ...  | u , ↘u , _ | u′ , ↘u′ , _ | Tστ≈
             rewrite Dn-comp C (mt σ) (mt τ)
                   | Re-det ↘u ↘u′ = ≈-trans ([∘]-Se ⊢T (⊢r⇒⊢s ⊢σ) (⊢r⇒⊢s ⊢τ)) Tστ≈
®-mon N N T∼A ⊢σ                                                         = ≈-trans ([]-cong-Se′ T∼A (⊢r⇒⊢s ⊢σ)) (N-[] _ (⊢r⇒⊢s ⊢σ))
®-mon (U j<i eq) (U j′<i eq′) T∼A ⊢σ                                     = ≈-trans ([]-cong-Se′ T∼A (⊢r⇒⊢s ⊢σ)) (lift-⊢≈-Se (Se-[] _ (⊢r⇒⊢s ⊢σ)) j<i)
®-mon {_} {_} {σ} {_} {_} {Δ} {i} (□ A≈B) (□ A≈Bσ) T∼A ⊢σ                = record
  { GT   = GT [ σ ； 1 ]
  ; T≈   = ≈-trans ([]-cong-Se′ T≈ (⊢r⇒⊢s ⊢σ)) (□-[] (⊢r⇒⊢s ⊢σ) (®□⇒wf A≈B T∼A))
  ; krip = helper -- ®̄-resp-≈ (A≈B (ins (mt σ ø mt τ) (len Ψs))) (krip Ψs (⊢r-∘ ⊢σ ⊢τ)) ?
  }
  where open Glu□ T∼A
        helper : ∀ Ψs → Δ′ ⊢r τ ∶ Δ → Ψs ++⁺ Δ′ ⊢ GT [ σ ； 1 ] [ τ ； len Ψs ] ®[ i ] A≈Bσ (ins (mt τ) (len Ψs))
        helper {Δ′} {τ} Ψs ⊢τ = ®-≡ (A≈B (ins (mt σ ø mt τ) (len Ψs)))
                                    (A≈Bσ (ins (mt τ) (len Ψs)))
                                    (®̄-resp-≈ (A≈B (ins (mt σ ø mt τ) (len Ψs))) (krip Ψs (⊢r-∘ ⊢σ ⊢τ)) {!!})
                                    {!!}
                                    {!!}
®-mon {_} {_} {σ} (Π iA RT) (Π iA′ RT′) T∼A ⊢σ       = record
  { IT   = IT [ σ ]
  ; OT   = OT [ q σ ]
  ; T≈   = ≈-trans ([]-cong-Se′ T≈ (⊢r⇒⊢s ⊢σ)) (Π-[] (⊢r⇒⊢s ⊢σ) (®Π-wf iA RT T∼A) {!!})
  ; krip = {!!}
  }
  where open GluΠ T∼A


-- ®-mon : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) → Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B → Δ ⊢r σ ∶ Γ → Δ ⊢ t ∶ T ®[ i ] a ∈El A≈B′
