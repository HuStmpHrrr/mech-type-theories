{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Soundness.Properties.LogRel (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Data.Nat
open import Data.Nat.Properties

open import kMLTT.Statics.Properties
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Soundness.LogRel

open import kMLTT.Soundness.Properties.NoFunExt.LogRel


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
