{-# OPTIONS --without-K --safe #-}

module kMLTT.Soundness.Properties.NoFunExt.LogRel where

open import Lib

open import kMLTT.Statics.Properties
open import kMLTT.Soundness.LogRel


®Nat⇒∈Nat : Γ ⊢ t ∶N® a ∈Nat → a ∈′ Nat
®Nat⇒∈Nat (ze t≈)    = ze
®Nat⇒∈Nat (su _ rel) = su (®Nat⇒∈Nat rel)
®Nat⇒∈Nat (ne c∈ _)  = ne c∈

®Nat⇒∶Nat : Γ ⊢ t ∶N® a ∈Nat → ⊢ Γ → Γ ⊢ t ∶ N
®Nat⇒∶Nat (ze t≈) ⊢Γ    = proj₁ (proj₂ (presup-≈ t≈))
®Nat⇒∶Nat (su t≈ _) ⊢Γ  = proj₁ (proj₂ (presup-≈ t≈))
®Nat⇒∶Nat (ne _ rel) ⊢Γ = [I]-inv (proj₁ (proj₂ (presup-≈ (rel (⊢rI ⊢Γ)))))

®Nat-resp-≈ : Γ ⊢ t ∶N® a ∈Nat → Γ ⊢ t ≈ t′ ∶ N →  Γ ⊢ t′ ∶N® a ∈Nat
®Nat-resp-≈ (ze t≈) t≈t′     = ze (≈-trans (≈-sym t≈t′) t≈)
®Nat-resp-≈ (su t≈ t∼a) t≈t′ = su (≈-trans (≈-sym t≈t′) t≈) t∼a
®Nat-resp-≈ (ne c∈ rel) t≈t′ = ne c∈ λ ⊢σ → ≈-trans ([]-cong-N′ (≈-sym t≈t′) (⊢r⇒⊢s ⊢σ)) (rel ⊢σ)

®⇒ty : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
       Γ ⊢ T ®[ i ] A≈B →
       -----------------------
       Γ ⊢ T
®⇒ty (ne C≈C′) (⊢T , _)   = ⊢T
®⇒ty N (_ , T∼A)          = -, proj₁ (proj₂ (presup-≈ T∼A))
®⇒ty (U j<i eq) (_ , T∼A) = -, proj₁ (proj₂ (presup-≈ T∼A))
®⇒ty (□ A≈B) T∼A          = -, proj₁ (proj₂ (presup-≈ (proj₂ T≈)))
  where open Glu□ T∼A
®⇒ty (Π iA RT) T∼A        = -, proj₁ (proj₂ (presup-≈ (proj₂ T≈)))
  where open GluΠ T∼A

®̄-resp-≈ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
          Γ ⊢ T ®[ i ] A≈B →
          Γ ⊢ T ≈ T′ →
          -----------------------
          Γ ⊢ T′ ®[ i ] A≈B
®̄-resp-≈ (ne C≈C′) (⊢T , rel) (_ , T≈T′) = (-, proj₁ (proj₂ (proj₂ (presup-≈ T≈T′)))) , λ ⊢σ → -, ≈-trans (lift-⊢≈-Se-max ([]-cong-Se′ (≈-sym T≈T′) (⊢r⇒⊢s ⊢σ))) (lift-⊢≈-Se-max′ (proj₂ (rel ⊢σ)))
®̄-resp-≈ N (_ , T∼A) (_ , T≈T′)          = -, ≈-trans (lift-⊢≈-Se-max (≈-sym T≈T′)) (lift-⊢≈-Se-max′ T∼A)
®̄-resp-≈ (U j<i eq) (_ , T∼A) (_ , T≈T′) = -, ≈-trans (lift-⊢≈-Se-max (≈-sym T≈T′)) (lift-⊢≈-Se-max′ T∼A)
®̄-resp-≈ (□ A≈B) T∼A (_ , T≈T′)          = record
  { GT   = GT
  ; T≈   = -, ≈-trans (lift-⊢≈-Se-max (≈-sym T≈T′)) (lift-⊢≈-Se-max′ (proj₂ T≈))
  ; krip = krip
  }
  where open Glu□ T∼A
®̄-resp-≈ (Π iA RT) T∼A (_ , T≈T′)        = record
  { IT   = IT
  ; OT   = OT
  ; ⊢OT  = ⊢OT
  ; T≈   = -, ≈-trans (lift-⊢≈-Se-max (≈-sym T≈T′)) (lift-⊢≈-Se-max′ (proj₂ T≈))
  ; krip = krip
  }
  where open GluΠ T∼A

®El-resp-T≈ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
              Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
              Γ ⊢ T ≈ T′ →
              ---------------------------
              Γ ⊢ t ∶ T′ ®[ i ] a ∈El A≈B
®El-resp-T≈ (ne C≈C′) (ne c∈ , ⊢t , _ , rel) (_ , T≈T′) = ne c∈ , conv ⊢t T≈T′ , (-, proj₁ (proj₂ (proj₂ (presup-≈ T≈T′))))
                                                        , λ ⊢σ → let (_ , Tσ≈) , tσ≈ = rel ⊢σ
                                                                     TT′σ = []-cong-Se′ T≈T′ (⊢r⇒⊢s ⊢σ)
                                                                 in (-, ≈-trans (lift-⊢≈-Se-max (≈-sym TT′σ)) (lift-⊢≈-Se-max′ Tσ≈))
                                                                  , ≈-conv tσ≈ TT′σ
®El-resp-T≈ N (t∼a , _ , T≈N) (_ , T≈T′)                = t∼a , -, ≈-trans (lift-⊢≈-Se-max (≈-sym T≈T′)) (lift-⊢≈-Se-max′ T≈N)
®El-resp-T≈ (U j<i eq) (t∼a , _ , T≈) (_ , T≈T′)        = t∼a , -, ≈-trans (lift-⊢≈-Se-max (≈-sym T≈T′)) (lift-⊢≈-Se-max′ T≈)
®El-resp-T≈ (□ A≈B) t∼a (_ , T≈T′)                      = record
  { GT   = GT
  ; t∶T  = conv t∶T T≈T′
  ; a∈El = a∈El
  ; T≈   = -, ≈-trans (lift-⊢≈-Se-max (≈-sym T≈T′)) (lift-⊢≈-Se-max′ (proj₂ T≈))
  ; krip = krip
  }
  where open Glubox t∼a
®El-resp-T≈ (Π iA RT) t∼a (_ , T≈T′)                    = record
  { t∶T  = conv t∶T T≈T′
  ; a∈El = a∈El
  ; IT   = IT
  ; OT   = OT
  ; ⊢OT  = ⊢OT
  ; T≈   = -, ≈-trans (lift-⊢≈-Se-max (≈-sym T≈T′)) (lift-⊢≈-Se-max′ (proj₂ T≈))
  ; krip = krip
  }
  where open GluΛ t∼a

®□⇒wf : ∀ {i} (A≈B : (κ : UMoT) → A [ κ ] ≈ B [ κ ] ∈ 𝕌 i) (T∼A : Γ ⊢ T ®[ i ] □ A≈B) → [] ∷⁺ Γ ⊢ Glu□.GT T∼A
®□⇒wf A≈B T∼A = -, [I；1]-inv (proj₂ (®⇒ty (A≈B (ins (mt I) 1)) (krip L.[ [] ] (⊢rI (proj₁ (presup-tm (proj₂ (®⇒ty (□ A≈B) T∼A))))))))
  where open Glu□ T∼A

®Π-wf : ∀ {i} →
        (iA : ∀ (κ : UMoT) → A [ κ ] ≈ A′ [ κ ] ∈ 𝕌 i)
        (RT : ∀ {a a′} (κ : UMoT) → a ≈ a′ ∈ El i (iA κ) → ΠRT T (ρ [ κ ] ↦ a) T′ (ρ′ [ κ ] ↦ a′) (𝕌 i)) →
        (T∼A : Γ ⊢ T″ ®[ i ] Π iA RT) →
        Γ ⊢ GluΠ.IT T∼A
®Π-wf iA RT T∼A = -, [I]-inv (proj₂ (®⇒ty (iA (mt I)) (ΠRel.IT-rel (krip (⊢rI (proj₁ (presup-tm (proj₂ (®⇒ty (Π iA RT) T∼A)))))))))
  where open GluΠ T∼A
