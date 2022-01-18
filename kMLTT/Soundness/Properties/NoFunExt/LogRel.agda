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

®⇒ty : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) → Γ ⊢ T ®[ i ] A≈B → Γ ⊢ T ∶ Se i
®⇒ty (ne C≈C′) (⊢T , _)  = ⊢T
®⇒ty N T∼A          = proj₁ (proj₂ (presup-≈ T∼A))
®⇒ty (U j<i eq) T∼A = proj₁ (proj₂ (presup-≈ T∼A))
®⇒ty (□ A≈B) T∼A    = proj₁ (proj₂ (presup-≈ T≈))
  where open Glu□ T∼A
®⇒ty (Π iA RT) T∼A  = proj₁ (proj₂ (presup-≈ T≈))
  where open GluΠ T∼A

®̄-resp-≈ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) → Γ ⊢ T ®[ i ] A≈B → Γ ⊢ T ≈ T′ ∶ Se i → Γ ⊢ T′ ®[ i ] A≈B
®̄-resp-≈ (ne C≈C′) (⊢T , rel) T≈T′ = proj₁ (proj₂ (proj₂ (presup-≈ T≈T′))) , λ ⊢σ → ≈-trans ([]-cong-Se′ (≈-sym T≈T′) (⊢r⇒⊢s ⊢σ)) (rel ⊢σ)
®̄-resp-≈ N T∼A T≈T′                = ≈-trans (≈-sym T≈T′) T∼A
®̄-resp-≈ (U j<i eq) T∼A T≈T′       = ≈-trans (≈-sym T≈T′) T∼A
®̄-resp-≈ (□ A≈B) T∼A T≈T′          = record
  { GT   = GT
  ; T≈   = ≈-trans (≈-sym T≈T′) T≈
  ; krip = krip
  }
  where open Glu□ T∼A
®̄-resp-≈ (Π iA RT) T∼A T≈T′        = record
  { IT   = IT
  ; OT   = OT
  ; T≈   = ≈-trans (≈-sym T≈T′) T≈
  ; krip = krip
  }
  where open GluΠ T∼A

®El-resp-T≈ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) → Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B → Γ ⊢ T ≈ T′ ∶ Se i → Γ ⊢ t ∶ T′ ®[ i ] a ∈El A≈B
®El-resp-T≈ (ne C≈C′) (ne c≈c′ , ⊢t , _ , rel) T≈T′ = ne c≈c′ , conv ⊢t T≈T′ , proj₁ (proj₂ (proj₂ (presup-≈ T≈T′)))
                                                    , λ ⊢σ → let Tσ≈ , tσ≈ = rel ⊢σ
                                                                 TT′σ = []-cong-Se′ T≈T′ (⊢r⇒⊢s ⊢σ)
                                                             in ≈-trans (≈-sym TT′σ) Tσ≈
                                                              , ≈-conv tσ≈ TT′σ
®El-resp-T≈ N (t∼a , T≈N) T≈T′                      = t∼a , ≈-trans (≈-sym T≈T′) T≈N
®El-resp-T≈ (U j<i eq) (t∼a , T≈) T≈T′              = t∼a , ≈-trans (≈-sym T≈T′) T≈
®El-resp-T≈ (□ A≈B) t∼a T≈T′                        = record
  { GT   = GT
  ; t∶T  = conv t∶T T≈T′
  ; a∈El = a∈El
  ; T≈   = ≈-trans (≈-sym T≈T′) T≈
  ; krip = krip
  }
  where open Glubox t∼a
®El-resp-T≈ (Π iA RT) t∼a T≈T′                      = record
  { t∶T  = conv t∶T T≈T′
  ; a∈El = a∈El
  ; IT   = IT
  ; OT   = OT
  ; T≈   = ≈-trans (≈-sym T≈T′) T≈
  ; krip = krip
  }
  where open GluΛ t∼a

®□⇒wf : ∀ {i} (A≈B : (κ : UMoT) → A [ κ ] ≈ B [ κ ] ∈ 𝕌 i) (T∼A : Γ ⊢ T ®[ i ] □ A≈B) → [] ∷⁺ Γ ⊢ Glu□.GT T∼A ∶ Se i
®□⇒wf A≈B T∼A = [I；1]-inv (®⇒ty (A≈B (ins (mt I) 1)) (krip L.[ [] ] (⊢rI (proj₁ (presup-tm (®⇒ty (□ A≈B) T∼A))))))
  where open Glu□ T∼A

®Π-wf : ∀ {i} →
        (iA : ∀ (κ : UMoT) → A [ κ ] ≈ A′ [ κ ] ∈ 𝕌 i)
        (RT : ∀ {a a′} (κ : UMoT) → a ≈ a′ ∈ El i (iA κ) → ΠRT T (ρ [ κ ] ↦ a) T′ (ρ′ [ κ ] ↦ a′) (𝕌 i)) →
        (T∼A : Γ ⊢ T″ ®[ i ] Π iA RT) →
        Γ ⊢ GluΠ.IT T∼A ∶ Se i
®Π-wf iA RT T∼A = [I]-inv (®⇒ty (iA (mt I)) (ΠRel.IT-rel (krip (⊢rI (proj₁ (presup-tm (®⇒ty (Π iA RT) T∼A)))))))
  where open GluΠ T∼A
