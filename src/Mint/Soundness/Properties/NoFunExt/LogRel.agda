{-# OPTIONS --without-K --safe #-}

-- Properties of the gluing models that do not rely on functional extensionality
module Mint.Soundness.Properties.NoFunExt.LogRel where

open import Lib

open import Mint.Statics.Properties
open import Mint.Semantics.Readback
open import Mint.Soundness.LogRel

-----------------------------------------------
-- Properties of the gluing model for natural numbers

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

®Nat-resp-⊢≈ : Γ ⊢ t ∶N® a ∈Nat → ⊢ Γ ≈ Δ →  Δ ⊢ t ∶N® a ∈Nat
®Nat-resp-⊢≈ (ze t≈) Γ≈Δ     = ze (ctxeq-≈ Γ≈Δ t≈)
®Nat-resp-⊢≈ (su t≈ t∼a) Γ≈Δ = su (ctxeq-≈ Γ≈Δ t≈) (®Nat-resp-⊢≈ t∼a Γ≈Δ)
®Nat-resp-⊢≈ (ne c∈ rel) Γ≈Δ = ne c∈ (λ ⊢σ → rel (⊢r-resp-⊢≈ʳ ⊢σ (⊢≈-sym Γ≈Δ)))

-- we prove this lemma directly so we do not have to rely on realizability of the PER
-- model which in turn relies on functional extensionality.
®Nat⇒∈Top : Γ ⊢ t ∶N® a ∈Nat → ↓ N a ∈′ Top
®Nat⇒∈Top (ze t≈) ns κ     = ze , Rze ns , Rze ns
®Nat⇒∈Top (su t≈ t′∼a) ns κ
  with ®Nat⇒∈Top t′∼a ns κ
...  | w , ↘w , ↘w′        = su w , Rsu ns ↘w , Rsu ns ↘w′
®Nat⇒∈Top (ne c∈ rel) ns κ
  with c∈ ns κ
...  | u , ↘u , ↘u′ = ne u , RN ns ↘u′ , RN ns ↘u′

-- If t and a are related as natural numbers, then t and the readback of a are equivalent up to any restricted weakening.
®Nat⇒≈ : (t∼a : Γ ⊢ t ∶N® a ∈Nat) → Δ ⊢r σ ∶ Γ → Δ ⊢ t [ σ ] ≈ Nf⇒Exp (proj₁ (®Nat⇒∈Top t∼a (map len Δ) (mt σ))) ∶ N
®Nat⇒≈ (ze t≈) ⊢σ     = ≈-trans ([]-cong-N′ t≈ (⊢r⇒⊢s ⊢σ)) (ze-[] (⊢r⇒⊢s ⊢σ))
®Nat⇒≈ (su t≈ t′∼a) ⊢σ
  with presup-s (⊢r⇒⊢s ⊢σ)
...  | _ , ⊢Γ         = ≈-trans ([]-cong-N′ t≈ (⊢r⇒⊢s ⊢σ)) (≈-trans (su-[] (⊢r⇒⊢s ⊢σ) (®Nat⇒∶Nat t′∼a ⊢Γ)) (su-cong (®Nat⇒≈ t′∼a ⊢σ)))
®Nat⇒≈ (ne c∈ rel) ⊢σ = rel ⊢σ

----------------------------------
-- Properties of the gluing models

-- If T and A (and B) are related in level i, then T is typed in level i.
®⇒ty : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
       Γ ⊢ T ®[ i ] A≈B →
       -----------------------
       Γ ⊢ T ∶ Se i
®⇒ty (ne C≈C′) (⊢T , _)  = ⊢T
®⇒ty N T∼A          = proj₁ (proj₂ (presup-≈ T∼A))
®⇒ty (U j<i eq) T∼A = proj₁ (proj₂ (presup-≈ T∼A))
®⇒ty (□ A≈B) T∼A    = proj₁ (proj₂ (presup-≈ T≈))
  where open Glu□ T∼A
®⇒ty (Π iA RT) T∼A  = proj₁ (proj₂ (presup-≈ T≈))
  where open GluΠ T∼A

-- ® respects type equivalence.
®-resp-≈ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
          Γ ⊢ T ®[ i ] A≈B →
          Γ ⊢ T ≈ T′ ∶ Se i →
          -----------------------
          Γ ⊢ T′ ®[ i ] A≈B
®-resp-≈ (ne C≈C′) (⊢T , rel) T≈T′ = proj₁ (proj₂ (proj₂ (presup-≈ T≈T′))) , λ ⊢σ → ≈-trans ([]-cong-Se′ (≈-sym T≈T′) (⊢r⇒⊢s ⊢σ)) (rel ⊢σ)
®-resp-≈ N T∼A T≈T′                = ≈-trans (≈-sym T≈T′) T∼A
®-resp-≈ (U j<i eq) T∼A T≈T′       = ≈-trans (≈-sym T≈T′) T∼A
®-resp-≈ (□ A≈B) T∼A T≈T′          = record
  { GT   = GT
  ; T≈   = ≈-trans (≈-sym T≈T′) T≈
  ; krip = krip
  }
  where open Glu□ T∼A
®-resp-≈ (Π iA RT) T∼A T≈T′        = record
  { IT   = IT
  ; OT   = OT
  ; ⊢OT  = ⊢OT
  ; T≈   = ≈-trans (≈-sym T≈T′) T≈
  ; krip = krip
  }
  where open GluΠ T∼A

-- ®El respects type equivalence.
®El-resp-T≈ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
              Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
              Γ ⊢ T ≈ T′ ∶ Se i →
              ---------------------------
              Γ ⊢ t ∶ T′ ®[ i ] a ∈El A≈B
®El-resp-T≈ (ne C≈C′) (ne c∈ , glu) T≈T′ = ne c∈ , record
  { t∶T  = conv t∶T T≈T′
  ; ⊢T   = proj₁ (proj₂ (proj₂ (presup-≈ T≈T′)))
  ; krip = λ ⊢σ →
    let Tσ≈ , tσ≈ = krip ⊢σ
        TT′σ = []-cong-Se′ T≈T′ (⊢r⇒⊢s ⊢σ)
    in ≈-trans (≈-sym TT′σ) Tσ≈ , ≈-conv tσ≈ TT′σ
  }
  where open GluNe glu
®El-resp-T≈ N (t∼a , T≈N) T≈T′           = t∼a , ≈-trans (≈-sym T≈T′) T≈N
®El-resp-T≈ (U j<i eq) t∼a T≈T′          = record
  { t∶T = conv t∶T T≈T′
  ; T≈  = ≈-trans (≈-sym T≈T′) T≈
  ; A∈𝕌 = A∈𝕌
  ; rel = rel
  }
  where open GluU t∼a
®El-resp-T≈ (□ A≈B) t∼a T≈T′             = record
  { GT   = GT
  ; t∶T  = conv t∶T T≈T′
  ; a∈El = a∈El
  ; T≈   = ≈-trans (≈-sym T≈T′) T≈
  ; krip = krip
  }
  where open Glubox t∼a
®El-resp-T≈ (Π iA RT) t∼a T≈T′           = record
  { t∶T  = conv t∶T T≈T′
  ; a∈El = a∈El
  ; IT   = IT
  ; OT   = OT
  ; ⊢OT  = ⊢OT
  ; T≈   = ≈-trans (≈-sym T≈T′) T≈
  ; krip = krip
  }
  where open GluΛ t∼a

®□⇒wf : ∀ {i} (A≈B : (κ : UMoT) → A [ κ ] ≈ B [ κ ] ∈ 𝕌 i) (T∼A : Γ ⊢ T ®[ i ] □ A≈B) → [] ∷⁺ Γ ⊢ Glu□.GT T∼A ∶ Se i
®□⇒wf A≈B T∼A = [I；1]-inv (®⇒ty (A≈B (ins (mt I) 1)) (krip L.[ [] ] (⊢κ (proj₁ (presup-≈ T≈))) (⊢rI (proj₁ (presup-tm (®⇒ty (□ A≈B) T∼A))))))
  where open Glu□ T∼A

®Π-wf : ∀ {i} →
        (iA : ∀ (κ : UMoT) → A [ κ ] ≈ A′ [ κ ] ∈ 𝕌 i)
        (RT : ∀ {a a′} (κ : UMoT) → a ≈ a′ ∈ El i (iA κ) → ΠRT T (ρ [ κ ] ↦ a) T′ (ρ′ [ κ ] ↦ a′) (𝕌 i)) →
        (T∼A : Γ ⊢ T″ ®[ i ] Π iA RT) →
        Γ ⊢ GluΠ.IT T∼A ∶ Se i
®Π-wf iA RT T∼A = [I]-inv (®⇒ty (iA (mt I)) (ΠRel.IT-rel (krip (⊢rI (proj₁ (presup-tm (®⇒ty (Π iA RT) T∼A)))))))
  where open GluΠ T∼A

-- ® respects context stack equivalence.
®-resp-⊢≈ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
            Γ ⊢ T ®[ i ] A≈B →
            ⊢ Γ ≈ Δ →
            ---------------------------
            Δ ⊢ T ®[ i ] A≈B
®-resp-⊢≈ (ne C≈C′) (⊢T , rel) Γ≈Δ  = ctxeq-tm Γ≈Δ ⊢T , λ ⊢σ → rel (⊢r-resp-⊢≈ʳ ⊢σ (⊢≈-sym Γ≈Δ))
®-resp-⊢≈ N T∼A Γ≈Δ          = ctxeq-≈ Γ≈Δ T∼A
®-resp-⊢≈ (U j<i eq) T∼A Γ≈Δ = ctxeq-≈ Γ≈Δ T∼A
®-resp-⊢≈ (□ A≈B) T∼A Γ≈Δ    = record
  { GT   = GT
  ; T≈   = ctxeq-≈ Γ≈Δ T≈
  ; krip = λ Ψs ⊢ΨsΔ ⊢σ → krip Ψs ⊢ΨsΔ (⊢r-resp-⊢≈ʳ ⊢σ (⊢≈-sym Γ≈Δ))
  }
  where open Glu□ T∼A
®-resp-⊢≈ (Π iA RT) T∼A Γ≈Δ  = record
  { IT   = IT
  ; OT   = OT
  ; ⊢OT  = ctxeq-tm (∺-cong Γ≈Δ (≈-refl ⊢IT)) ⊢OT
  ; T≈   = ctxeq-≈ Γ≈Δ T≈
  ; krip = λ ⊢σ → krip (⊢r-resp-⊢≈ʳ ⊢σ (⊢≈-sym Γ≈Δ))
  }
  where open GluΠ T∼A
        ⊢IT = ®Π-wf iA RT T∼A
