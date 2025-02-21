{-# OPTIONS --without-K --safe #-}

-- Properties of the gluing models that do not rely on functional extensionality
module NonCumulative.Ascribed.Soundness.Properties.NoFunExt.LogRel where

open import Lib

open import NonCumulative.Ascribed.Semantics.Readback
open import NonCumulative.Ascribed.Semantics.Properties.PER.Core
open import NonCumulative.Ascribed.Soundness.LogRel
open import NonCumulative.Ascribed.Statics.Presup
open import NonCumulative.Ascribed.Statics.Misc
open import NonCumulative.Ascribed.Statics.Refl
open import NonCumulative.Ascribed.Statics.CtxEquiv
open import NonCumulative.Ascribed.Statics.Properties
open import NonCumulative.Ascribed.Statics.Properties.Contexts

-----------------------------------------------
-- Properties of the gluing model for natural numbers

®Nat⇒∈Nat : Γ ⊢ t ∶N® a ∈Nat → a ∈′ Nat
®Nat⇒∈Nat (ze t≈)    = ze
®Nat⇒∈Nat (su _ rel) = su (®Nat⇒∈Nat rel)
®Nat⇒∈Nat (ne c∈ _)  = ne c∈

®Nat⇒∶Nat : Γ ⊢ t ∶N® a ∈Nat → ⊢ Γ → Γ ⊢ t ∶[ 0 ] N
®Nat⇒∶Nat (ze t≈) ⊢Γ    = proj₁ (proj₂ (presup-≈ t≈))
®Nat⇒∶Nat (su t≈ _) ⊢Γ  = proj₁ (proj₂ (presup-≈ t≈))
®Nat⇒∶Nat (ne _ rel) ⊢Γ = [I]-inv (proj₁ (proj₂ (presup-≈ (rel (⊢wI ⊢Γ)))))

®Nat-resp-≈ : Γ ⊢ t ∶N® a ∈Nat → Γ ⊢ t ≈ t′ ∶[ 0 ] N →  Γ ⊢ t′ ∶N® a ∈Nat
®Nat-resp-≈ (ze t≈) t≈t′     = ze (≈-trans (≈-sym t≈t′) t≈)
®Nat-resp-≈ (su t≈ t∼a) t≈t′ = su (≈-trans (≈-sym t≈t′) t≈) t∼a
®Nat-resp-≈ (ne c∈ rel) t≈t′ = ne c∈ λ ⊢σ → ≈-trans ([]-cong-N′ (≈-sym t≈t′) (⊢w⇒⊢s ⊢σ)) (rel ⊢σ)

®Nat-resp-⊢≈ : Γ ⊢ t ∶N® a ∈Nat → ⊢ Γ ≈ Δ →  Δ ⊢ t ∶N® a ∈Nat
®Nat-resp-⊢≈ (ze t≈) Γ≈Δ     = ze (ctxeq-≈ Γ≈Δ t≈)
®Nat-resp-⊢≈ (su t≈ t∼a) Γ≈Δ = su (ctxeq-≈ Γ≈Δ t≈) (®Nat-resp-⊢≈ t∼a Γ≈Δ)
®Nat-resp-⊢≈ (ne c∈ rel) Γ≈Δ = ne c∈ (λ ⊢σ → rel (⊢w-resp-⊢≈ʳ ⊢σ (⊢≈-sym Γ≈Δ)))

-- we prove this lemma directly so we do not have to rely on realizability of the PER
-- model which in turn relies on functional extensionality.
®Nat⇒∈Top : Γ ⊢ t ∶N® a ∈Nat → ↓ 0 N a ∈′ Top
®Nat⇒∈Top (ze t≈) ns     = ze , Rze ns , Rze ns
®Nat⇒∈Top (su t≈ t′∼a) ns
  with ®Nat⇒∈Top t′∼a ns
...  | w , ↘w , ↘w′        = su w , Rsu ns ↘w , Rsu ns ↘w′
®Nat⇒∈Top (ne c∈ rel) ns
  with c∈ ns
...  | u , ↘u , ↘u′ = ne u , RN ns ↘u′ , RN ns ↘u′

-- If t and a are related as natural numbers, then t and the readback of a are equivalent up to any weakening.
®Nat⇒≈ : (t∼a : Γ ⊢ t ∶N® a ∈Nat) → Δ ⊢w σ ∶ Γ → Δ ⊢ t [ σ ] ≈ Nf⇒Exp (proj₁ (®Nat⇒∈Top t∼a (len Δ))) ∶[ 0 ] N
®Nat⇒≈ (ze t≈) ⊢σ     = ≈-trans ([]-cong-N′ t≈ (⊢w⇒⊢s ⊢σ)) (ze-[] (⊢w⇒⊢s ⊢σ))
®Nat⇒≈ (su t≈ t′∼a) ⊢σ
  with presup-s (⊢w⇒⊢s ⊢σ)
...  | _ , ⊢Γ         = ≈-trans ([]-cong-N′ t≈ (⊢w⇒⊢s ⊢σ)) (≈-trans (su-[] (⊢w⇒⊢s ⊢σ) (®Nat⇒∶Nat t′∼a ⊢Γ)) (su-cong (®Nat⇒≈ t′∼a ⊢σ)))
®Nat⇒≈ (ne c∈ rel) ⊢σ = rel ⊢σ

®Nat-mon : Γ ⊢ t ∶N® a ∈Nat → Δ ⊢w σ ∶ Γ → Δ ⊢ t [ σ ] ∶N® a ∈Nat
®Nat-mon (ze t≈) ⊢σ                             = ze (≈-trans ([]-cong-N′ t≈ (⊢w⇒⊢s ⊢σ)) (ze-[] (⊢w⇒⊢s ⊢σ)))
®Nat-mon (su t≈ t∼a) ⊢σ                         = su (≈-trans ([]-cong-N′ t≈ ⊢σ′) (su-[] ⊢σ′ (®Nat⇒∶Nat t∼a (proj₂ (presup-s ⊢σ′))))) (®Nat-mon t∼a ⊢σ)
  where ⊢σ′ = ⊢w⇒⊢s ⊢σ
®Nat-mon {_} {t} {_} {Δ} {σ} t∼a@(ne {c} c∈ rel) ⊢σ = ne c∈ helper
  where
    helper : Δ′ ⊢w τ ∶ Δ → Δ′ ⊢ sub (sub t σ) τ ≈ Ne⇒Exp (proj₁ (c∈ (L.length Δ′))) ∶[ 0 ] N
    helper  {Δ′} {τ} ⊢τ
      with c∈ (len Δ′) | c∈ (len Δ′) | rel (⊢w-∘ ⊢σ ⊢τ)
    ... | u , ↘u , _ | u′ , ↘u′ , _ | tστ≈
      rewrite Re-det ↘u ↘u′ = ≈-trans ([∘]-N (®Nat⇒∶Nat t∼a (proj₂ (presup-s (⊢w⇒⊢s ⊢σ)))) (⊢w⇒⊢s ⊢σ) (⊢w⇒⊢s ⊢τ)) tστ≈


----------------------------------
-- Properties of the gluing models

-- If T and A (and B) are related in level i, then T is typed in level i.
®⇒ty : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
       Γ ⊢ T ®[ i ] A≈B →
       -----------------------
       Γ ⊢ T ∶[ 1 + i ] Se i
®⇒ty (ne C≈C′ j≡1+i j′≡1+i) (⊢T , _) = ⊢T
®⇒ty (N i≡0) T® = proj₁ (proj₂ (presup-≈ T®))
®⇒ty (U i≡1+j j≡j′) T® = proj₁ (proj₂ (presup-≈ T®))
®⇒ty (Π i≡maxjk jA RT j≡j′ k≡k′) T® = proj₁ (proj₂ (presup-≈ T≈))
  where open GluΠ T®
®⇒ty (L i≡j+k kA j≡j′ k≡k′) T® = proj₁ (proj₂ (presup-≈ T≈))
  where open GluL T®

-- ® respects type equivalence.
®-resp-≈ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
          Γ ⊢ T ®[ i ] A≈B →
          Γ ⊢ T ≈ T′ ∶[ 1 + i ] Se i →
          -----------------------
          Γ ⊢ T′ ®[ i ] A≈B
®-resp-≈ (ne C≈C′ j≡1+i j′≡1+i) (⊢T , rel) T≈T′ = (proj₁ (proj₂ (proj₂ (presup-≈ T≈T′)))) , λ ⊢σ → ≈-trans ([]-cong-Se′ (≈-sym T≈T′) (⊢w⇒⊢s ⊢σ)) (rel ⊢σ)
®-resp-≈ (N i≡0) T® T≈T′ = ≈-trans (≈-sym T≈T′) T®
®-resp-≈ (U i≡1+j j≡j′) T® T≈T′ = ≈-trans (≈-sym T≈T′) T®
®-resp-≈ (Π i≡maxjk jA RT j≡j′ k≡k′) T® T≈T′ = record
  { IT = IT
  ; OT = OT
  ; ⊢IT = ⊢IT
  ; ⊢OT = ⊢OT
  ; T≈ = ≈-trans (≈-sym T≈T′) T≈
  ; krip = krip
  }
  where open GluΠ T®
®-resp-≈ (L i≡j+k kA j≡j′ k≡k′) T® T≈T′ = record
  { UT = UT
  ; ⊢UT = ⊢UT
  ; T≈ = ≈-trans (≈-sym T≈T′) T≈
  ; krip = krip
  }
  where open GluL T®

-- ®El respects type equivalence.
®El-resp-T≈ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
              Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
              Γ ⊢ T ≈ T′ ∶[ 1 + i ] Se i →
              ---------------------------
              Γ ⊢ t ∶ T′ ®[ i ] a ∈El A≈B
®El-resp-T≈ (ne C≈C′ j≡1+i j′≡1+i) (ne c≈c' j≡i j≡′i , glu) T≈T′ =
  (ne c≈c' j≡i j≡′i) , record
  { t∶T = conv t∶T T≈T′
  ; ⊢T = proj₁ (proj₂ (proj₂ (presup-≈ T≈T′)))
  ; krip = λ ⊢σ → let Tσ≈ , tσ≈ = krip ⊢σ
                      TT′σ = []-cong-Se′ T≈T′ (⊢w⇒⊢s ⊢σ)
                  in ≈-trans (≈-sym TT′σ) Tσ≈ , ≈-conv tσ≈ TT′σ
  }
  where open GluNe glu
®El-resp-T≈ N′ (t∶N® , T≈N) T≈T′ = t∶N® , ≈-trans (≈-sym T≈T′) T≈N
®El-resp-T≈ (U i≡1+j j≡j′) t® T≈T′ = record
  { t∶T = conv t∶T T≈T′
  ; T≈  = ≈-trans (≈-sym T≈T′) T≈
  ; A∈𝕌 = A∈𝕌
  ; rel = rel
  }
  where open GluU t®
®El-resp-T≈ (Π i≡maxjk jA RT j≡j′ k≡k′) t® T≈T′ = record
  { t∶T  = conv t∶T T≈T′
  ; a∈El = a∈El
  ; IT   = IT
  ; OT   = OT
  ; ⊢IT  = ⊢IT
  ; ⊢OT  = ⊢OT
  ; T≈   = ≈-trans (≈-sym T≈T′) T≈
  ; krip = krip
  }
  where open GluΛ t®
®El-resp-T≈ (L i≡j+k kA j≡j′ k≡k′) t® T≈T′ = record
  { t∶T  = conv t∶T T≈T′
  ; UT   = UT
  ; ⊢UT  = ⊢UT
  ; a∈El = a∈El
  ; T≈   = ≈-trans (≈-sym T≈T′) T≈
  ; krip = krip
  }
  where open Glul t®

®-resp-⊢≈ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
            Γ ⊢ T ®[ i ] A≈B →
            ⊢ Γ ≈ Δ →
            ---------------------------
            Δ ⊢ T ®[ i ] A≈B
®-resp-⊢≈ (ne C≈C′ j≡1+i j′≡1+i) (⊢T , krip) Γ≈Δ = (ctxeq-tm Γ≈Δ ⊢T) , λ ⊢σ → krip (⊢w-resp-⊢≈ʳ ⊢σ (⊢≈-sym Γ≈Δ))
®-resp-⊢≈ (N i≡0) T® Γ≈Δ = ctxeq-≈ Γ≈Δ T®
®-resp-⊢≈ (U i≡1+j j≡j′) T® Γ≈Δ = ctxeq-≈ Γ≈Δ T®
®-resp-⊢≈ (Π eq jA RT j≡j′ k≡k′) T® Γ≈Δ = record
  { IT = IT
  ; OT = OT
  ; ⊢IT = ctxeq-tm Γ≈Δ ⊢IT
  ; ⊢OT = ctxeq-tm (∷-cong Γ≈Δ ⊢IT (ctxeq-tm Γ≈Δ ⊢IT) (≈-refl ⊢IT) (ctxeq-≈ Γ≈Δ (≈-refl ⊢IT))) ⊢OT
  ; T≈ = ctxeq-≈ Γ≈Δ T≈
  ; krip = λ ⊢σ → krip ((⊢w-resp-⊢≈ʳ ⊢σ (⊢≈-sym Γ≈Δ)))
  }
  where open GluΠ T®
®-resp-⊢≈ (L eq i≡j+k j≡j′ k≡k′) T® Γ≈Δ = record
  { UT = UT
  ; ⊢UT = ctxeq-tm Γ≈Δ ⊢UT
  ; T≈ = ctxeq-≈ Γ≈Δ T≈
  ; krip = λ ⊢σ → krip (⊢w-resp-⊢≈ʳ ⊢σ (⊢≈-sym Γ≈Δ))
  }
  where open GluL T®

-- If t and a are related, then t is well-typed.
®El⇒tm : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
           Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
           ---------------------------
           Γ ⊢ t ∶[ i ] T
®El⇒tm (ne′ _) (ne _ refl _ , glu) = GluNe.t∶T glu
®El⇒tm N′ (t®Nat , T≈N) = conv (®Nat⇒∶Nat t®Nat (proj₁ (presup-≈ T≈N))) (≈-sym T≈N)
®El⇒tm (U _ _) t® = GluU.t∶T t®
®El⇒tm (Π _ _ _ _ _) t® = GluΛ.t∶T t®
®El⇒tm (L _ _ _ _) t® = Glul.t∶T t®