{-# OPTIONS --without-K --safe #-}

-- Properties of the gluing models that do not rely on functional extensionality
module MLTT.Soundness.Properties.NoFunExt.LogRel where

open import Lib

open import MLTT.Statics.Properties
open import MLTT.Semantics.Readback
open import MLTT.Soundness.LogRel

-----------------------------------------------
-- Properties of the gluing model for natural numbers

®Nat⇒∈Nat : Γ ⊢ t ∶N® a ∈Nat → a ∈′ Nat
®Nat⇒∈Nat (ze t≈)    = ze
®Nat⇒∈Nat (su _ rel) = su (®Nat⇒∈Nat rel)
®Nat⇒∈Nat (ne c∈ _)  = ne c∈

®Nat⇒∶Nat : Γ ⊢ t ∶N® a ∈Nat → ⊢ Γ → Γ ⊢ t ∶ N
®Nat⇒∶Nat (ze t≈) ⊢Γ    = proj₁ (proj₂ (presup-≈ t≈))
®Nat⇒∶Nat (su t≈ _) ⊢Γ  = proj₁ (proj₂ (presup-≈ t≈))
®Nat⇒∶Nat (ne _ rel) ⊢Γ = [I]-inv (proj₁ (proj₂ (presup-≈ (rel (⊢wI ⊢Γ)))))

®Nat-resp-≈ : Γ ⊢ t ∶N® a ∈Nat → Γ ⊢ t ≈ t′ ∶ N →  Γ ⊢ t′ ∶N® a ∈Nat
®Nat-resp-≈ (ze t≈) t≈t′     = ze (≈-trans (≈-sym t≈t′) t≈)
®Nat-resp-≈ (su t≈ t∼a) t≈t′ = su (≈-trans (≈-sym t≈t′) t≈) t∼a
®Nat-resp-≈ (ne c∈ rel) t≈t′ = ne c∈ λ ⊢σ → ≈-trans ([]-cong-N′ (≈-sym t≈t′) (⊢w⇒⊢s ⊢σ)) (rel ⊢σ)

®Nat-resp-⊢≈ : Γ ⊢ t ∶N® a ∈Nat → ⊢ Γ ≈ Δ →  Δ ⊢ t ∶N® a ∈Nat
®Nat-resp-⊢≈ (ze t≈) Γ≈Δ     = ze (ctxeq-≈ Γ≈Δ t≈)
®Nat-resp-⊢≈ (su t≈ t∼a) Γ≈Δ = su (ctxeq-≈ Γ≈Δ t≈) (®Nat-resp-⊢≈ t∼a Γ≈Δ)
®Nat-resp-⊢≈ (ne c∈ rel) Γ≈Δ = ne c∈ (λ ⊢σ → rel (⊢w-resp-⊢≈ʳ ⊢σ (⊢≈-sym Γ≈Δ)))

-- we prove this lemma directly so we do not have to rely on realizability of the PER
-- model which in turn relies on functional extensionality.
®Nat⇒∈Top : Γ ⊢ t ∶N® a ∈Nat → ↓ N a ∈′ Top
®Nat⇒∈Top (ze t≈) ns     = ze , Rze ns , Rze ns
®Nat⇒∈Top (su t≈ t′∼a) ns
  with ®Nat⇒∈Top t′∼a ns
...  | w , ↘w , ↘w′        = su w , Rsu ns ↘w , Rsu ns ↘w′
®Nat⇒∈Top (ne c∈ rel) ns
  with c∈ ns
...  | u , ↘u , ↘u′ = ne u , RN ns ↘u′ , RN ns ↘u′

-- If t and a are related as natural numbers, then t and the readback of a are equivalent up to any weakening.
®Nat⇒≈ : (t∼a : Γ ⊢ t ∶N® a ∈Nat) → Δ ⊢w σ ∶ Γ → Δ ⊢ t [ σ ] ≈ Nf⇒Exp (proj₁ (®Nat⇒∈Top t∼a (len Δ))) ∶ N
®Nat⇒≈ (ze t≈) ⊢σ     = ≈-trans ([]-cong-N′ t≈ (⊢w⇒⊢s ⊢σ)) (ze-[] (⊢w⇒⊢s ⊢σ))
®Nat⇒≈ (su t≈ t′∼a) ⊢σ
  with presup-s (⊢w⇒⊢s ⊢σ)
...  | _ , ⊢Γ         = ≈-trans ([]-cong-N′ t≈ (⊢w⇒⊢s ⊢σ)) (≈-trans (su-[] (⊢w⇒⊢s ⊢σ) (®Nat⇒∶Nat t′∼a ⊢Γ)) (su-cong (®Nat⇒≈ t′∼a ⊢σ)))
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
®⇒ty (Π iA RT) T∼A  = proj₁ (proj₂ (presup-≈ T≈))
  where open GluΠ T∼A

-- ® respects type equivalence.
®-resp-≈ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
          Γ ⊢ T ®[ i ] A≈B →
          Γ ⊢ T ≈ T′ ∶ Se i →
          -----------------------
          Γ ⊢ T′ ®[ i ] A≈B
®-resp-≈ (ne C≈C′) (⊢T , rel) T≈T′ = proj₁ (proj₂ (proj₂ (presup-≈ T≈T′))) , λ ⊢σ → ≈-trans ([]-cong-Se′ (≈-sym T≈T′) (⊢w⇒⊢s ⊢σ)) (rel ⊢σ)
®-resp-≈ N T∼A T≈T′                = ≈-trans (≈-sym T≈T′) T∼A
®-resp-≈ (U j<i eq) T∼A T≈T′       = ≈-trans (≈-sym T≈T′) T∼A
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
        TT′σ = []-cong-Se′ T≈T′ (⊢w⇒⊢s ⊢σ)
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

®Π-wf : ∀ {i} →
        (iA : A ≈ A′ ∈ 𝕌 i)
        (RT : ∀ {a a′} → a ≈ a′ ∈ El i iA → ΠRT T (ρ ↦ a) T′ (ρ′ ↦ a′) (𝕌 i)) →
        (T∼A : Γ ⊢ T″ ®[ i ] Π iA RT) →
        Γ ⊢ GluΠ.IT T∼A ∶ Se i
®Π-wf iA RT T∼A = [I]-inv (®⇒ty iA (ΠRel.IT-rel (krip (⊢wI (proj₁ (presup-tm (®⇒ty (Π iA RT) T∼A)))))))
  where open GluΠ T∼A

-- ® respects context stack equivalence.
®-resp-⊢≈ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
            Γ ⊢ T ®[ i ] A≈B →
            ⊢ Γ ≈ Δ →
            ---------------------------
            Δ ⊢ T ®[ i ] A≈B
®-resp-⊢≈ (ne C≈C′) (⊢T , rel) Γ≈Δ  = ctxeq-tm Γ≈Δ ⊢T , λ ⊢σ → rel (⊢w-resp-⊢≈ʳ ⊢σ (⊢≈-sym Γ≈Δ))
®-resp-⊢≈ N T∼A Γ≈Δ          = ctxeq-≈ Γ≈Δ T∼A
®-resp-⊢≈ (U j<i eq) T∼A Γ≈Δ = ctxeq-≈ Γ≈Δ T∼A
®-resp-⊢≈ (Π iA RT) T∼A Γ≈Δ  = record
  { IT   = IT
  ; OT   = OT
  ; ⊢OT  = ctxeq-tm (∷-cong Γ≈Δ (≈-refl ⊢IT)) ⊢OT
  ; T≈   = ctxeq-≈ Γ≈Δ T≈
  ; krip = λ ⊢σ → krip (⊢w-resp-⊢≈ʳ ⊢σ (⊢≈-sym Γ≈Δ))
  }
  where open GluΠ T∼A
        ⊢IT = ®Π-wf iA RT T∼A
