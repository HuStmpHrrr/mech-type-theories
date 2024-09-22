{-# OPTIONS --without-K --safe #-}

open import Level hiding (_⊔_)
open import Axiom.Extensionality.Propositional

-- Properties of the gluing models for terms and types
module NonCumulative.Soundness.Properties.LogRel (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂) where

open import Lib
open import Data.Nat
open import Data.Nat.Properties as ℕₚ

open import NonCumulative.Statics.Ascribed.Misc
open import NonCumulative.Statics.Ascribed.Presup
open import NonCumulative.Statics.Ascribed.Properties
open import NonCumulative.Statics.Ascribed.Properties.Contexts
open import NonCumulative.Statics.Ascribed.Properties.Subst
open import NonCumulative.Statics.Ascribed.CtxEquiv
open import NonCumulative.Statics.Ascribed.Refl
open import NonCumulative.Semantics.Readback
open import NonCumulative.Semantics.Properties.PER (fext)
open import NonCumulative.Soundness.Weakening
open import NonCumulative.Soundness.LogRel

open import NonCumulative.Soundness.Properties.NoFunExt.LogRel public

Glu-wellfounded-≡′ : ∀ {j i i′} → (j<i : j < i) → (j<i′ : j < i′) →
  (λ (univ : ∀ {l} → l < j → Ty) {A B} → Glu-wellfounded i j<i univ {A} {B}) ≡ (λ (univ : ∀ {l} → l < j → Ty) {A B} → Glu-wellfounded i′ j<i′ univ {A} {B})
Glu-wellfounded-≡′ {j} {i} {i′} (s≤s {j} j<i) (s≤s {j} j<i′) = fext λ (univ : ∀ {l} → l < j → Ty) → cong
  (λ (rc : ∀ {k} (k<i : k < j) (univ : ∀ {l} → l < k → Ty) {A B} → Ctx → Typ → A ≈ B ∈ PERDef.𝕌 k univ → Set) {A B} →
    Glu.⟦ j , rc , univ ⟧_⊢_®_)
  (implicit-extensionality fext λ {j′} → fext λ j′<j → Glu-wellfounded-≡′ (≤-trans j′<j j<i) (≤-trans j′<j j<i′))

Glu-wellfounded-≡ : ∀ {i j} (j<i : j < i) → (λ {A B} → Glu-wellfounded i {j} j<i (𝕌-wellfounded j) {A} {B}) ≡ (_⊢_®[ j ]_)
Glu-wellfounded-≡ {j = j} (s≤s j<i) = cong
  (λ (rc : ∀ {k} (k<i : k < j) (univ : ∀ {l} → l < k → Ty) {A B} → Ctx → Typ → A ≈ B ∈ PERDef.𝕌 k univ → Set) {A B} → Glu.⟦ j , rc , 𝕌-wellfounded j ⟧_⊢_®_)
  (implicit-extensionality fext λ {j′} → fext λ j′<j → Glu-wellfounded-≡′ (≤-trans j′<j j<i) j′<j)

Glu-wf-gen : ∀ {i′} i → (f : ∀ {j} → j < i → j < i′) →
  (λ {l} l<k → Glu-wellfounded (i′) {l} (f l<k)) ≡ Glu-wellfounded i
Glu-wf-gen {i′} i f = implicit-extensionality fext (fext (λ l<k → Glu-wellfounded-≡′ (f l<k) l<k))

 -- If t and a are related, then a is in the El PER model.
®El⇒∈El : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
          Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
          -----------------------------
          a ∈′ El i A≈B
®El⇒∈El (ne C≈C j≡1+i j′≡1+i) (ne c≈c j≡i j≡′i , rel) = ne c≈c j≡i j≡′i
®El⇒∈El N′ (t®Nat , T≈N) = ®Nat⇒∈Nat t®Nat
®El⇒∈El {a = a} {i = i} (U′ {j}) t®
  rewrite 𝕌-≡-gen j U≤′
        | 𝕌-wf-gen j (U≤ refl) = A∈𝕌
  where open GluU t®
®El⇒∈El (Π eq jA RT j≡j' k≡k′) t® = a∈El
  where open GluΛ t®
®El⇒∈El (L eq A≈A′ j≡j' k≡k′) t® = a∈El
  where open Glul t®

®El⇒® : ∀ { i } → (A≈B : A ≈ B ∈ 𝕌 i) →
        Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
        ----------------------------
        Γ ⊢ T ®[ i ] A≈B
®El⇒® (ne C≈C j≡1+i j′≡1+i) (ne c≈c j≡i j≡í , record { t∶T = t∶T ; ⊢T = ⊢T ; krip = krip }) = ⊢T , λ ⊢σ → proj₁ (krip ⊢σ)
®El⇒® N′ (_ , T≈N) = T≈N
®El⇒® (U _ _) t® = GluU.T≈ t®
®El⇒® (Π′ {j = j} {k = k} jA RT) t®
  rewrite 𝕌-wf-gen k (ΠO≤′ j k refl)
        | Glu-wf-gen k (ΠO≤′ j k refl) = record
    { IT   = IT
    ; OT   = OT
    ; ⊢IT  = ⊢IT
    ; ⊢OT  = ⊢OT
    ; T≈   = T≈
    ; krip = λ ⊢σ → let open ΛRel (krip ⊢σ) in record
        { IT-rel = IT-rel
        ; OT-rel = λ s® a∈ → let open ΛKripke (ap-rel s® a∈) in ®El⇒® (ΠRT.T≈T′ (RT a∈)) ®fa
        }
    }
    where open GluΛ t®
®El⇒® (L′ {j} {k} kA) t®
  rewrite 𝕌-wf-gen k (Li≤′ j k refl)
        | Glu-wf-gen k (Li≤′ j k refl) = record
    { UT   = UT
    ; ⊢UT  = ⊢UT
    ; T≈   = T≈
    ; krip = λ ⊢σ → let open lKripke (krip ⊢σ) in ®El⇒® kA ®ua
    }
    where open Glul t®

-- If t and a are related, then the type of t is well-formed.
®El⇒ty : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
           Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
           ---------------------------
           Γ ⊢ T ∶[ 1 + i ] Se i
®El⇒ty A≈B t∼a = ®⇒ty A≈B (®El⇒® A≈B t∼a)

-- ®El respects term equivalence.
®El-resp-≈ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
             Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
             Γ ⊢ t ≈ t′ ∶[ i ] T →
             ----------------------------
             Γ ⊢ t′ ∶ T ®[ i ] a ∈El A≈B
®El-resp-≈ (ne C≈C j≡1+i j′≡1+i) (ne c≈c′ refl _ , glu) t≈t′ = ne′ c≈c′ , record
  { t∶T  = proj₁ (proj₂ (proj₂ (presup-≈ t≈t′)))
  ; ⊢T   = ⊢T
  ; krip = λ ⊢σ → proj₁ (krip ⊢σ) , ≈-trans ([]-cong (≈-sym t≈t′) (s-≈-refl (⊢w⇒⊢s ⊢σ))) (proj₂ (krip ⊢σ))
  }
  where open GluNe glu
®El-resp-≈ N′ (t® , T≈N) t≈t′ = ®Nat-resp-≈ t® (≈-conv t≈t′ T≈N) , T≈N
®El-resp-≈ (U′ {j}) t® t≈t′
  rewrite 𝕌-wf-gen j (U≤ refl)
        | Glu-wf-gen {j} j U≤′ = record
    { t∶T = proj₁ (proj₂ (proj₂ (presup-≈ t≈t′)))
    ; T≈  = T≈
    ; A∈𝕌 = A∈𝕌
    ; rel = ®-resp-≈ A∈𝕌 rel (≈-conv t≈t′ T≈)
    }
    where open GluU t®
®El-resp-≈ {Γ = Γ} {t = t} {t′ = t′} (Π′ {j = j} {k = k} jA RT) t® t≈t′
  rewrite 𝕌-wf-gen k (ΠO≤′ j k refl)
        | 𝕌-wf-gen j (ΠI≤′ j k refl)
        | Glu-wf-gen j (ΠI≤′ j k refl)
        | Glu-wf-gen k (ΠO≤′ j k refl) = record
    { t∶T  = proj₁ (proj₂ (proj₂ (presup-≈ t≈t′)))
    ; a∈El = a∈El
    ; IT   = IT
    ; OT   = OT
    ; ⊢IT  = ⊢IT
    ; ⊢OT  = ⊢OT
    ; T≈   = T≈
    ; krip = λ ⊢σ → let open ΛRel (krip ⊢σ) in record
        { IT-rel = IT-rel
        ; ap-rel = λ t® b∈ →
          let open ΛKripke (ap-rel t® b∈)
          in record
            { fa = fa
            ; ↘fa = ↘fa
            ; ®fa = ®El-resp-≈ (ΠRT.T≈T′ (RT b∈)) ®fa (t[σ]≈t′[σ]s (⊢w⇒⊢s ⊢σ) (®El⇒tm jA t®))
            }
        }
    }
    where open GluΛ t®
          t[σ]≈t′[σ]s : Δ ⊢s σ ∶ Γ →
               Δ ⊢ s ∶[ j ] IT [ σ ] →
               ----------------------
               Δ ⊢ t [ σ ] $ s ≈ t′ [ σ ] $ s ∶[ k ] OT [ σ , s ∶ IT ↙ j ]
          t[σ]≈t′[σ]s ⊢σ′ ⊢s = ≈-conv ($-cong Δ⊢IT[σ] Δ⊢OT[σ]
                                              (≈-conv ([]-cong t≈t′ (s-≈-refl ⊢σ′)) (≈-trans ([]-cong-Se′ T≈ ⊢σ′) (Π-[] ⊢σ′ ⊢IT ⊢OT refl)))
                                              (≈-refl ⊢s) refl)
                                      (≈-trans ([∘]-Se ⊢OT IT,Δ⊢s (⊢I,t ⊢Δ Δ⊢IT[σ] ⊢s))
                                               ([]-cong-Se″ ⊢OT
                                                            (s-∘ (s-, (s-I ⊢Δ) Δ⊢IT[σ] (conv ⊢s (≈-sym ([I] Δ⊢IT[σ])))) IT,Δ⊢s)
                                                            (qσ∘[I,t]≈σ,t ⊢Δ ⊢IT ⊢σ′ ⊢s)))
            where ⊢Δ      = (proj₁ (presup-s ⊢σ′))
                  Δ⊢IT[σ] = t[σ]-Se ⊢IT ⊢σ′
                  IT,Δ⊢s  = ⊢q ⊢Δ ⊢σ′ ⊢IT
                  Δ⊢OT[σ] = t[σ]-Se ⊢OT IT,Δ⊢s

®El-resp-≈ {i = i} (L′ {j = j} {k = k} kA) t® t≈t′
  rewrite 𝕌-wf-gen k (Li≤′ j k refl)
        | Glu-wf-gen k (Li≤′ j k refl) = record
    { t∶T  = proj₁ (proj₂ (proj₂ (presup-≈ t≈t′)))
    ; UT   = UT
    ; ⊢UT  = ⊢UT
    ; a∈El = a∈El
    ; T≈   = T≈
    ; krip = λ ⊢σ →
        let open lKripke (krip ⊢σ) in record
        { ua = ua
        ; ↘ua = ↘ua
        ; ®ua = ®El-resp-≈ kA ®ua ([]-cong (unlift-cong j ⊢UT (≈-conv t≈t′ T≈)) (s-≈-refl (⊢w⇒⊢s ⊢σ)))
        }
    }
    where open Glul t®

-- ®El respects context stack equivalence.
®El-resp-⊢≈ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
              Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
              ⊢ Γ ≈ Δ →
              ---------------------------
              Δ ⊢ t ∶ T ®[ i ] a ∈El A≈B
®El-resp-⊢≈ (ne′ _) (ne c≈c′ refl _ , glu) Γ≈Δ = (ne′ c≈c′) , record
  { t∶T = ctxeq-tm Γ≈Δ t∶T
  ; ⊢T = ctxeq-tm Γ≈Δ ⊢T
  ; krip = λ ⊢σ → krip (⊢w-resp-⊢≈ʳ ⊢σ (⊢≈-sym Γ≈Δ))
  }
  where open GluNe glu
®El-resp-⊢≈ N′ (t®N , T≈N) Γ≈Δ = (®Nat-resp-⊢≈ t®N Γ≈Δ) , ctxeq-≈ Γ≈Δ T≈N
®El-resp-⊢≈ (U′ {j}) t® Γ≈Δ
  rewrite 𝕌-wf-gen j (U≤ refl)
        | Glu-wf-gen {j} j U≤′ = record
    { t∶T = ctxeq-tm Γ≈Δ t∶T
    ; T≈  = ctxeq-≈ Γ≈Δ T≈
    ; A∈𝕌 = A∈𝕌
    ; rel = ®-resp-⊢≈ A∈𝕌 rel Γ≈Δ
    }
    where open GluU t®
®El-resp-⊢≈ (Π′ _ _) t® Γ≈Δ =
  let Δ⊢IT = ctxeq-tm Γ≈Δ ⊢IT in record
    { t∶T  = ctxeq-tm Γ≈Δ t∶T
    ; a∈El = a∈El
    ; IT   = IT
    ; OT   = OT
    ; ⊢IT  = Δ⊢IT
    ; ⊢OT  = ctxeq-tm (∷-cong Γ≈Δ ⊢IT Δ⊢IT (≈-refl ⊢IT) (≈-refl Δ⊢IT)) ⊢OT
    ; T≈   = ctxeq-≈ Γ≈Δ T≈
    ; krip = λ ⊢σ → krip (⊢w-resp-⊢≈ʳ ⊢σ (⊢≈-sym Γ≈Δ))
    }
    where open GluΛ t®
®El-resp-⊢≈ (L′ _) t® Γ≈Δ = record
  { t∶T  = ctxeq-tm Γ≈Δ t∶T
  ; UT   = UT
  ; ⊢UT  = ctxeq-tm Γ≈Δ ⊢UT
  ; a∈El = a∈El
  ; T≈   = ctxeq-≈ Γ≈Δ T≈
  ; krip = λ ⊢σ → krip (⊢w-resp-⊢≈ʳ ⊢σ (⊢≈-sym Γ≈Δ))
  }
  where open Glul t®

mutual
  ®-swap : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i)
           (B≈A : B ≈ A ∈ 𝕌 i) →
           Γ ⊢ T ®[ i ] A≈B →
           -----------------------
           Γ ⊢ T ®[ i ] B≈A
  ®-swap {Γ = Γ} {T} {i = i} (ne′ c≈c′) (ne c′≈c _ _) (⊢T , krip) = ⊢T , helper
    where
      helper : Δ ⊢w σ ∶ Γ →
               -----------------------------------
               Δ ⊢ T [ σ ] ≈ Ne⇒Exp (proj₁ (c′≈c (len Δ))) ∶[ 1 + i ] Se i
      helper {Δ} {σ} ⊢σ
        with c≈c′ (len Δ) | c′≈c (len Δ) | krip ⊢σ
      ...  | _ , ↘u , _ | _ , _ , ↘u₁ | Tσ≈
          rewrite Re-det ↘u ↘u₁ = Tσ≈
  ®-swap N′ N′ T® = T®
  ®-swap U′ (U i≡1+j j≡j′) T®
    rewrite ≡-irrelevant i≡1+j refl = T®
  ®-swap {_} {_} {Γ} (Π′ {j} {k} jA RT) (Π i≡maxjk jA′ RT′ j≡j′ k≡k′) T®
    rewrite ≡-irrelevant i≡maxjk refl
          | 𝕌-wf-gen j (ΠI≤′ j k refl)
          | 𝕌-wf-gen k (ΠO≤′ j k refl)
          | Glu-wf-gen j (ΠI≤′ j k refl)
          | Glu-wf-gen k (ΠO≤′ j k refl) = record
      { IT   = IT
      ; OT   = OT
      ; ⊢IT  = ⊢IT
      ; ⊢OT  = ⊢OT
      ; T≈   = T≈
      ; krip = λ ⊢σ → let open ΠRel (krip ⊢σ) in record
        { IT-rel = ®-swap jA jA′ IT-rel
        ; OT-rel = λ s® a∈ → OT-helper a∈ s® OT-rel
        }
      }
      where open GluΠ T®
            OT-helper : (a∈′ : a ∈′ El j jA′) →
                        Δ ⊢ s ∶ IT [ σ ] ®[ j ] a ∈El jA′ →
                        (∀ {s a} → Δ ⊢ s ∶ IT [ σ ] ®[ j ] a ∈El jA →
                          (a∈ : a ∈′ El j jA) →
                          Δ ⊢ OT [ σ , s ∶ IT ↙ j ] ®[ k ] ΠRT.T≈T′ (RT a∈)) →
                        --------------------------------------------------------------
                        Δ ⊢ OT [ σ , s ∶ IT ↙ j ] ®[ k ] ΠRT.T≈T′ (RT′ a∈′)
            OT-helper a∈′ s® OT-rel
              with El-sym jA′ jA a∈′
            ...  | a∈
                with RT a∈ | RT′ a∈′ | OT-rel (®El-swap jA′ jA s®) a∈
            ...    | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
                  | record { ↘⟦T⟧ = ↘⟦T′⟧₁ ; ↘⟦T′⟧ = ↘⟦T⟧₁ ; T≈T′ = T′≈T }
                  | R
                  rewrite ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₁
                        | ⟦⟧-det ↘⟦T′⟧ ↘⟦T′⟧₁ = ®-swap T≈T′ T′≈T R
  ®-swap (L′ {j} {k} kA) (L i≡j+k kA′ _ _) T®
    rewrite ≡-irrelevant i≡j+k refl
          | 𝕌-wf-gen k (Li≤′ j k refl)
          | Glu-wf-gen k (Li≤′ j k refl) = record
      { UT   = UT
      ; ⊢UT  = ⊢UT
      ; T≈   = T≈
      ; krip = λ ⊢σ → ®-swap kA kA′ (krip ⊢σ)
      }
      where open GluL T®

  ®El-swap : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i)
             (B≈A : B ≈ A ∈ 𝕌 i) →
             Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
             ----------------------------
             Γ ⊢ t ∶ T ®[ i ] a ∈El B≈A
  ®El-swap {_} {_} {Γ} {t} {T} {i = i} (ne′ C≈C′) (ne C′≈C _ _) (ne c≈c refl _ , glu) = (ne c≈c refl refl) , record
    { t∶T  = t∶T
    ; ⊢T   = ⊢T
    ; krip = λ ⊢σ → krip′ ⊢σ
    }
    where
      open GluNe glu
      krip′ : Δ ⊢w σ ∶ Γ →
               -----------------------------------
               Δ ⊢ T [ σ ] ≈ Ne⇒Exp (proj₁ (C′≈C (L.length Δ))) ∶[ 1 + i ] Se i
                 × Δ ⊢ t [ σ ] ≈ Ne⇒Exp (proj₁ (c≈c (L.length Δ))) ∶[ i ] T [ σ ]
      krip′ {Δ} {σ} ⊢σ
        with C≈C′ (len Δ) | C′≈C (len Δ) | krip ⊢σ
      ...  | _ , ↘u , _ | _ , _ , ↘u₁ | Tσ≈ , tσ≈
           rewrite Re-det ↘u ↘u₁ = Tσ≈ , tσ≈
  ®El-swap N′ N′ T® = T®
  ®El-swap U′ (U i≡1+j j≡j′) T®
    rewrite ≡-irrelevant i≡1+j refl = T®
  ®El-swap (Π′ {j} {k} jA RT) (Π i≡maxjk jA′ RT′ j≡j′ k≡k′) t®
    rewrite ≡-irrelevant i≡maxjk refl
          | 𝕌-wf-gen j (ΠI≤′ j k refl)
          | 𝕌-wf-gen k (ΠO≤′ j k refl)
          | Glu-wf-gen j (ΠI≤′ j k refl)
          | Glu-wf-gen k (ΠO≤′ j k refl) = record
      { t∶T  = t∶T
      ; a∈El = El-Π-𝕌 i≡maxjk jA′ RT′ (El-swap (proj₁ Π-bund) (Π-𝕌 jA′ RT′ i≡maxjk) (proj₂ Π-bund))
      ; IT   = IT
      ; OT   = OT
      ; ⊢IT  = ⊢IT
      ; ⊢OT  = ⊢OT
      ; T≈   = T≈
      ; krip = λ ⊢σ → let open ΛRel (krip ⊢σ) in record
        { IT-rel = ®-swap jA jA′ IT-rel
        ; ap-rel = λ s® b∈ → ap-helper b∈ s® ap-rel
        }
      }
      where open GluΛ t®
            Π-bund = Π-bundle jA (λ a≈a′ → RT a≈a′ , a∈El a≈a′) refl
            ap-helper : (b∈′ : b ∈′ El j jA′) →
                        Δ ⊢ s ∶ IT [ σ ] ®[ j ] b ∈El jA′ →
                        (∀ {s b} → Δ ⊢ s ∶ IT [ σ ] ®[ j ] b ∈El jA →
                          (a∈ : b ∈′ El j jA) →
                          ΛKripke Δ (t [ σ ] $ s) (OT [ σ , s ∶ IT ↙ j ]) a b (_⊢_∶_®[ k ]_∈El ΠRT.T≈T′ (RT a∈)) ) →
                        --------------------------------------------------------------
                        ΛKripke Δ (t [ σ ] $ s) (OT [ σ , s ∶ IT ↙ j ]) a b (_⊢_∶_®[ k ]_∈El ΠRT.T≈T′ (RT′ b∈′))
            ap-helper b∈′ s® ap-rel
              with El-sym jA′ jA b∈′
            ...  | b∈
                with RT b∈ | RT′ b∈′ | ap-rel (®El-swap jA′ jA s®) b∈
            ...    | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
                   | record { ↘⟦T⟧ = ↘⟦T′⟧₁ ; ↘⟦T′⟧ = ↘⟦T⟧₁ ; T≈T′ = T′≈T }
                   | record { fa = fa ; ↘fa = ↘fa ; ®fa = ®fa }
                  rewrite ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₁
                        | ⟦⟧-det ↘⟦T′⟧ ↘⟦T′⟧₁ = record
                    { fa = fa
                    ; ↘fa = ↘fa
                    ; ®fa = ®El-swap T≈T′ T′≈T ®fa
                    }

  ®El-swap (L′ {j} {k} kA) (L i≡j+k kA′ j≡j′ k≡k′) t®
    rewrite ≡-irrelevant i≡j+k refl
          | 𝕌-wf-gen k (Li≤′ j k refl)
          | Glu-wf-gen k (Li≤′ j k refl) = record
      { t∶T   = t∶T
      ; UT    = UT
      ; ⊢UT   = ⊢UT
      ; a∈El  = El-L-𝕌 kA′ i≡j+k (El-swap (proj₁ L-bund) (L-𝕌 kA′ i≡j+k) (proj₂ L-bund))
      ; T≈    = T≈
      ; krip  = λ ⊢σ → let open lKripke (krip ⊢σ) in record
        { ua  = ua
        ; ↘ua = ↘ua
        ; ®ua = ®El-swap kA kA′ ®ua
        }
      }
      where open Glul t®
            L-bund = L-bundle {j = j} kA a∈El refl

mutual

  ®-one-sided : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i)
                  (A≈B′ : A ≈ B′ ∈ 𝕌 i) →
                  Γ ⊢ T ®[ i ] A≈B →
                  -----------------------
                  Γ ⊢ T ®[ i ] A≈B′
  ®-one-sided {Γ = Γ} {T} {i} (ne′ C≈C′) (ne C≈C″ _ _) (⊢T , rel) = ⊢T , helper
    where helper : Δ ⊢w σ ∶ Γ → Δ ⊢ T [ σ ] ≈ Ne⇒Exp (proj₁ (C≈C″ (len Δ))) ∶[ 1 + i ] Se i
          helper {Δ} {σ} ⊢σ
            with C≈C′ (len Δ) | C≈C″ (len Δ) | rel ⊢σ
          ... | u , ↘u , _ | u′ , ↘u′ , _ | Tσ≈
               rewrite Re-det ↘u ↘u′ = Tσ≈
  ®-one-sided N′ N′ T® = T®
  ®-one-sided U′ (U i≡1+j j≡j′) T®
   rewrite ≡-irrelevant i≡1+j refl = T®
  ®-one-sided {_} {_} {Γ} (Π′ {j} {k} jA RT) (Π i≡maxjk jA′ RT′ _ _) T®
    rewrite ≡-irrelevant i≡maxjk refl
          | 𝕌-wf-gen j (ΠI≤′ j k refl)
          | 𝕌-wf-gen k (ΠO≤′ j k refl)
          | Glu-wf-gen j (ΠI≤′ j k refl)
          | Glu-wf-gen k (ΠO≤′ j k refl)
    = record
      { IT   = IT
      ; OT   = OT
      ; ⊢IT  = ⊢IT
      ; ⊢OT  = ⊢OT
      ; T≈   = T≈
      ; krip = λ ⊢σ →
        let open ΠRel (krip ⊢σ)
        in record
        { IT-rel = ®-one-sided jA jA′ IT-rel
        ; OT-rel = λ s® a∈ → OT-helper a∈ s® OT-rel
        }
      }
      where open GluΠ T®
            OT-helper : (a∈′ : a ∈′ El j jA′) →
                        Δ ⊢ s ∶ IT [ σ ] ®[ j ] a ∈El jA′ →
                        (∀ {s a} → Δ ⊢ s ∶ IT [ σ ] ®[ j ] a ∈El jA →
                          (a∈ : a ∈′ El j jA) →
                          Δ ⊢ OT [ σ , s ∶ IT ↙ j ] ®[ k ] ΠRT.T≈T′ (RT a∈)) →
                        --------------------------------------------------------------
                        Δ ⊢ OT [ σ , s ∶ IT ↙ j ] ®[ k ] ΠRT.T≈T′ (RT′ a∈′)
            OT-helper a∈′ s® OT-rel
              with El-one-sided jA′ jA a∈′
            ...  | a∈
                with RT a∈ | RT′ a∈′ | OT-rel (®El-one-sided jA′ jA s®) a∈
            ...    | record { ⟦T⟧ = ⟦T⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; T≈T′ = T≈T′ }
                   | record { ↘⟦T⟧ = ↘⟦T⟧′ ; T≈T′ = T≈T′₁ }
                   | R
                  rewrite ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧ = ®-one-sided T≈T′ T≈T′₁ R
  ®-one-sided (L′ {j} {k} kA) (L i≡j+k kA′ j≡j′ k≡k′) T®
    rewrite ≡-irrelevant i≡j+k refl
          | 𝕌-wf-gen k (Li≤′ j k refl)
          | Glu-wf-gen k (Li≤′ j k refl) = record
      { UT   = UT
      ; ⊢UT  = ⊢UT
      ; T≈   = T≈
      ; krip = λ ⊢σ → ®-one-sided kA kA′ (krip ⊢σ)
      }
      where open GluL T®

  ®El-one-sided : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i)
                (A≈B′ : A ≈ B′ ∈ 𝕌 i) →
                Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
                ----------------------------
                Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B′
  ®El-one-sided {Γ = Γ} {t} {T} {_} {i} (ne′ C≈C′) (ne C≈C″ _ _) (ne c≈c refl _ , glu) = (ne c≈c refl refl) , record
    { t∶T  = t∶T
    ; ⊢T   = ⊢T
    ; krip = krip′
    }
    where open GluNe glu
          krip′ : Δ ⊢w σ ∶ Γ →
                  -----------------------------------
                  Δ ⊢ T [ σ ] ≈ Ne⇒Exp (proj₁ (C≈C″ (L.length Δ))) ∶[ ℕ.suc i ] Se i
                  × Δ ⊢ t [ σ ] ≈ Ne⇒Exp (proj₁ (c≈c (L.length Δ))) ∶[ i ] T [ σ ]
          krip′ {Δ} {σ} ⊢σ
            with C≈C′ (len Δ) | C≈C″ (len Δ) | krip ⊢σ
          ...  | u , ↘u , _ | u′ , ↘u′ , _ | Tσ≈ , tσ≈
               rewrite Re-det ↘u ↘u′ = Tσ≈ , tσ≈
  ®El-one-sided N′ N′ t® = t®
  ®El-one-sided U′ (U i≡1+j j≡j′) t®
    rewrite ≡-irrelevant i≡1+j refl = t®
  ®El-one-sided (Π′ {j} {k} jA RT) (Π i≡maxjk jA′ RT′ _ _) t®
    rewrite ≡-irrelevant i≡maxjk refl
          | 𝕌-wf-gen j (ΠI≤′ j k refl)
          | 𝕌-wf-gen k (ΠO≤′ j k refl)
          | Glu-wf-gen j (ΠI≤′ j k refl)
          | Glu-wf-gen k (ΠO≤′ j k refl) = record
      { t∶T  = t∶T
      ; a∈El = El-Π-𝕌 i≡maxjk jA′ RT′ (El-one-sided (proj₁ Π-bund) (Π-𝕌 jA′ RT′ i≡maxjk) (proj₂ Π-bund))
      ; IT   = IT
      ; OT   = OT
      ; ⊢IT  = ⊢IT
      ; ⊢OT  = ⊢OT
      ; T≈   = T≈
      ; krip = λ ⊢σ →
        let open ΛRel (krip ⊢σ)
        in record
          { IT-rel = ®-one-sided jA jA′ IT-rel
          ; ap-rel = λ s® b∈ → ap-helper b∈ s® ap-rel
          }
      }
      where open GluΛ t®
            Π-bund = Π-bundle jA (λ a≈a′ → RT a≈a′ , a∈El a≈a′) refl
            ap-helper : (b∈′ : b ∈′ El j jA′) →
                          Δ ⊢ s ∶ IT [ σ ] ®[ j ] b ∈El jA′ →
                          (∀ {s b} → Δ ⊢ s ∶ IT [ σ ] ®[ j ] b ∈El jA →
                            (a∈ : b ∈′ El j jA) →
                            ΛKripke Δ (t [ σ ] $ s) (OT [ σ , s ∶ IT ↙ j ]) a b (_⊢_∶_®[ k ]_∈El ΠRT.T≈T′ (RT a∈)) ) →
                          --------------------------------------------------------------
                          ΛKripke Δ (t [ σ ] $ s) (OT [ σ , s ∶ IT ↙ j ]) a b (_⊢_∶_®[ k ]_∈El ΠRT.T≈T′ (RT′ b∈′))
            ap-helper b∈′ s® ap-rel
              with El-one-sided jA′ jA b∈′
            ...  | b∈
                with RT b∈ | RT′ b∈′ | ap-rel (®El-one-sided jA′ jA s®) b∈
            ...    | record { ⟦T⟧ = ⟦T⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; T≈T′ = T≈T′ }
                   | record { ↘⟦T⟧ = ↘⟦T⟧′ ; T≈T′ = T≈T′₁ }
                   | R
                  rewrite ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧ = record
                    { fa  = fa
                    ; ↘fa = ↘fa
                    ; ®fa = ®El-one-sided T≈T′ T≈T′₁ ®fa
                    }
                    where open ΛKripke R
  ®El-one-sided (L′ {j} {k} kA) (L i≡j+k kA′ _ _) t®
    rewrite ≡-irrelevant i≡j+k refl
          | 𝕌-wf-gen k (Li≤′ j k refl)
          | Glu-wf-gen k (Li≤′ j k refl) = record
      { t∶T  = t∶T
      ; UT   = UT
      ; ⊢UT  = ⊢UT
      ; a∈El = El-L-𝕌 kA′ i≡j+k (El-one-sided (proj₁ L-bund) (L-𝕌 kA′ i≡j+k) (proj₂ L-bund))
      ; T≈   = T≈
      ; krip = λ ⊢σ →
        let open lKripke (krip ⊢σ)
        in record
        { ua  = ua
        ; ↘ua = ↘ua
        ; ®ua = ®El-one-sided kA kA′ ®ua
        }
      }
      where open Glul t®
            L-bund = L-bundle {j = j} kA a∈El refl

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

-- The gluing models for types and terms are monotonic.
®-mon : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i)
        (A≈B′ : A ≈ B ∈ 𝕌 i) →
        Γ ⊢ T ®[ i ] A≈B →
        Δ ⊢w σ ∶ Γ →
        -----------------------------------
        Δ ⊢ T [ σ ] ®[ i ] A≈B′
®-mon {_} {_} {_} {T} {Δ} {σ} {i} (ne′ C≈C′) (ne C≈′C′ _ _) (⊢T , rel) ⊢σ = (t[σ]-Se ⊢T (⊢w⇒⊢s ⊢σ)) , helper
  where helper : Δ′ ⊢w τ ∶ Δ → Δ′ ⊢ T [ σ ] [ τ ] ≈ Ne⇒Exp (proj₁ (C≈′C′ (L.length Δ′))) ∶[ 1 + i ] Se i
        helper {Δ′} ⊢τ
          with C≈C′ (len Δ′) | C≈′C′ (len Δ′) | (rel (⊢w-∘ ⊢σ ⊢τ))
        ...  | u , ↘u , _ | u′ , ↘u′ , _ | Tστ≈
            rewrite Re-det ↘u ↘u′ = ≈-trans ([∘]-Se ⊢T (⊢w⇒⊢s ⊢σ) (⊢w⇒⊢s ⊢τ)) Tστ≈
®-mon N′ N′ T® ⊢σ = ≈-trans ([]-cong-Se′ T® (⊢w⇒⊢s ⊢σ)) (N-[] (⊢w⇒⊢s ⊢σ))
®-mon U′ (U _ _) T® ⊢σ = ≈-trans ([]-cong-Se′ T® (⊢w⇒⊢s ⊢σ)) (Se-[] _ (⊢w⇒⊢s ⊢σ))
®-mon {Δ = Δ} {σ = σ} (Π′ {j} {k} jA RT) (Π i≡maxjk jA′ RT′ _ _) T® ⊢σ
  rewrite ≡-irrelevant i≡maxjk refl
        | 𝕌-wf-gen k (ΠO≤′ j k refl)
        | 𝕌-wf-gen j (ΠI≤′ j k refl)
        | Glu-wf-gen j (ΠI≤′ j k refl)
        | Glu-wf-gen k (ΠO≤′ j k refl) = record
    { IT   = IT [ σ ]
    ; OT   = OT [ q (IT ↙ j) σ ]
    ; ⊢IT  = t[σ]-Se ⊢IT ⊢σ′
    ; ⊢OT  = t[σ]-Se ⊢OT (⊢q (proj₁ (presup-s ⊢σ′)) ⊢σ′ ⊢IT)
    ; T≈   = ≈-trans ([]-cong-Se′ T≈ ⊢σ′) (Π-[] ⊢σ′ ⊢IT ⊢OT refl)
    ; krip = λ {_} {τ} ⊢τ →
      let open ΠRel (krip (⊢w-∘ ⊢σ ⊢τ)) in record
        { IT-rel = ®-one-sided jA jA′ (®-resp-≈ jA IT-rel (≈-sym ([∘]-Se ⊢IT ⊢σ′ (⊢w⇒⊢s ⊢τ))))
        ; OT-rel = λ s® a∈ → OT-helper ⊢τ a∈ s® OT-rel
        }
    }
    where
      open GluΠ T®
      ⊢σ′ = ⊢w⇒⊢s ⊢σ
      OT-helper : Δ′ ⊢w τ ∶ Δ →
                  (a∈′ : a ∈′ El j jA′) →
                  Δ′ ⊢ s ∶ IT [ σ ] [ τ ] ®[ j ] a ∈El jA′ →
                  (∀ {s a} → Δ′ ⊢ s ∶ IT [ σ ∘ τ ] ®[ j ] a ∈El jA →
                    (a∈ : a ∈′ El j jA) →
                    Δ′ ⊢ OT [ (σ ∘ τ) , s ∶ IT ↙ j ] ®[ k ] ΠRT.T≈T′ (RT a∈)) →
                  --------------------------------------------------------------
                  Δ′ ⊢ OT [ q (IT ↙ j) σ ] [ τ , s ∶ IT [ σ ] ↙ j ] ®[ k ] ΠRT.T≈T′ (RT′ a∈′)
      OT-helper ⊢τ a∈′ s®′ OT-rel
        with ®El-resp-T≈ jA (®El-one-sided jA′ jA s®′) ([∘]-Se ⊢IT ⊢σ′ (⊢w⇒⊢s ⊢τ))
           | El-one-sided jA′ jA a∈′
      ...  | s® | a∈
          with RT a∈ | RT′ a∈′ | OT-rel s® a∈
      ...    | record { ⟦T⟧ = ⟦T⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; T≈T′ = T≈T′ }
             | record { ↘⟦T⟧ = ↘⟦T⟧′ ; T≈T′ = T≈T′₁ }
             | rel
            rewrite ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧ = ®-resp-≈ T≈T′₁ (®-≡ T≈T′ T≈T′₁ rel refl) ([]-q-∘-, ⊢OT ⊢σ′ (⊢w⇒⊢s ⊢τ) (®El⇒tm jA′ s®′))
®-mon {Δ = Δ} {σ = σ} (L′ {j} {k} kA) (L i≡j+k kA′ _ _) T® ⊢σ
  rewrite ≡-irrelevant i≡j+k refl
        | 𝕌-wf-gen k (Li≤′ j k refl)
        | Glu-wf-gen k (Li≤′ j k refl) = record
    { UT   = UT [ σ ]
    ; ⊢UT  = t[σ]-Se ⊢UT (⊢w⇒⊢s ⊢σ)
    ; T≈   = ≈-trans ([]-cong-Se′ T≈ (⊢w⇒⊢s ⊢σ)) (Liftt-[] _ (⊢w⇒⊢s ⊢σ) ⊢UT)
    ; krip = helper
    }
  where open GluL T®
        helper : Δ′ ⊢w τ ∶ Δ → Δ′ ⊢ UT [ σ ] [ τ ] ®[ k ] kA′
        helper {Δ′} ⊢τ = ®-≡ kA kA′ (®-resp-≈ kA (krip (⊢w-∘ ⊢σ ⊢τ)) (≈-sym ([∘]-Se ⊢UT (⊢w⇒⊢s ⊢σ) (⊢w⇒⊢s ⊢τ)))) refl

®El-mon : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i)
          (A≈B′ : A ≈ B ∈ 𝕌 i) →
          Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
          Δ ⊢w σ ∶ Γ →
          --------------------------------------
          Δ ⊢ t [ σ ] ∶ T [ σ ] ®[ i ] a ∈El A≈B′
®El-mon {t = t} {T = T} {Δ = Δ} {σ = σ} {i = i} (ne′ C≈C′) (ne C≈′C′ _ _) (ne c≈c refl _ , glu) ⊢σ = (ne′ c≈c) , record
  { t∶T  = t[σ] t∶T ⊢σ′
  ; ⊢T   = t[σ]-Se ⊢T ⊢σ′
  ; krip = helper
  }
  where open GluNe glu
        ⊢σ′ = ⊢w⇒⊢s ⊢σ

        helper : ∀ {Δ′ τ} → Δ′ ⊢w τ ∶ Δ →
                 -------------------------------------------------
                 Δ′ ⊢ T [ σ ] [ τ ] ≈ Ne⇒Exp (proj₁ (C≈′C′ (len Δ′))) ∶[ 1 + i ] Se i
                  × Δ′ ⊢ t [ σ ] [ τ ] ≈ Ne⇒Exp (proj₁ (c≈c (len Δ′))) ∶[ i ] T [ σ ] [ τ ]
        helper {Δ′ = Δ′} {τ = τ} ⊢τ
          with C≈C′ (len Δ′) | C≈′C′ (len Δ′) | c≈c (len Δ′) | krip (⊢w-∘ ⊢σ ⊢τ)
        ...  | V , ↘V , _
             | V′ , ↘V′ , _
             | u , ↘u , _
             | Tστ≈ , tστ≈
            rewrite Re-det ↘V ↘V′ = (≈-trans ([∘]-Se ⊢T ⊢σ′ ⊢τ′) Tστ≈) , ≈-conv (≈-trans (≈-sym ([∘] ⊢τ′ ⊢σ′ t∶T)) tστ≈) (≈-sym ([∘]-Se ⊢T ⊢σ′ ⊢τ′))
            where ⊢τ′ = ⊢w⇒⊢s ⊢τ
®El-mon N′ N′ (t®Nat , T≈N) ⊢σ = ®Nat-mon t®Nat ⊢σ , ≈-trans ([]-cong-Se′ T≈N (⊢w⇒⊢s ⊢σ)) (N-[] (⊢w⇒⊢s ⊢σ))
®El-mon (U′ {j}) (U i≡1+j j≡j′) t® ⊢σ
  rewrite ≡-irrelevant i≡1+j refl
        | 𝕌-wf-gen j (U≤ refl)
        | Glu-wf-gen {j} j U≤′ = record
    { t∶T = t[σ] t∶T (⊢w⇒⊢s ⊢σ)
    ; T≈  = ≈-trans ([]-cong-Se′ T≈ ⊢σ′) (Se-[] _ ⊢σ′)
    ; A∈𝕌 = A∈𝕌
    ; rel = ®-mon A∈𝕌 A∈𝕌 rel ⊢σ
    }
    where open GluU t®
          ⊢σ′ = ⊢w⇒⊢s ⊢σ
®El-mon {Γ = Γ} {t = t} {T = T} {Δ = Δ} {σ = σ} (Π′ {j} {k} jA RT) (Π i≡maxjk jA′ RT′ _ _) t® ⊢σ
  rewrite ≡-irrelevant i≡maxjk refl
        | 𝕌-wf-gen j (ΠI≤′ j k refl)
        | 𝕌-wf-gen k (ΠO≤′ j k refl)
        | Glu-wf-gen j (ΠI≤′ j k refl)
        | Glu-wf-gen k (ΠO≤′ j k refl) = record
    { t∶T  = t[σ] t∶T ⊢σ′
    ; a∈El = El-Π-𝕌 i≡maxjk jA′ RT′ (El-one-sided (proj₁ Π-bund) (Π-𝕌 jA′ RT′ i≡maxjk) (proj₂ Π-bund))
    ; IT   = IT [ σ ]
    ; OT   = OT [ q (IT ↙ j) σ ]
    ; ⊢IT  = t[σ]-Se ⊢IT ⊢σ′
    ; ⊢OT  = t[σ]-Se ⊢OT (⊢q (proj₁ (presup-s ⊢σ′)) ⊢σ′ ⊢IT)
    ; T≈   = ≈-trans ([]-cong-Se′ T≈ ⊢σ′) (Π-[] ⊢σ′ ⊢IT ⊢OT refl)
    ; krip = λ {Δ′} {τ} ⊢τ →
      let open ΛRel (krip (⊢w-∘ ⊢σ ⊢τ))
      in record
      { IT-rel = ®-one-sided jA jA′ (®-resp-≈ jA IT-rel (≈-sym ([∘]-Se ⊢IT ⊢σ′ (⊢w⇒⊢s ⊢τ))))
      ; ap-rel = λ s® b∈ → ap-helper ⊢τ b∈ s® ap-rel
      }
    }
    where open GluΛ t®
          Π-bund = Π-bundle jA (λ a≈a′ → RT a≈a′ , a∈El a≈a′) refl
          ⊢σ′ = ⊢w⇒⊢s ⊢σ
          ap-helper : Δ′ ⊢w τ ∶ Δ →
                      (b∈′ : b ∈′ El j jA′) →
                      Δ′ ⊢ s ∶ IT [ σ ] [ τ ] ®[ j ] b ∈El jA′ →
                      (∀ {s b} → Δ′ ⊢ s ∶ IT [ σ ∘ τ ] ®[ j ] b ∈El jA →
                        (a∈ : b ∈′ PERDef.El j _ jA) →
                        ΛKripke Δ′ (t [ σ ∘ τ ] $ s) (OT [ (σ ∘ τ) , s ∶ IT ↙ j ]) a b (_⊢_∶_®[ k ]_∈El ΠRT.T≈T′ (RT a∈)) ) →
                      --------------------------------------------------------------
                      ΛKripke Δ′ (t [ σ ] [ τ ] $ s) (OT [ q (IT ↙ j) σ ] [ τ , s ∶ IT [ σ ] ↙ j ]) a b (_⊢_∶_®[ k ]_∈El ΠRT.T≈T′ (RT′ b∈′))
          ap-helper {Δ′ = Δ′} {τ = τ} {s = s} ⊢τ b∈′ s®′ ap-rel
            with El-one-sided jA′ jA b∈′
          ...  | b∈
              with ®El-one-sided jA′ jA (®El-resp-T≈ jA′ s®′ ([∘]-Se ⊢IT ⊢σ′ (⊢w⇒⊢s ⊢τ)))
          ...    | s®
                with RT b∈ | RT′ b∈′ | (ap-rel s® b∈)
          ...      | record { ⟦T⟧ = ⟦T⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; T≈T′ = T≈T′ }
                  | record { ↘⟦T⟧ = ↘⟦T⟧′ ; T≈T′ = T≈T′₁ }
                  | record { fa = fa ; ↘fa = ↘fa ; ®fa = ®fa }
                  rewrite ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧ = record
                    { fa = fa
                    ; ↘fa = ↘fa
                    ; ®fa = ®El-one-sided T≈T′ T≈T′₁ (®El-resp-≈ T≈T′ (®El-resp-T≈ T≈T′ ®fa OT,≈) t[στ]s≈t[σ][τ]s)
                    }
            where ⊢τ′  = ⊢w⇒⊢s ⊢τ
                  ⊢s   = ®El⇒tm jA′ s®′
                  ⊢s′  = ®El⇒tm jA s®
                  ⊢στ  = s-∘ ⊢τ′ ⊢σ′
                  OT,≈ = []-q-∘-, ⊢OT ⊢σ′ ⊢τ′ ⊢s
                  t[στ]s≈t[σ][τ]s : Δ′ ⊢ t [ σ ∘ τ ] $ s ≈ t [ σ ] [ τ ] $ s ∶[ k ] OT [ q (IT ↙ j) σ ] [ τ , s ∶ sub IT σ ↙ j ]
                  t[στ]s≈t[σ][τ]s = ≈-conv ($-cong (t[σ]-Se ⊢IT ⊢στ) (t[σ]-Se ⊢OT (⊢q (proj₁ (presup-s ⊢τ′)) ⊢στ ⊢IT))
                                                  (≈-conv ([∘] ⊢τ′ ⊢σ′ t∶T) (≈-trans ([]-cong-Se′ T≈ ⊢στ) (Π-[] ⊢στ ⊢IT ⊢OT refl)))
                                                  (≈-refl ⊢s′) refl)
                                         (≈-trans (≈-sym ([]-q-∘-,′ ⊢OT ⊢στ ⊢s′)) OT,≈)
®El-mon {Γ = Γ} {t = t} {T = T} {Δ = Δ} {σ = σ} {i = i} (L′ {j} {k} kA) (L i≡j+k kA′ _ _) t® ⊢σ
  rewrite ≡-irrelevant i≡j+k refl
        | 𝕌-wf-gen k (Li≤′ j k refl)
        | Glu-wf-gen k (Li≤′ j k refl) = record
    { t∶T  = t[σ] t∶T (⊢w⇒⊢s ⊢σ)
    ; UT   = UT [ σ ]
    ; ⊢UT  = t[σ]-Se ⊢UT ⊢σ′
    ; a∈El = El-L-𝕌 kA′ i≡j+k (El-one-sided (proj₁ L-bund) (L-𝕌 kA′ i≡j+k) (proj₂ L-bund))
    ; T≈   = ≈-trans ([]-cong-Se′ T≈ ⊢σ′) (Liftt-[] _ ⊢σ′ ⊢UT)
    ; krip = λ {Δ′} {τ} ⊢τ →
      let open lKripke (krip (⊢w-∘ ⊢σ ⊢τ))
      in record
        { ua  = ua
        ; ↘ua = ↘ua
        ; ®ua = helper (⊢w⇒⊢s ⊢τ) ®ua (unli[τ∘σ]≈unli[σ][τ] (⊢w⇒⊢s ⊢τ))
        }
    }
    where open Glul t®
          L-bund = L-bundle {j = j} kA a∈El refl
          ⊢σ′ = ⊢w⇒⊢s ⊢σ
          unli[τ∘σ]≈unli[σ][τ] : Δ′ ⊢s τ ∶ Δ →
                                 Δ′ ⊢ (unlift t) [ σ ∘ τ ] ≈ (unlift (t [ σ ])) [ τ ] ∶[ k ] UT [ σ ] [ τ ]
          unli[τ∘σ]≈unli[σ][τ] ⊢τ′ = ≈-trans (≈-conv ([∘] ⊢τ′ ⊢σ′ (L-E _ ⊢UT (conv t∶T T≈)))
                                                     (≈-sym ([∘]-Se ⊢UT ⊢σ′ ⊢τ′)))
                                             ([]-cong (unlift-[] _ ⊢UT ⊢σ′ (conv t∶T T≈)) (s-≈-refl ⊢τ′))
          helper :  ∀ {ua} →
                    Δ′ ⊢s τ ∶ Δ →
                    Δ′ ⊢ (unlift t) [ σ ∘ τ ] ∶ UT [ σ ∘ τ ] ®[ k ] ua ∈El kA →
                    Δ′ ⊢ (unlift t) [ σ ∘ τ ] ≈ (unlift (t [ σ ])) [ τ ] ∶[ k ] UT [ σ ] [ τ ] →
                    ------------------------------------
                    Δ′ ⊢ (unlift (t [ σ ])) [ τ ] ∶ UT [ σ ] [ τ ] ®[ k ] ua ∈El kA′
          helper ⊢τ′ ®a t≈t′ = ®El-one-sided kA kA′ (®El-resp-≈ kA (®El-resp-T≈ kA ®a (≈-sym ([∘]-Se ⊢UT ⊢σ′ ⊢τ′))) t≈t′)

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