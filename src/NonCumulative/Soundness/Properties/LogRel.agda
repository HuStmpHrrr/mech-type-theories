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

Glu-wellfounded-≡ : ∀ {i j} (j<i : j < i) →  (λ {A B} → Glu-wellfounded i {j} j<i (𝕌-wellfounded j) {A} {B}) ≡ (_⊢_®[ j ]_)
Glu-wellfounded-≡ {j = j} (s≤s j<i) = cong
  (λ (rc : ∀ {k} (k<i : k < j) (univ : ∀ {l} → l < k → Ty) {A B} → Ctx → Typ → A ≈ B ∈ PERDef.𝕌 k univ → Set) {A B} → Glu.⟦ j , rc , 𝕌-wellfounded j ⟧_⊢_®_)
  (implicit-extensionality fext λ {j′} → fext λ j′<j → Glu-wellfounded-≡′ (≤-trans j′<j j<i) j′<j)

 -- If t and a are related, then a is in the El PER model.
®El⇒∈El : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
          Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
          -----------------------------
          a ∈′ El i A≈B
®El⇒∈El (ne C≈C j≡1+i j′≡1+i) (ne c≈c j≡i j≡′i , snd) = ne c≈c j≡i j≡′i
®El⇒∈El N′ (t®Nat , T≈N) = ®Nat⇒∈Nat t®Nat
®El⇒∈El {a = a} {i = i} (U {j} {j′ = _} i≡1+j j≡j′) record { t∶T = t∶T ; T≈ = T≈ ; A∈𝕌 = A∈𝕌 ; rel = rel }
  rewrite 𝕌-wellfounded-≡-𝕌 (1 + j) (≤-reflexive refl) | 𝕌-wf-simpl i | sym (𝕌-wf-simpl j) = A∈𝕌
®El⇒∈El (Π eq jA RT j≡j' k≡k′) t® = a∈El
  where open GluΛ t®
®El⇒∈El (L eq A≈A′ j≡j' k≡k′) t® = a∈El
  where open Glul t®

Glu-wellfounded-≡-Glul : ∀ {j k} →
  (λ {l} l<k → Glu-wellfounded (j + k) {l} (Li≤ refl l<k)) ≡ Glu-wellfounded k
Glu-wellfounded-≡-Glul {j} {k} = implicit-extensionality fext (fext (λ l<k → Glu-wellfounded-≡′ (Li≤ {j + k} refl l<k) l<k))

Glu-wellfounded-≡-GluΛI : ∀ {j k} →
  (λ {l} l<k → Glu-wellfounded (max j k) {l} (ΠI≤ refl l<k)) ≡ Glu-wellfounded j
Glu-wellfounded-≡-GluΛI {j} {k} = implicit-extensionality fext (fext (λ l<k → Glu-wellfounded-≡′ (ΠI≤ {max j k} refl l<k) l<k))

Glu-wellfounded-≡-GluΛO : ∀ {j k} →
  (λ {l} l<k → Glu-wellfounded (max j k) {l} (ΠO≤ refl l<k)) ≡ Glu-wellfounded k
Glu-wellfounded-≡-GluΛO {j} {k} = implicit-extensionality fext (fext (λ l<k → Glu-wellfounded-≡′ (ΠO≤ {max j k} refl l<k) l<k))

Glu-wellfounded-≡-GluU : ∀ {j} →
  (λ {l} l<j → Glu-wellfounded (j) {l} (≤-trans l<j (≤-reflexive refl))) ≡ Glu-wellfounded j
Glu-wellfounded-≡-GluU {j} = implicit-extensionality fext (fext λ l<j → Glu-wellfounded-≡′ (≤-trans l<j (≤-reflexive refl)) l<j)

®El⇒® : ∀ { i } → (A≈B : A ≈ B ∈ 𝕌 i) →
        Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
        ----------------------------
        Γ ⊢ T ®[ i ] A≈B
®El⇒® (ne C≈C j≡1+i j′≡1+i) (ne c≈c j≡i j≡í , record { t∶T = t∶T ; ⊢T = ⊢T ; krip = krip }) = ⊢T , λ ⊢σ → proj₁ (krip ⊢σ)
®El⇒® N′ (_ , T≈N) = T≈N
®El⇒® (U _ _) t® = GluU.T≈ t®
®El⇒® (Π {j = j} {k = k} refl jA RT refl refl) record { t∶T = t∶T ; a∈El = a∈El ; IT = IT ; OT = OT ; ⊢IT = ⊢IT ; ⊢OT = ⊢OT ; T≈ = T≈ ; krip = krip }
  rewrite 𝕌-wf-gen {max j k} k (λ l<k → ΠO≤ refl l<k) | Glu-wellfounded-≡-GluΛO {j} {k} = record
  { IT = IT
  ; OT = OT
  ; ⊢IT = ⊢IT
  ; ⊢OT = ⊢OT
  ; T≈ = T≈
  ; krip = λ ⊢σ → let open ΛRel (krip ⊢σ) in record
      { IT-rel = IT-rel
      ; OT-rel = λ s® a∈ → let open ΛKripke (ap-rel s® a∈) in ®El⇒® (ΠRT.T≈T′ (RT a∈)) ®fa
      }
  }
®El⇒® (L′ {j} {k} kA) record { t∶T = t∶T ; UT = UT ; ⊢UT = ⊢UT ; a∈El = a∈El ; T≈ = T≈ ; krip = krip }
  rewrite 𝕌-wf-gen {j + k} k (λ l<k → Li≤ refl l<k) | Glu-wellfounded-≡-Glul {j} {k} = record
  { UT = UT
  ; ⊢UT = ⊢UT
  ; T≈ = T≈
  ; krip = λ ⊢σ → let open lKripke (krip ⊢σ) in ®El⇒® kA ®ua
  }

-- If t and a are related, then the type of t is well-formed.
®El⇒ty : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
           Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
           ---------------------------
           Γ ⊢ T ∶[ 1 + i ] Se i
®El⇒ty A≈B t∼a = ®⇒ty A≈B (®El⇒® A≈B t∼a)

private
  s:IT®⇒⊢s : ∀ { j k b IT σ s} → 
            (jA : A ≈ A′ ∈ PERDef.𝕌 j (λ l<j → 𝕌-wellfounded (max j k) (ΠI≤ refl l<j))) → 
            Glu.⟦ j , (λ l<j → Glu-wellfounded (max j k) (ΠI≤ refl l<j)) , (λ l<j → 𝕌-wellfounded (max j k) (ΠI≤ refl l<j)) ⟧ Δ ⊢ s ∶ sub IT σ ® b ∈El jA →
            Δ ⊢ s ∶[ j ] sub IT σ
  s:IT®⇒⊢s {j = j} {k = k} jA tr rewrite 𝕌-wf-gen {max j k} j (λ l<k → ΠI≤ refl l<k) | Glu-wellfounded-≡-GluΛI {j} {k} = ®El⇒tm jA tr

-- ®El respects term equivalence.
®El-resp-≈ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
             Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
             Γ ⊢ t ≈ t′ ∶[ i ] T →
             ----------------------------
             Γ ⊢ t′ ∶ T ®[ i ] a ∈El A≈B
®El-resp-≈ (ne C≈C j≡1+i j′≡1+i) (ne c≈c′ refl _ , glu) t≈t′ = ne c≈c′ refl refl , record 
  { t∶T = proj₁ (proj₂ (proj₂ (presup-≈ t≈t′)))
  ; ⊢T = ⊢T
  ; krip = λ ⊢σ → proj₁ (krip ⊢σ) , ≈-trans ([]-cong (≈-sym t≈t′) (s-≈-refl (⊢w⇒⊢s ⊢σ))) (proj₂ (krip ⊢σ)) 
  }
  where open GluNe glu
®El-resp-≈ N′ (t® , T≈N) t≈t′ = ®Nat-resp-≈ t® (≈-conv t≈t′ T≈N) , T≈N
®El-resp-≈ (U {j} refl refl) record { t∶T = t∶T ; T≈ = T≈ ; A∈𝕌 = A∈𝕌 ; rel = rel } t≈t′ 
  rewrite Glu-wellfounded-≡-GluU {j} rewrite 𝕌-wf-gen j (λ l<j → <-trans l<j (s≤s (≤-reflexive refl))) = record
    { t∶T = proj₁ (proj₂ (proj₂ (presup-≈ t≈t′))) 
    ; T≈ = T≈ 
    ; A∈𝕌 = A∈𝕌 
    ; rel = ®-resp-≈ A∈𝕌 rel (≈-conv t≈t′ T≈) 
    }
®El-resp-≈ (Π {j = j} {k = k} refl jA RT refl refl) record { t∶T = t∶T ; a∈El = a∈El ; IT = IT ; OT = OT ; ⊢IT = ⊢IT ; ⊢OT = ⊢OT ; T≈ = T≈ ; krip = krip } t≈t′    
  rewrite Glu-wellfounded-≡-GluΛO {j} {k} = record 
  { t∶T = proj₁ (proj₂ (proj₂ (presup-≈ t≈t′)))
  ; a∈El = a∈El
  ; IT = IT
  ; OT = OT
  ; ⊢IT = ⊢IT
  ; ⊢OT = ⊢OT
  ; T≈ = T≈
  ; krip = λ ⊢σ → let open ΛRel (krip ⊢σ) in record 
      { IT-rel = IT-rel 
      ; ap-rel = λ t® b∈ → 
        let open ΛKripke (ap-rel t® b∈) 
            ⊢σ′     = ⊢w⇒⊢s ⊢σ
            ⊢Δ      = (proj₁ (presup-s ⊢σ′))
            Δ⊢IT[σ] = t[σ]-Se ⊢IT ⊢σ′
            IT,Δ⊢s  = ⊢q ⊢Δ ⊢σ′ ⊢IT
            Δ⊢OT[σ] = t[σ]-Se ⊢OT IT,Δ⊢s
            ⊢s      = s:IT®⇒⊢s jA t®
        in record 
          { fa = fa
          ; ↘fa = ↘fa
          ; ®fa = helper fa jA b∈ RT (≈-conv ($-cong Δ⊢IT[σ] 
                                                     Δ⊢OT[σ] 
                                                     (≈-conv ([]-cong t≈t′ (s-≈-refl ⊢σ′)) 
                                                             (≈-trans ([]-cong-Se′ T≈ ⊢σ′) (Π-[] ⊢σ′ ⊢IT ⊢OT refl))) 
                                                     (≈-refl ⊢s) 
                                                     refl) 
                                             (≈-trans ([∘]-Se ⊢OT 
                                                              IT,Δ⊢s 
                                                              (⊢I,t ⊢Δ Δ⊢IT[σ] ⊢s)) 
                                                      ([]-cong-Se″ ⊢OT 
                                                                   (s-∘ (s-, (s-I ⊢Δ) Δ⊢IT[σ] (conv ⊢s (≈-sym ([I] Δ⊢IT[σ])))) IT,Δ⊢s) 
                                                                   (qσ∘[I,t]≈σ,t ⊢Δ ⊢IT ⊢σ′ ⊢s))))
                            ®fa
          }
      }
  }
  -- extract part of the context that we want to rewrite
  where helper : (fa : D) → 
                 (jA : A ≈ A′ ∈ PERDef.𝕌 j (λ l<j → 𝕌-wellfounded (max j k) (ΠI≤ refl l<j))) → 
                 (b∈ : b ∈′ PERDef.El j (λ l<j → 𝕌-wellfounded (max j k) (ΠI≤ refl l<j)) jA) → 
                 (RT : ∀ {a a′} → a ≈ a′ ∈ PERDef.El j (λ l<j → 𝕌-wellfounded (max j k) (ΠI≤ refl l<j)) jA → ΠRT T (ρ ↦ a) T′ (ρ′ ↦ a′) (PERDef.𝕌 k (λ l<k → 𝕌-wellfounded (max j k) (ΠO≤ refl l<k))) ) → 
                 Δ ⊢ sub t σ $ s ≈ sub t′ σ $ s ∶[ k ] sub OT (σ , s ∶ IT ↙ j) → 
                 Glu.⟦ k , Glu-wellfounded k , (λ l<k → 𝕌-wellfounded (max j k) (ΠO≤ refl l<k))⟧ Δ ⊢ sub t σ $ s ∶ sub OT (σ , s ∶ IT ↙ j) ® fa ∈El ΠRT.T≈T′ (RT b∈) → 
                 -----------------------------------
                 Glu.⟦ k , Glu-wellfounded k , (λ l<k → 𝕌-wellfounded (max j k) (ΠO≤ refl l<k))⟧ Δ ⊢ sub t′ σ $ s ∶ sub OT (σ , s ∶ IT ↙ j) ® fa ∈El ΠRT.T≈T′ (RT b∈)
        helper fa jA b∈ RT t≈t′ ®fa rewrite 𝕌-wf-gen {max j k} k (λ l<k → ΠO≤ refl l<k) = ®El-resp-≈ (ΠRT.T≈T′ (RT b∈)) ®fa t≈t′
®El-resp-≈ {i = i} (L {j = j} {k = k} refl kA refl refl) record { t∶T = t∶T ; UT = UT ; ⊢UT = ⊢UT ; a∈El = a∈El ; T≈ = T≈ ; krip = krip } t≈t′ 
  rewrite Glu-wellfounded-≡-Glul {j} {k} = record 
  { t∶T = proj₁ (proj₂ (proj₂ (presup-≈ t≈t′)))
  ; UT = UT 
  ; ⊢UT = ⊢UT 
  ; a∈El = a∈El
  ; T≈ = T≈
  ; krip = λ ⊢σ → 
      let open lKripke (krip ⊢σ) in record 
      { ua = ua 
      ; ↘ua = ↘ua 
      ; ®ua = helper ([]-cong (unlift-cong j ⊢UT (≈-conv t≈t′ T≈)) (s-≈-refl (⊢w⇒⊢s ⊢σ))) ®ua
      } 
  }
  where helper : {a : D} → 
                 Δ ⊢ sub (unlift t) σ ≈ sub (unlift t′) σ ∶[ k ] sub UT σ → 
                 Glu.⟦ k , Glu-wellfounded k , (λ {l} l<k → 𝕌-wellfounded (j + k) (Li≤ refl l<k)) ⟧ Δ ⊢ sub (unlift t) σ ∶ sub UT σ ® a ∈El kA →  
                 -----------------------------------
                 Glu.⟦ k , Glu-wellfounded k , (λ {l} l<k → 𝕌-wellfounded (j + k) (Li≤ refl l<k)) ⟧ Δ ⊢ sub (unlift t′) σ ∶ sub UT σ ® a ∈El kA 
        helper t≈t′ ®a rewrite 𝕌-wf-gen {j + k} k (λ l<k → Li≤ refl l<k) = ®El-resp-≈ kA ®a t≈t′
        
-- ®El respects context stack equivalence.
®El-resp-⊢≈ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
              Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
              ⊢ Γ ≈ Δ →
              ---------------------------
              Δ ⊢ t ∶ T ®[ i ] a ∈El A≈B
®El-resp-⊢≈ (ne′ x) (ne c≈c′ refl _ , glu) Γ≈Δ = (ne c≈c′ refl refl) , record 
  { t∶T = ctxeq-tm Γ≈Δ t∶T
  ; ⊢T = ctxeq-tm Γ≈Δ ⊢T
  ; krip = λ ⊢σ → krip (⊢w-resp-⊢≈ʳ ⊢σ (⊢≈-sym Γ≈Δ)) 
  }
  where open GluNe glu
®El-resp-⊢≈ N′ (t®N , T≈N) Γ≈Δ = (®Nat-resp-⊢≈ t®N Γ≈Δ) , ctxeq-≈ Γ≈Δ T≈N
®El-resp-⊢≈ (U {j} refl refl) t® Γ≈Δ 
  rewrite Glu-wellfounded-≡-GluU {j} rewrite 𝕌-wf-gen j (λ l<j → <-trans l<j (s≤s (≤-reflexive refl))) = record 
  { t∶T = ctxeq-tm Γ≈Δ t∶T
  ; T≈ = ctxeq-≈ Γ≈Δ T≈
  ; A∈𝕌 = A∈𝕌
  ; rel = ®-resp-⊢≈ A∈𝕌 rel Γ≈Δ
  } 
  where open GluU t®
®El-resp-⊢≈ (Π eq jA x x₁ x₂) t® Γ≈Δ = 
  let Δ⊢IT = ctxeq-tm Γ≈Δ ⊢IT in record
  { t∶T = ctxeq-tm Γ≈Δ t∶T
  ; a∈El = a∈El
  ; IT = IT
  ; OT = OT
  ; ⊢IT = Δ⊢IT
  ; ⊢OT = ctxeq-tm (∷-cong Γ≈Δ ⊢IT Δ⊢IT (≈-refl ⊢IT) (≈-refl Δ⊢IT)) ⊢OT
  ; T≈ = ctxeq-≈ Γ≈Δ T≈
  ; krip = λ ⊢σ → krip (⊢w-resp-⊢≈ʳ ⊢σ (⊢≈-sym Γ≈Δ))
  }
  where open GluΛ t®
®El-resp-⊢≈ (L refl kA refl refl) t® Γ≈Δ = record
  { t∶T = ctxeq-tm Γ≈Δ t∶T 
  ; UT = UT 
  ; ⊢UT = ctxeq-tm Γ≈Δ ⊢UT 
  ; a∈El = a∈El 
  ; T≈ = ctxeq-≈ Γ≈Δ T≈ 
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
               Δ ⊢ T [ σ ] ≈ Ne⇒Exp (proj₁ (c′≈c  (len Δ))) ∶[ 1 + i ] Se i
      helper {Δ} {σ} ⊢σ
        with c≈c′ (len Δ) | c′≈c  (len Δ) | krip ⊢σ
      ...  | _ , ↘u , _ | _ , _ , ↘u₁ | Tσ≈
           rewrite Re-det ↘u ↘u₁ = Tσ≈
  ®-swap N′ N′ T® = T®
  ®-swap (U refl refl) (U i≡1+j j≡j′) T® 
    rewrite ≡-irrelevant i≡1+j refl = T®
  ®-swap {_} {_} {Γ} (Π′ {j} {k} jA RT) (Π i≡maxjk jA′ RT′ j≡j′ k≡k′) record { IT = IT ; OT = OT ; ⊢IT = ⊢IT ; ⊢OT = ⊢OT ; T≈ = T≈ ; krip = krip } 
    rewrite ≡-irrelevant i≡maxjk refl | Glu-wellfounded-≡-GluΛI {j} {k} | Glu-wellfounded-≡-GluΛO {j} {k} | 𝕌-wf-gen {max j k} k (λ l<j → ΠO≤ refl l<j) = record 
    { IT = IT 
    ; OT = OT 
    ; ⊢IT = ⊢IT 
    ; ⊢OT = ⊢OT 
    ; T≈ = T≈ 
    ; krip = λ ⊢σ → let open ΠRel (krip ⊢σ) in record 
      { IT-rel = IT-helper jA jA′ IT-rel
      ; OT-rel = λ s® a∈ → OT-helper refl jA jA′ RT RT′ a∈ s® OT-rel
      }
    }
    -- generalize k′ so that other irrelevant premises won't be affected by rewrite
    where IT-helper : ∀ {k′} → 
                      (jA : A ≈ A′ ∈ PERDef.𝕌 j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))) → 
                      (jA′ : A′ ≈ A ∈ PERDef.𝕌 j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))) → 
                      Glu.⟦ j , Glu-wellfounded j , (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))⟧ Δ ⊢ sub IT σ ® jA → 
                      -----------------------------------
                      Glu.⟦ j , Glu-wellfounded j , (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))⟧ Δ ⊢ sub IT σ ® jA′
          IT-helper {k′ = k′} jA jA′ T® rewrite 𝕌-wf-gen {max j k′} j (λ l<j → ΠI≤ refl l<j) = ®-swap jA jA′ T®
          
          OT-helper : ∀ {k′} → (k′ ≡ k) →  
                      (jA : A ≈ A′ ∈ PERDef.𝕌 j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))) → 
                      (jA′ : A′ ≈ A ∈ PERDef.𝕌 j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))) → 
                      (RT : ∀ {a a′} → a ≈ a′ ∈ PERDef.El j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j)) jA → ΠRT T (ρ ↦ a) T′ (ρ′ ↦ a′) (PERDef.𝕌 k′ (𝕌-wellfounded k′) )) → 
                      (RT′ : ∀ {a a′} → a ≈ a′ ∈ PERDef.El j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j)) jA′ → ΠRT T′ (ρ′ ↦ a) T (ρ ↦ a′) (PERDef.𝕌 k′ (𝕌-wellfounded k′) )) → 
                      (a∈′ : a ∈′ PERDef.El j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j)) jA′) → 
                      Glu.⟦ j , Glu-wellfounded j , (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))⟧ Δ ⊢ s ∶ sub IT σ ® a ∈El jA′ → 
                      (∀ {s a} → Glu.⟦ j , Glu-wellfounded j , (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j)) ⟧ Δ ⊢ s ∶ sub IT σ ® a ∈El jA →
                        (a∈ : a ∈′ PERDef.El j (λ g → 𝕌-wellfounded (max j k′) (ΠI≤ refl g)) jA) → 
                        Glu.⟦ k′ , Glu-wellfounded k′ , 𝕌-wellfounded k′ ⟧ Δ ⊢ sub OT (σ , s ∶ IT ↙ j) ® ΠRT.T≈T′ (RT a∈)) → 
                      --------------------------------------------------------------
                      Glu.⟦ k′ , Glu-wellfounded k′ , 𝕌-wellfounded k′ ⟧ Δ ⊢ sub OT (σ , s ∶ IT ↙ j) ® ΠRT.T≈T′ (RT′ a∈′)
          OT-helper {k′ = k′} k′≡k jA jA′ RT RT′ a∈′ s® OT-rel rewrite 𝕌-wf-gen {max j k′} j (λ l<j → ΠI≤ refl l<j) | k′≡k 
            with El-sym jA′ jA a∈′
          ... | a∈ 
              with (RT a∈) | RT′ a∈′ | OT-rel (®El-swap jA′ jA s®) a∈
          ... | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
              | record { ↘⟦T⟧ = ↘⟦T′⟧₁ ; ↘⟦T′⟧ = ↘⟦T⟧₁ ; T≈T′ = T′≈T } 
              | R 
              rewrite ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₁
                    | ⟦⟧-det ↘⟦T′⟧ ↘⟦T′⟧₁ = ®-swap T≈T′ T′≈T R

  ®-swap (L′ {j} {k} kA) (L i≡j+k kA′ _ _) record { UT = UT ; ⊢UT = ⊢UT ; T≈ = T≈ ; krip = krip } 
    rewrite ≡-irrelevant i≡j+k refl | Glu-wellfounded-≡-Glul {j} {k} = record 
    { UT = UT 
    ; ⊢UT = ⊢UT 
    ; T≈ = T≈ 
    ; krip = λ ⊢σ → helper kA kA′ (krip ⊢σ) 
    }
    where helper : (kA : A ≈ A′ ∈ PERDef.𝕌 k (λ l<k → 𝕌-wellfounded (j + k) (Li≤ refl l<k))) → 
                  (kA′ : A′ ≈ A ∈ PERDef.𝕌 k (λ l<k → 𝕌-wellfounded (j + k) (Li≤ refl l<k))) → 
                  Glu.⟦ k , Glu-wellfounded k , (λ {l} l<k → 𝕌-wellfounded (j + k) (Li≤ refl l<k))⟧ Δ ⊢ sub UT σ ® kA → 
                  -----------------------------------
                  Glu.⟦ k , Glu-wellfounded k , (λ {l} l<k → 𝕌-wellfounded (j + k) (Li≤ refl l<k))⟧ Δ ⊢ sub UT σ ® kA′
          helper kA kA′ T® rewrite 𝕌-wf-gen {j + k} k (λ l<k → Li≤ refl l<k) = ®-swap kA kA′ T®
    
  ®El-swap : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i)
             (B≈A : B ≈ A ∈ 𝕌 i) →
             Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
             ----------------------------
             Γ ⊢ t ∶ T ®[ i ] a ∈El B≈A
  ®El-swap {_} {_} {Γ} {t} {T} {i = i} (ne′ C≈C′) (ne C′≈C _ _) (ne c≈c refl _ , glu) = (ne c≈c refl refl) , record 
    { t∶T = t∶T
    ; ⊢T = ⊢T
    ; krip = λ ⊢σ → krip′ ⊢σ 
    }
    where
      open GluNe glu
      krip′ : Δ ⊢w σ ∶ Γ →
               -----------------------------------
               Δ ⊢ sub T σ ≈ Ne⇒Exp (proj₁ (C′≈C (L.length Δ))) ∶[ ℕ.suc i ] Se i
                 × Δ ⊢ sub t σ ≈ Ne⇒Exp (proj₁ (c≈c (L.length Δ))) ∶[ i ] sub T σ
      krip′ {Δ} {σ} ⊢σ
        with C≈C′ (len Δ) | C′≈C (len Δ) | krip ⊢σ
      ...  | _ , ↘u , _ | _ , _ , ↘u₁ | Tσ≈ , tσ≈ 
           rewrite Re-det ↘u ↘u₁ = Tσ≈ , tσ≈
  ®El-swap N′ N′ T® = T®
  ®El-swap U′ (U i≡1+j j≡j′) T® 
    rewrite ≡-irrelevant i≡1+j refl = T®
  ®El-swap (Π′ {j} {k} jA RT) (Π i≡maxjk jA′ RT′ j≡j′ k≡k′) record { t∶T = t∶T ; a∈El = a∈El ; IT = IT ; OT = OT ; ⊢IT = ⊢IT ; ⊢OT = ⊢OT ; T≈ = T≈ ; krip = krip } 
    rewrite ≡-irrelevant i≡maxjk refl | Glu-wellfounded-≡-GluΛI {j} {k} | Glu-wellfounded-≡-GluΛO {j} {k} = record
    { t∶T = t∶T
    ; a∈El = El-sym (Π′ jA RT) (Π′ jA′ RT′) a∈El
    ; IT = IT
    ; OT = OT
    ; ⊢IT = ⊢IT
    ; ⊢OT = ⊢OT
    ; T≈ = T≈
    ; krip = λ ⊢σ → let open ΛRel (krip ⊢σ) in record
      { IT-rel = IT-helper jA jA′ IT-rel 
      ; ap-rel = λ s® b∈ → ap-helper refl jA jA′ RT RT′ b∈ s® ap-rel 
      } 
    }
    where IT-helper : ∀ {k′} → 
                      (jA : A ≈ A′ ∈ PERDef.𝕌 j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))) → 
                      (jA′ : A′ ≈ A ∈ PERDef.𝕌 j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))) → 
                      Glu.⟦ j , Glu-wellfounded j , (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))⟧ Δ ⊢ sub IT σ ® jA → 
                      -----------------------------------
                      Glu.⟦ j , Glu-wellfounded j , (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))⟧ Δ ⊢ sub IT σ ® jA′
          IT-helper {k′ = k′} jA jA′ T® rewrite 𝕌-wf-gen {max j k′} j (λ l<j → ΠI≤ refl l<j) = ®-swap jA jA′ T®

          ap-helper : ∀ {k′} → 
                      (k′ ≡ k) → 
                      (jA : A ≈ A′ ∈ PERDef.𝕌 j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))) → 
                      (jA′ : A′ ≈ A ∈ PERDef.𝕌 j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))) → 
                      (RT : ∀ {a a′} → a ≈ a′ ∈ PERDef.El j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j)) jA → ΠRT T (ρ ↦ a) T′ (ρ′ ↦ a′) (PERDef.𝕌 k′ (λ l<k → 𝕌-wellfounded (max j k′) (ΠO≤ refl l<k)) )) → 
                      (RT′ : ∀ {a a′} → a ≈ a′ ∈ PERDef.El j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j)) jA′ → ΠRT T′ (ρ′ ↦ a) T (ρ ↦ a′) (PERDef.𝕌 k′ (λ l<k → 𝕌-wellfounded (max j k′) (ΠO≤ refl l<k)) )) → 
                      (b∈′ : b ∈′ PERDef.El j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j)) jA′) → 
                      Glu.⟦ j , Glu-wellfounded j , (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))⟧ Δ ⊢ s ∶ sub IT σ ® b ∈El jA′ → 
                      (∀ {s b} → Glu.⟦ j , Glu-wellfounded j , (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))⟧ Δ ⊢ s ∶ sub IT σ ® b ∈El jA →
                        (a∈ : b ∈′ PERDef.El j (λ g → 𝕌-wellfounded (max j k′) (ΠI≤ refl g)) jA) → 
                        ΛKripke Δ (sub t σ $ s) (sub OT (σ , s ∶ IT ↙ j)) a b (Glu.⟦ k′ , Glu-wellfounded k′ , (λ l<k → 𝕌-wellfounded (max j k′) (ΠO≤ refl l<k)) ⟧_⊢_∶_®_∈El ΠRT.T≈T′ (RT a∈)) ) →      
                      --------------------------------------------------------------
                      ΛKripke Δ (sub t σ $ s) (sub OT (σ , s ∶ IT ↙ j)) a b (Glu.⟦ k′ , Glu-wellfounded k′ , (λ l<k → 𝕌-wellfounded (max j k′) (ΠO≤ refl l<k))⟧_⊢_∶_®_∈El ΠRT.T≈T′ (RT′ b∈′))
          ap-helper {k′ = k′} k′≡k jA jA′ RT RT′ b∈′ s® ap-rel rewrite 𝕌-wf-gen {max j k′} j (λ l<j → ΠI≤ refl l<j) | 𝕌-wf-gen {max j k′} k′ (λ l<j → ΠO≤ refl l<j) | k′≡k 
             with El-sym jA′ jA b∈′
          ...  | b∈ 
              with RT b∈ | RT′ b∈′ | ap-rel (®El-swap jA′ jA s®) b∈ 
          ... | record { ↘⟦T⟧ = ↘⟦T⟧ ; ↘⟦T′⟧ = ↘⟦T′⟧ ; T≈T′ = T≈T′ }
              | record { ↘⟦T⟧ = ↘⟦T′⟧₁ ; ↘⟦T′⟧ = ↘⟦T⟧₁ ; T≈T′ = T′≈T } 
              | record { fa = fa ; ↘fa = ↘fa ; ®fa = ®fa } 
              rewrite ⟦⟧-det ↘⟦T⟧ ↘⟦T⟧₁
                    | ⟦⟧-det ↘⟦T′⟧ ↘⟦T′⟧₁ = record { fa = fa ; ↘fa = ↘fa ; ®fa = ®El-swap T≈T′ T′≈T ®fa }      
  
  ®El-swap (L′ {j} {k} kA) (L i≡j+k kA′ j≡j′ k≡k′) record { t∶T = t∶T ; UT = UT ; ⊢UT = ⊢UT ; a∈El = a∈El ; T≈ = T≈ ; krip = krip } 
    rewrite ≡-irrelevant i≡j+k refl | Glu-wellfounded-≡-Glul {j} {k} = record
    { t∶T = t∶T 
    ; UT = UT 
    ; ⊢UT = ⊢UT 
    ; a∈El = let open Unli a∈El in record 
        { ua = ua 
        ; ub = ub 
        ; ↘ua = ↘ua 
        ; ↘ub = ↘ub 
        ; ua≈ub = helper kA kA′ ua≈ub 
        }
    ; T≈ = T≈ 
    ; krip = λ ⊢σ → let open lKripke (krip ⊢σ) in record { ua = ua ; ↘ua = ↘ua ; ®ua = helper2 kA kA′ ®ua }
    }
    where helper : (kA : A ≈ A′ ∈ PERDef.𝕌 k (λ l<k → 𝕌-wellfounded (j + k) (Li≤ refl l<k))) → 
                   (kA′ : A′ ≈ A ∈ PERDef.𝕌 k (λ l<k → 𝕌-wellfounded (j + k) (Li≤ refl l<k))) → 
                   a ≈ b ∈ PERDef.El k (λ l<k → 𝕌-wellfounded (j + k) (Li≤ refl l<k)) kA → 
                   -----------------------------------
                   a ≈ b ∈ PERDef.El k (λ l<k → 𝕌-wellfounded (j + k) (Li≤ refl l<k)) kA′
          helper kA kA′ a≈a′ rewrite 𝕌-wf-gen {j + k} k (λ l<k → Li≤ refl l<k) = El-swap kA kA′ a≈a′

          helper2 : {a : D} → 
                    (kA : A ≈ A′ ∈ PERDef.𝕌 k (λ l<k → 𝕌-wellfounded (j + k) (Li≤ refl l<k))) → 
                    (kA′ : A′ ≈ A ∈ PERDef.𝕌 k (λ l<k → 𝕌-wellfounded (j + k) (Li≤ refl l<k))) → 
                    Glu.⟦ k , Glu-wellfounded k , (λ {l} l<k → 𝕌-wellfounded (j + k) (Li≤ refl l<k)) ⟧ Δ ⊢ sub (unlift t) σ ∶ sub UT σ ® a ∈El kA → 
                    -----------------------------------
                    Glu.⟦ k , Glu-wellfounded k , (λ {l} l<k → 𝕌-wellfounded (j + k) (Li≤ refl l<k)) ⟧ Δ ⊢ sub (unlift t) σ ∶ sub UT σ ® a ∈El kA′
          helper2  kA kA′ ®a rewrite 𝕌-wf-gen {j + k} k (λ l<k → Li≤ refl l<k) = ®El-swap kA kA′ ®a


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
          ...  | u , ↘u , _ | u′ , ↘u′ , _ | Tσ≈
               rewrite Re-det ↘u ↘u′ = Tσ≈
  ®-one-sided N′ N′ T® = T®
  ®-one-sided (U′ {_}) (U i≡1+j j≡j′) T® 
   rewrite ≡-irrelevant i≡1+j refl = T®
  ®-one-sided {_} {_} {Γ} (Π′ {j} {k} jA RT) (Π i≡maxjk jA′ RT′ _ _) record { IT = IT ; OT = OT ; ⊢IT = ⊢IT ; ⊢OT = ⊢OT ; T≈ = T≈ ; krip = krip } 
    rewrite ≡-irrelevant i≡maxjk refl | Glu-wellfounded-≡-GluΛI {j} {k} |  Glu-wellfounded-≡-GluΛO {j} {k} | 𝕌-wf-gen {max j k} k (λ l<j → ΠO≤ refl l<j) = record 
    { IT = IT 
    ; OT = OT 
    ; ⊢IT = ⊢IT 
    ; ⊢OT = ⊢OT 
    ; T≈ = T≈ 
    ; krip = λ ⊢σ → 
      let open ΠRel (krip ⊢σ) 
      in record 
      { IT-rel = IT-helper jA jA′ IT-rel 
      ; OT-rel = λ s® a∈ → OT-helper refl jA jA′ RT RT′ a∈ s® OT-rel
      } 
    }
    -- generalize k′ so that other irrelevant premises won't be affected by rewrite
    where IT-helper : ∀ {k′} → 
                      (jA : A ≈ A′ ∈ PERDef.𝕌 j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))) → 
                      (jA′ : A ≈ A″ ∈ PERDef.𝕌 j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))) → 
                      Glu.⟦ j , Glu-wellfounded j , (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))⟧ Δ ⊢ sub IT σ ® jA → 
                      -----------------------------------
                      Glu.⟦ j , Glu-wellfounded j , (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))⟧ Δ ⊢ sub IT σ ® jA′
          IT-helper {k′ = k′} jA jA′ T® rewrite 𝕌-wf-gen {max j k′} j (λ l<j → ΠI≤ refl l<j) = ®-one-sided jA jA′ T®

          OT-helper : ∀ {k′} → (k′ ≡ k) →  
                     (jA : A ≈ A′ ∈ PERDef.𝕌 j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))) → 
                     (jA′ : A ≈ A″  ∈ PERDef.𝕌 j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))) → 
                     (RT : ∀ {a a′} → a ≈ a′ ∈ PERDef.El j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j)) jA → ΠRT T (ρ ↦ a) T′ (ρ′ ↦ a′) (PERDef.𝕌 k′ (𝕌-wellfounded k′) )) → 
                     (RT′ : ∀ {a a″} → a ≈ a″ ∈ PERDef.El j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j)) jA′ → ΠRT T (ρ ↦ a) T″ (ρ″ ↦ a″) (PERDef.𝕌 k′ (𝕌-wellfounded k′) )) → 
                     (a∈′ : a ∈′ PERDef.El j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j)) jA′) → 
                     Glu.⟦ j ,  Glu-wellfounded j , (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))⟧ Δ ⊢ s ∶ sub IT σ ® a ∈El jA′ → 
                     (∀ {s a} → Glu.⟦ j , Glu-wellfounded j , (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j)) ⟧ Δ ⊢ s ∶ sub IT σ ® a ∈El jA →
                       (a∈ : a ∈′ PERDef.El j (λ g → 𝕌-wellfounded (max j k′) (ΠI≤ refl g)) jA) → 
                       Glu.⟦ k′ , Glu-wellfounded k′ , 𝕌-wellfounded k′ ⟧ Δ ⊢ sub OT (σ , s ∶ IT ↙ j) ® ΠRT.T≈T′ (RT a∈)) → 
                     --------------------------------------------------------------
                    Glu.⟦ k′ , Glu-wellfounded k′ , 𝕌-wellfounded k′ ⟧ Δ ⊢ sub OT (σ , s ∶ IT ↙ j) ® ΠRT.T≈T′ (RT′ a∈′)
          OT-helper {k′ = k′} k′≡k jA jA′ RT RT′ a∈′ s® OT-rel rewrite 𝕌-wf-gen {max j k′} j (λ l<j → ΠI≤ refl l<j) | k′≡k 
            with El-one-sided jA′ jA a∈′ 
          ... | a∈ 
              with (RT a∈) | RT′ a∈′ | OT-rel (®El-one-sided jA′ jA s®) a∈ 
          ... | record { ⟦T⟧ = ⟦T⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; T≈T′ = T≈T′ }
              | record { ↘⟦T⟧ = ↘⟦T⟧′ ; T≈T′ = T≈T′₁ }
              | R 
              rewrite ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧ = ®-one-sided T≈T′ T≈T′₁ R
  ®-one-sided (L′ {j} {k} kA) (L i≡j+k kA′ j≡j′ k≡k′) record { UT = UT ; ⊢UT = ⊢UT ; T≈ = T≈ ; krip = krip } 
    rewrite ≡-irrelevant i≡j+k refl | Glu-wellfounded-≡-Glul {j} {k} = record 
    { UT = UT
    ; ⊢UT = ⊢UT
    ; T≈ = T≈
    ; krip = λ ⊢σ → helper kA kA′ (krip ⊢σ) 
    }
    where helper : (kA : A ≈ A′ ∈ PERDef.𝕌 k (λ l<k → 𝕌-wellfounded (j + k) (Li≤ refl l<k))) → 
                   (kA′ : A ≈ A″ ∈ PERDef.𝕌 k (λ l<k → 𝕌-wellfounded (j + k) (Li≤ refl l<k))) → 
                   Glu.⟦ k , Glu-wellfounded k , (λ {l} l<k → 𝕌-wellfounded (j + k) (Li≤ refl l<k))⟧ Δ ⊢ sub UT σ ® kA → 
                   -----------------------------------
                   Glu.⟦ k , Glu-wellfounded k , (λ {l} l<k → 𝕌-wellfounded (j + k) (Li≤ refl l<k))⟧ Δ ⊢ sub UT σ ® kA′
          helper kA kA′ T® rewrite 𝕌-wf-gen {j + k} k (λ l<k → Li≤ refl l<k) = ®-one-sided kA kA′ T®

  ®El-one-sided : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i)
                (A≈B′ : A ≈ B′ ∈ 𝕌 i) →
                Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
                ----------------------------
                Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B′
  ®El-one-sided {Γ = Γ} {t} {T} {_} {i} (ne′ C≈C′) (ne C≈C″ _ _) (ne c≈c refl _ , glu) = (ne c≈c refl refl) , record 
    { t∶T = t∶T
    ; ⊢T = ⊢T
    ; krip = krip′ 
    }
    where open GluNe glu
          krip′ : Δ ⊢w σ ∶ Γ →
                  -----------------------------------
                  Δ ⊢ sub T σ ≈ Ne⇒Exp (proj₁ (C≈C″ (L.length Δ))) ∶[ ℕ.suc i ] Se i
                  × Δ ⊢ sub t σ ≈ Ne⇒Exp (proj₁ (c≈c (L.length Δ))) ∶[ i ] sub T σ
          krip′ {Δ} {σ} ⊢σ
            with C≈C′ (len Δ) | C≈C″ (len Δ) | krip ⊢σ
          ...  | u , ↘u , _ | u′ , ↘u′ , _ | Tσ≈ , tσ≈
               rewrite Re-det ↘u ↘u′ = Tσ≈ , tσ≈
  ®El-one-sided N′ N′ t® = t®
  ®El-one-sided (U′ {_}) (U i≡1+j j≡j′) t® 
    rewrite ≡-irrelevant i≡1+j refl = t®
  ®El-one-sided (Π′ {j} {k} jA RT) (Π i≡maxjk jA′ RT′ _ _) record { t∶T = t∶T ; a∈El = a∈El ; IT = IT ; OT = OT ; ⊢IT = ⊢IT ; ⊢OT = ⊢OT ; T≈ = T≈ ; krip = krip } 
    rewrite ≡-irrelevant i≡maxjk refl | Glu-wellfounded-≡-GluΛI {j} {k} | Glu-wellfounded-≡-GluΛO {j} {k} = record
    { t∶T = t∶T
    ; a∈El = El-one-sided (Π′ jA RT) (Π′ jA′ RT′) a∈El
    ; IT = IT
    ; OT = OT
    ; ⊢IT = ⊢IT
    ; ⊢OT = ⊢OT
    ; T≈ = T≈
    ; krip =  λ ⊢σ → 
      let open ΛRel (krip ⊢σ) 
      in record 
      { IT-rel = IT-helper jA jA′ IT-rel
      ; ap-rel = λ s® b∈ → ap-helper refl jA jA′ RT RT′ b∈ s® ap-rel 
      } 
    }
    where IT-helper : ∀ {k′} → 
                  (jA : A ≈ A′ ∈ PERDef.𝕌 j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))) → 
                  (jA′ : A ≈ A″ ∈ PERDef.𝕌 j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))) → 
                  Glu.⟦ j , Glu-wellfounded j , (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))⟧ Δ ⊢ sub IT σ ® jA → 
                  -----------------------------------
                  Glu.⟦ j , Glu-wellfounded j , (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))⟧ Δ ⊢ sub IT σ ® jA′
          IT-helper {k′ = k′} jA jA′ T® rewrite 𝕌-wf-gen {max j k′} j (λ l<j → ΠI≤ refl l<j) = ®-one-sided jA jA′ T®
          ap-helper : ∀ {k′} → 
                     (k′ ≡ k) → 
                     (jA : A ≈ A′ ∈ PERDef.𝕌 j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))) → 
                     (jA′ : A ≈ A″ ∈ PERDef.𝕌 j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))) → 
                     (RT : ∀ {a a′} → a ≈ a′ ∈ PERDef.El j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j)) jA → ΠRT T (ρ ↦ a) T′ (ρ′ ↦ a′) (PERDef.𝕌 k′ (λ l<k → 𝕌-wellfounded (max j k′) (ΠO≤ refl l<k)) )) → 
                     (RT′ : ∀ {a a″} → a ≈ a″ ∈ PERDef.El j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j)) jA′ → ΠRT T (ρ ↦ a) T″ (ρ″ ↦ a″ ) (PERDef.𝕌 k′ (λ l<k → 𝕌-wellfounded (max j k′) (ΠO≤ refl l<k)) )) → 
                     (b∈′ : b ∈′ PERDef.El j (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j)) jA′) → 
                     Glu.⟦ j ,  Glu-wellfounded j , (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))⟧ Δ ⊢ s ∶ sub IT σ ® b ∈El jA′ → 
                     (∀ {s b} → Glu.⟦ j ,  Glu-wellfounded j , (λ l<j → 𝕌-wellfounded (max j k′) (ΠI≤ refl l<j))⟧ Δ ⊢ s ∶ sub IT σ ® b ∈El jA →
                       (a∈ : b ∈′ PERDef.El j (λ g → 𝕌-wellfounded (max j k′) (ΠI≤ refl g)) jA) → 
                       ΛKripke Δ (sub t σ $ s) (sub OT (σ , s ∶ IT ↙ j)) a b (Glu.⟦ k′ , Glu-wellfounded k′ , (λ l<k → 𝕌-wellfounded (max j k′) (ΠO≤ refl l<k)) ⟧_⊢_∶_®_∈El ΠRT.T≈T′ (RT a∈)) ) →      
                     --------------------------------------------------------------
                     ΛKripke Δ (sub t σ $ s) (sub OT (σ , s ∶ IT ↙ j)) a b (Glu.⟦ k′ , Glu-wellfounded k′ , (λ l<k → 𝕌-wellfounded (max j k′) (ΠO≤ refl l<k))⟧_⊢_∶_®_∈El ΠRT.T≈T′ (RT′ b∈′))
          ap-helper {k′ = k′} k′≡k jA jA′ RT RT′ b∈′ s® ap-rel rewrite 𝕌-wf-gen {max j k′} j (λ l<j → ΠI≤ refl l<j) | 𝕌-wf-gen {max j k′} k′ (λ l<j → ΠO≤ refl l<j) | k′≡k 
             with El-one-sided jA′ jA b∈′
          ... | b∈ 
              with RT b∈ | RT′ b∈′ | ap-rel (®El-one-sided jA′ jA s®) b∈
          ... | record { ⟦T⟧ = ⟦T⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; T≈T′ = T≈T′ }
              | record { ↘⟦T⟧ = ↘⟦T⟧′ ; T≈T′ = T≈T′₁ } 
              | R  
                rewrite ⟦⟧-det ↘⟦T⟧′ ↘⟦T⟧ = record { fa = fa ; ↘fa = ↘fa ; ®fa = ®El-one-sided T≈T′ T≈T′₁ ®fa }
              where open ΛKripke R

  ®El-one-sided (L′ {j} {k} kA) (L i≡j+k kA′ _ _) record { t∶T = t∶T ; UT = UT ; ⊢UT = ⊢UT ; a∈El = a∈El ; T≈ = T≈ ; krip = krip } 
    rewrite ≡-irrelevant i≡j+k refl | Glu-wellfounded-≡-Glul {j} {k} = record 
    { t∶T = t∶T 
    ; UT = UT 
    ; ⊢UT = ⊢UT 
    ; a∈El = 
      let open Unli a∈El 
      in record 
      { ua = ua 
      ; ub = ub 
      ; ↘ua = ↘ua 
      ; ↘ub = ↘ub 
      ; ua≈ub = helper kA kA′ ua≈ub 
      } 
    ; T≈ = T≈ 
    ; krip = λ ⊢σ → 
      let open lKripke (krip ⊢σ) 
      in record 
      { ua = ua 
      ; ↘ua = ↘ua 
      ; ®ua = helper2 kA kA′ ®ua  
      } 
    }
    where helper : (kA : A ≈ A′ ∈ PERDef.𝕌 k (λ l<k → 𝕌-wellfounded (j + k) (Li≤ refl l<k))) → 
                   (kA′ : A ≈ A″ ∈ PERDef.𝕌 k (λ l<k → 𝕌-wellfounded (j + k) (Li≤ refl l<k))) → 
                   a ≈ b ∈ PERDef.El k (λ l<k → 𝕌-wellfounded (j + k) (Li≤ refl l<k)) kA → 
                   -----------------------------------
                   a ≈ b ∈ PERDef.El k (λ l<k → 𝕌-wellfounded (j + k) (Li≤ refl l<k)) kA′
          helper kA kA′ a≈a′ rewrite 𝕌-wf-gen {j + k} k (λ l<k → Li≤ refl l<k) = El-one-sided kA kA′ a≈a′

          helper2 : {a : D} → 
                    (kA : A ≈ A′ ∈ PERDef.𝕌 k (λ l<k → 𝕌-wellfounded (j + k) (Li≤ refl l<k))) → 
                    (kA′ : A ≈ A″ ∈ PERDef.𝕌 k (λ l<k → 𝕌-wellfounded (j + k) (Li≤ refl l<k))) → 
                    Glu.⟦ k , Glu-wellfounded k , (λ {l} l<k → 𝕌-wellfounded (j + k) (Li≤ refl l<k)) ⟧ Δ ⊢ sub (unlift t) σ ∶ sub UT σ ® a ∈El kA → 
                    -----------------------------------
                    Glu.⟦ k , Glu-wellfounded k , (λ {l} l<k → 𝕌-wellfounded (j + k) (Li≤ refl l<k)) ⟧ Δ ⊢ sub (unlift t) σ ∶ sub UT σ ® a ∈El kA′
          helper2  kA kA′ ®a rewrite 𝕌-wf-gen {j + k} k (λ l<k → Li≤ refl l<k) = ®El-one-sided kA kA′ ®a
              