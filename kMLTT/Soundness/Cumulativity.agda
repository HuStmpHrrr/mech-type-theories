{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

-- prove that the gluing model is cumulative
module kMLTT.Soundness.Cumulativity (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Data.Nat.Properties as ℕₚ

open import kMLTT.Statics.Properties
open import kMLTT.Semantics.Readback
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Soundness.LogRel
open import kMLTT.Soundness.Realizability fext
open import kMLTT.Soundness.Properties.LogRel fext


®⇒≈ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
      Γ ⊢ T ®[ i ] A≈B →
      Γ ⊢ T′ ®[ i ] A≈B →
      ----------------------------
      Γ ⊢ T ≈ T′ ∶ Se i
®⇒≈ {_} {_} {_} {T} {T′} (ne C≈C′) (⊢T , rel) (⊢T′ , rel′)
  with presup-tm ⊢T
...  | ⊢Γ , _           = begin
  T        ≈˘⟨ [I] ⊢T ⟩
  T [ I ]  ≈⟨ rel (⊢rI ⊢Γ) ⟩
  _        ≈˘⟨ rel′ (⊢rI ⊢Γ) ⟩
  T′ [ I ] ≈⟨ [I] ⊢T′ ⟩
  T′       ∎
  where open ER
®⇒≈ N T∼A T′∼A          = ≈-trans T∼A (≈-sym T′∼A)
®⇒≈ (U j<i eq) T∼A T′∼A = ≈-trans T∼A (≈-sym T′∼A)
®⇒≈ {_} {_} {_} {T} {T′} (□ A≈B) T∼A T′∼A
  with presup-≈ (Glu□.T≈ T∼A)
...  | ⊢Γ , _           = begin
  T                    ≈⟨ T.T≈ ⟩
  □ T.GT               ≈˘⟨ □-cong ([I；1] (®□⇒wf A≈B T∼A)) ⟩
  □ (T.GT [ I ； 1 ])  ≈⟨ □-cong (®⇒≈ (A≈B (ins vone 1)) (T.krip L.[ [] ] (⊢rI ⊢Γ)) (T′.krip L.[ [] ] (⊢rI ⊢Γ))) ⟩
  □ (T′.GT [ I ； 1 ]) ≈⟨ □-cong ([I；1] (®□⇒wf A≈B T′∼A)) ⟩
  □ T′.GT              ≈˘⟨ T′.T≈ ⟩
  T′                   ∎
  where module T  = Glu□ T∼A
        module T′ = Glu□ T′∼A
        open ER
®⇒≈ {Π A _ _} {_} {_} {T} {T′} (Π iA RT) T∼A T′∼A
  with presup-≈ (GluΠ.T≈ T∼A) | ®Π-wf iA RT T∼A | ®Π-wf iA RT T′∼A
...  | ⊢Γ , _ | ⊢IT | ⊢IT′
     with ®El-resp-T≈ (iA (mt I)) (v0®x (iA (mt I)) (ΠRel.IT-rel (GluΠ.krip T∼A (⊢rI ⊢Γ)))) ([]-cong-Se′ ([I] ⊢IT) (s-wk (⊢∺ ⊢Γ (t[σ]-Se ⊢IT (s-I ⊢Γ)))))
...     | v∼l               = begin
  T                                    ≈⟨ T.T≈ ⟩
  Π T.IT T.OT                          ≈˘⟨ Π-cong ([I] ⊢IT) ([wk,v0] (ctxeq-tm (∺-cong (⊢≈-refl ⊢Γ) (≈-sym ([I] ⊢IT))) T.⊢OT)) ⟩
  Π (T.IT [ I ]) (T.OT [ wk , v 0 ])   ≈⟨ Π-cong ([]-cong-Se′ IT≈IT′ (s-I ⊢Γ))
                                                 (®⇒≈ (ΠRT.T≈T′ (RT (mt wk) l∈))
                                                      (ΠRel.OT-rel (T.krip (⊢rwk ⊢ITΓ)) v∼l l∈)
                                                      (ΠRel.OT-rel (T′.krip (⊢rwk ⊢ITΓ)) (®El-resp-T≈ (iA vone) v∼l ([]-cong-Se′ IT≈IT′ (s-wk ⊢ITΓ))) l∈)) ⟩
  Π (T′.IT [ I ]) (T′.OT [ wk , v 0 ]) ≈⟨ Π-cong ([I] (®Π-wf iA RT T′∼A)) ([wk,v0] (ctxeq-tm (∺-cong (⊢≈-refl ⊢Γ) (≈-sym ([I] ⊢IT′))) T′.⊢OT)) ⟩
  Π T′.IT T′.OT                        ≈˘⟨ T′.T≈ ⟩
  T′                                   ∎
  where module T  = GluΠ T∼A
        module T′ = GluΠ T′∼A
        open ER
        IT-rel = ΠRel.IT-rel (T.krip (⊢rI ⊢Γ))
        IT-rel′ = ΠRel.IT-rel (T′.krip (⊢rI ⊢Γ))
        IT≈IT′ = ≈-trans (≈-sym ([I] ⊢IT)) (≈-trans (®⇒≈ (iA (mt I)) IT-rel IT-rel′) ([I] (®Π-wf iA RT T′∼A)))
        l∈ = ®El⇒∈El (iA vone) v∼l
        ⊢ITΓ = ⊢∺ ⊢Γ (t[σ]-Se ⊢IT (s-I ⊢Γ))


®El⇒≈ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
        Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
        Γ ⊢ t′ ∶ T ®[ i ] a ∈El A≈B →
        ----------------------------
        Γ ⊢ t ≈ t′ ∶ T
®El⇒≈ {_} {_} {Γ} {t} {_} {_} {t′} A≈B@(ne C≈C′) t∼a@(ne c∈⊥ , rel) t′∼a@(ne c∈⊥′ , rel′)
  with presup-tm (GluNe.t∶T rel)
...  | ⊢Γ , _ = begin
  t        ≈˘⟨ [I] ⊢t ⟩
  t [ I ]  ≈⟨ subst (Γ ⊢ _ ≈_∶ _)
                    (cong Ne⇒Exp (Re-det (proj₁ (proj₂ (c∈⊥ (map len Γ) vone))) (proj₁ (proj₂ (c∈⊥′ (map len Γ) vone)))))
                    (≈-conv (proj₂ (rel.krip (⊢rI ⊢Γ))) ([I] ⊢T)) ⟩
  _        ≈˘⟨ ≈-conv (proj₂ (rel′.krip (⊢rI ⊢Γ))) ([I] ⊢T) ⟩
  t′ [ I ] ≈⟨ [I] ⊢t′ ⟩
  t′       ∎
  where module rel  = GluNe rel
        module rel′ = GluNe rel′
        open ER
        T≈T′ = ®⇒≈ A≈B (®El⇒® A≈B t∼a) (®El⇒® A≈B t′∼a)
        ⊢T   = ®El⇒ty A≈B t∼a
        ⊢t   = ®El⇒tm A≈B t∼a
        ⊢t′  = ®El⇒tm A≈B t′∼a
®El⇒≈ N (t∼a , T≈) (t′∼a , _)
  with presup-≈ T≈
...  | ⊢Γ , _ = ≈-conv (®Nat⇒tm≈ ⊢Γ t∼a t′∼a) (≈-sym T≈)
®El⇒≈ (U j<i eq) t∼a t′∼a
  rewrite Glu-wellfounded-≡ j<i = ≈-conv (®⇒≈ r.A∈𝕌 r.rel (®-one-sided r′.A∈𝕌 r.A∈𝕌 r′.rel)) (≈-sym r.T≈)
    where module r  = GluU t∼a
          module r′ = GluU t′∼a
®El⇒≈ {_} {_} {_} {t} {T} {_} {t′} (□ A≈B) t∼a t′∼a
  with presup-tm (Glubox.t∶T t∼a)
...  | ⊢Γ , _ = ≈-conv (begin
                  t                        ≈˘⟨ [I] ⊢t ⟩
                  t [ I ]                  ≈⟨ □-η (t[I] ⊢t) ⟩
                  box (unbox 1 (t [ I ]))  ≈⟨ box-cong (≈-conv (®El⇒≈ (A≈B (ins vone 1))
                                                                      k.rel
                                                                      (subst (_ ⊢ _ ∶ _ ®[ _ ]_∈El _)
                                                                             (unbox-det k′.↘ua k.↘ua)
                                                                             (®El-resp-T≈ (A≈B (ins vone 1)) k′.rel (≈-sym GT≈GT′[I；1]))))
                                                               ([I；1] ⊢GT)) ⟩
                  box (unbox 1 (t′ [ I ])) ≈˘⟨ □-η (t[I] ⊢t′) ⟩
                  t′ [ I ]                 ≈⟨ [I] ⊢t′ ⟩
                  t′                       ∎)
                       (≈-sym r.T≈)
  where module r  = Glubox t∼a
        module r′ = Glubox t′∼a
        module k  = □Krip (r.krip L.[ [] ] (⊢rI ⊢Γ))
        module k′ = □Krip (r′.krip L.[ [] ] (⊢rI ⊢Γ))
        open ER
        ⊢GT          = ®□⇒wf A≈B (®El⇒® (□ A≈B) t∼a)
        ⊢GT′         = ®□⇒wf A≈B (®El⇒® (□ A≈B) t′∼a)
        GT≈GT′[I；1] = ®⇒≈ (A≈B (ins vone 1)) (®El⇒® (A≈B (ins vone 1)) k.rel) (®El⇒® (A≈B (ins vone 1)) k′.rel)
        GT≈GT′       = ≈-trans (≈-sym ([I；1] ⊢GT)) (≈-trans GT≈GT′[I；1] ([I；1] ⊢GT′))
        ⊢t           = conv r.t∶T r.T≈
        ⊢t′          = conv r′.t∶T (≈-trans r′.T≈ (□-cong (≈-sym GT≈GT′)))
®El⇒≈ {_} {_} {_} {t} {T} {_} {t′} (Π iA RT) t∼a t′∼a
  with presup-tm (GluΛ.t∶T t∼a)
...  | ⊢Γ , _  = ≈-conv (begin
                   t                   ≈⟨ Λ-η ⊢t ⟩
                   Λ (t [ wk ] $ v 0)  ≈⟨ Λ-cong (≈-conv (®El⇒≈ T≈T′ k.®fa
                                                                (subst (_ ⊢ _ ∶ _ ®[ _ ]_∈El T≈T′)
                                                                       (ap-det k′.↘fa k.↘fa)
                                                                       (®El-resp-T≈ T≈T′ k′.®fa (≈-sym OT≈OT′[wkv0]))))
                                                         ([wk,v0] r.⊢OT)) ⟩
                   Λ (t′ [ wk ] $ v 0) ≈˘⟨ Λ-η ⊢t′ ⟩
                   t′                  ∎) (≈-sym r.T≈)
  where module r     = GluΛ t∼a
        module r′    = GluΛ t′∼a
        open ER
        ⊢IT          = ®Π-wf iA RT (®El⇒® (Π iA RT) t∼a)
        ⊢IT′         = ®Π-wf iA RT (®El⇒® (Π iA RT) t′∼a)
        IT-rel       = ®-resp-≈ (iA vone) (ΛRel.IT-rel (r.krip (⊢rI ⊢Γ))) ([I] ⊢IT)
        IT-rel′      = ®-resp-≈ (iA vone) (ΛRel.IT-rel (r′.krip (⊢rI ⊢Γ))) ([I] ⊢IT′)
        IT≈IT′       = ®⇒≈ (iA vone) IT-rel IT-rel′
        ⊢OT′         = ctxeq-tm (∺-cong (⊢≈-refl ⊢Γ) (≈-sym IT≈IT′)) r′.⊢OT
        v∼l          = v0®x (iA vone) IT-rel
        l∈           = ®El⇒∈El (iA vone) v∼l
        open ΛRel (r.krip (⊢rwk (⊢∺ ⊢Γ ⊢IT))) using (ap-rel)
        open ΛRel (r′.krip (⊢rwk (⊢∺ ⊢Γ ⊢IT))) using () renaming (ap-rel to ap-rel′)
        module k     = ΛKripke (ap-rel v∼l l∈)
        module k′    = ΛKripke (ap-rel′ (®El-resp-T≈ (iA vone) v∼l ([]-cong-Se′ IT≈IT′ (s-wk (⊢∺ ⊢Γ ⊢IT)))) l∈)
        open ΠRT (RT vone l∈) using (T≈T′)
        OT≈OT′[wkv0] = ®⇒≈ T≈T′ (®El⇒® T≈T′ k.®fa) (®El⇒® T≈T′ k′.®fa)
        OT≈OT′       = ≈-trans (≈-sym ([wk,v0] r.⊢OT)) (≈-trans OT≈OT′[wkv0] ([wk,v0] ⊢OT′))
        ⊢t           = conv r.t∶T r.T≈
        ⊢t′          = conv r′.t∶T (≈-trans r′.T≈ (≈-sym (Π-cong IT≈IT′ OT≈OT′)))


®El⇒≈-gen : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
            Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
            Γ ⊢ t′ ∶ T′ ®[ i ] a ∈El A≈B →
            ----------------------------
            Γ ⊢ t ≈ t′ ∶ T
®El⇒≈-gen A≈B t∼a t′∼a = ®El⇒≈ A≈B t∼a (®El-resp-T≈ A≈B t′∼a (®⇒≈ A≈B (®El⇒® A≈B t′∼a) (®El⇒® A≈B t∼a)))


mutual

  ®-cumu-step : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
                Γ ⊢ T ®[ i ] A≈B →
                -----------------------------
                Γ ⊢ T ®[ suc i ] 𝕌-cumu-step i A≈B
  ®-cumu-step (ne C≈C′) (⊢T , rel) = cumu ⊢T , λ ⊢σ → ≈-cumu (rel ⊢σ)
  ®-cumu-step N T∼A                = ≈-cumu T∼A
  ®-cumu-step (U′ j<i) T∼A         = ≈-cumu T∼A
  ®-cumu-step (□ A≈B) T∼A          = record
    { GT   = GT
    ; T≈   = ≈-cumu T≈
    ; krip = λ {_} {σ} Ψs ⊢σ → ®-cumu-step (A≈B (ins (mt σ) (len Ψs))) (krip Ψs ⊢σ)
    }
    where open Glu□ T∼A
  ®-cumu-step (Π iA RT) T∼A        = record
    { IT   = IT
    ; OT   = OT
    ; ⊢OT  = cumu ⊢OT
    ; T≈   = ≈-cumu T≈
    ; krip = λ {_} {σ} ⊢σ →
      let open ΠRel (krip ⊢σ)
      in record
      { IT-rel = ®-cumu-step (iA (mt σ)) IT-rel
      ; OT-rel = λ s∼a a∈ → ®-cumu-step (ΠRT.T≈T′ (RT (mt σ) (El-lower _ (iA (mt σ)) a∈))) (OT-rel (®El-lower (iA (mt σ)) IT-rel s∼a) (El-lower _ (iA (mt σ)) a∈))
      }
    }
    where open GluΠ T∼A


  ®El-cumu-step : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
                  Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
                  ------------------------------------------
                  Γ ⊢ t ∶ T ®[ suc i ] a ∈El 𝕌-cumu-step i A≈B
  ®El-cumu-step (ne C≈C′) (ne c∈ , rel)    = ne c∈ , record
    { t∶T  = t∶T
    ; ⊢T   = cumu ⊢T
    ; krip = λ ⊢σ → let Tσ≈ , tσ≈ = krip ⊢σ in ≈-cumu Tσ≈ , tσ≈
    }
    where open GluNe rel
  ®El-cumu-step N (t∼a , T≈N)              = t∼a , ≈-cumu T≈N
  ®El-cumu-step (U′ j<i) t∼a
    rewrite Glu-wellfounded-≡ j<i
          | Glu-wellfounded-≡ (≤-step j<i) = record
    { t∶T = t∶T
    ; T≈  = ≈-cumu T≈
    ; A∈𝕌 = A∈𝕌
    ; rel = rel
    }
    where open GluU t∼a
  ®El-cumu-step (□ A≈B) t∼a                = record
    { GT   = GT
    ; t∶T  = t∶T
    ; a∈El = El-cumu-step _ (□ A≈B) a∈El
    ; T≈   = ≈-cumu T≈
    ; krip = λ {_} {σ} Ψs ⊢σ →
      let open □Krip (krip Ψs ⊢σ)
      in record
      { ua  = ua
      ; ↘ua = ↘ua
      ; rel = ®El-cumu-step (A≈B (ins (mt σ) (len Ψs))) rel
      }
    }
    where open Glubox t∼a
  ®El-cumu-step (Π iA RT) t∼a              = record
    { t∶T  = t∶T
    ; a∈El = El-cumu-step _ (Π iA RT) a∈El
    ; IT   = IT
    ; OT   = OT
    ; ⊢OT  = cumu ⊢OT
    ; T≈   = ≈-cumu T≈
    ; krip = λ {_} {σ} ⊢σ →
      let open ΛRel (krip ⊢σ)
      in record
      { IT-rel = ®-cumu-step (iA (mt σ)) IT-rel
      ; ap-rel = λ s∼b b∈ →
        let open ΛKripke (ap-rel (®El-lower (iA (mt σ)) IT-rel s∼b) (El-lower _ (iA (mt σ)) b∈))
        in record
        { fa  = fa
        ; ↘fa = ↘fa
        ; ®fa = ®El-cumu-step (ΠRT.T≈T′ (RT (mt σ) (El-lower _ (iA (mt σ)) b∈))) ®fa
        }
      }
    }
    where open GluΛ t∼a


  -- this is tricky! we need to pass on the knowledge that T is related to A in a lower level such that
  -- ®El can be lowered! it cannot be done without this extra piece of knowledge.
  ®El-lower : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
              Γ ⊢ T ®[ i ] A≈B →
              Γ ⊢ t ∶ T ®[ suc i ] a ∈El 𝕌-cumu-step i A≈B →
              -----------------------------------------
              Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B
  ®El-lower (ne C≈C′) (⊢T , rel) (ne c∈⊥ , rel′) = ne c∈⊥ , record
    { t∶T  = t∶T
    ; ⊢T   = ⊢T
    ; krip = λ ⊢σ → rel ⊢σ , proj₂ (krip ⊢σ)
    }
    where open GluNe rel′ hiding (⊢T)
  ®El-lower N T∼A (t∼a , _)                      = t∼a , T∼A
  ®El-lower (U′ j<i) T∼A t∼a
    rewrite Glu-wellfounded-≡ j<i
          | Glu-wellfounded-≡ (≤-step j<i)       = record
    { t∶T = t∶T
    ; T≈  = T∼A
    ; A∈𝕌 = A∈𝕌
    ; rel = rel
    }
    where open GluU t∼a
  ®El-lower (□ A≈B) T∼A t∼a                      = record
    { GT   = T.GT
    ; t∶T  = t∶T
    ; a∈El = El-lower _ (□ A≈B) a∈El
    ; T≈   = T.T≈
    ; krip = λ {_} {σ} Ψs ⊢σ →
      let open □Krip (krip Ψs ⊢σ)
          A≈Bcu = A≈B (ins (mt σ) (len Ψs))
      in record
      { ua  = ua
      ; ↘ua = ↘ua
      ; rel = ®El-lower (A≈B (ins (mt σ) (len Ψs)))
                        (T.krip Ψs ⊢σ)
                        (®El-resp-T≈ (𝕌-cumu-step _ (A≈B (ins (mt σ) (len Ψs))))
                                     rel
                                     (≈-sym (®⇒≈ (𝕌-cumu-step _ A≈Bcu) (®-cumu-step A≈Bcu (T.krip Ψs ⊢σ)) (®El⇒® (𝕌-cumu-step _ A≈Bcu) rel))))
      }
    }
    where module T = Glu□ T∼A
          open Glubox t∼a
  ®El-lower (Π iA RT) T∼A t∼a                    = record
    { t∶T  = t∶T
    ; a∈El = El-lower _ (Π iA RT) a∈El
    ; IT   = T.IT
    ; OT   = T.OT
    ; ⊢OT  = T.⊢OT
    ; T≈   = T.T≈
    ; krip = λ {_} {σ} ⊢σ →
      let open ΛRel (krip ⊢σ)
          module Π = ΠRel (T.krip ⊢σ)
          iAcu = 𝕌-cumu-step _ (iA (mt σ))
      in record
      { IT-rel = Π.IT-rel
      ; ap-rel = λ s∼b b∈ →
        let open ΛKripke (ap-rel (®El-resp-T≈ iAcu
                                              (®El-cumu-step (iA (mt σ)) s∼b)
                                              (®⇒≈ iAcu (®-cumu-step (iA (mt σ)) Π.IT-rel) IT-rel))
                                 (El-cumu-step _ (iA (mt σ)) b∈))
            RT₁      = RT (mt σ) b∈
            RT₂      = RT (mt σ) (El-lower _ (iA (mt σ)) (El-cumu-step _ (iA (mt σ)) b∈))
            T≈T′     = ΠRT.T≈T′ RT₁
            T≈T′cumu = 𝕌-cumu-step _ T≈T′
            ®fa′     = ®El-≡ (𝕌-cumu-step _ (ΠRT.T≈T′ RT₂))
                             T≈T′cumu
                             ®fa
                             (⟦⟧-det (ΠRT.↘⟦T⟧ RT₂) (ΠRT.↘⟦T⟧ RT₁))
        in record
        { fa  = fa
        ; ↘fa = ↘fa
        ; ®fa = ®El-lower T≈T′ (Π.OT-rel s∼b b∈)
                          (®El-resp-T≈ T≈T′cumu ®fa′
                                       (®⇒≈ T≈T′cumu (®El⇒® T≈T′cumu ®fa′) (®-cumu-step T≈T′ (Π.OT-rel s∼b b∈))))
        }
      }
    }
    where module T = GluΠ T∼A
          open GluΛ t∼a

®-cumu-steps : ∀ {i} j
               (A≈B : A ≈ B ∈ 𝕌 i) →
               Γ ⊢ T ®[ i ] A≈B →
               -----------------------------
               Γ ⊢ T ®[ j + i ] 𝕌-cumu-steps i j A≈B
®-cumu-steps zero A≈B T∼A    = T∼A
®-cumu-steps (suc j) A≈B T∼A = ®-cumu-step (𝕌-cumu-steps _ j A≈B) (®-cumu-steps j A≈B T∼A)


®El-cumu-steps : ∀ {i} j
                 (A≈B : A ≈ B ∈ 𝕌 i) →
                 Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
                 ------------------------------------------
                 Γ ⊢ t ∶ T ®[ j + i ] a ∈El 𝕌-cumu-steps i j A≈B
®El-cumu-steps zero A≈B t∼a    = t∼a
®El-cumu-steps (suc j) A≈B t∼a = ®El-cumu-step (𝕌-cumu-steps _ j A≈B) (®El-cumu-steps j A≈B t∼a)


®-cumu : ∀ {i j}
         (A≈B : A ≈ B ∈ 𝕌 i) →
         Γ ⊢ T ®[ i ] A≈B →
         (i≤j : i ≤ j) →
         -----------------------------
         Γ ⊢ T ®[ j ] 𝕌-cumu i≤j A≈B
®-cumu {i = i} A≈B T∼A i≤j
  with ®-cumu-steps (≤-diff i≤j) A≈B T∼A
...  | rel = helper (𝕌-cumu-steps i (≤-diff i≤j) A≈B) (𝕌-cumu i≤j A≈B) rel (trans (ℕₚ.+-comm (≤-diff i≤j) i) (≤-diff-+ i≤j))
  where helper : ∀ {i j} (A≈B : A ≈ B ∈ 𝕌 i) (A≈B′ : A ≈ B ∈ 𝕌 j) → Γ ⊢ T ®[ i ] A≈B → i ≡ j → Γ ⊢ T ®[ j ] A≈B′
        helper A≈B A≈B′ T∼A refl = ®-one-sided A≈B A≈B′ T∼A

®El-cumu : ∀ {i j}
           (A≈B : A ≈ B ∈ 𝕌 i) →
           Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
           (i≤j : i ≤ j) →
           -----------------------------
           Γ ⊢ t ∶ T ®[ j ] a ∈El 𝕌-cumu i≤j A≈B
®El-cumu {i = i} A≈B t∼a i≤j
  with ®El-cumu-steps (≤-diff i≤j) A≈B t∼a
...  | rel = helper (𝕌-cumu-steps i (≤-diff i≤j) A≈B) (𝕌-cumu i≤j A≈B) rel (trans (ℕₚ.+-comm (≤-diff i≤j) i) (≤-diff-+ i≤j))
  where helper : ∀ {i j} (A≈B : A ≈ B ∈ 𝕌 i) (A≈B′ : A ≈ B ∈ 𝕌 j) → Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B → i ≡ j → Γ ⊢ t ∶ T ®[ j ] a ∈El A≈B′
        helper A≈B A≈B′ t∼a refl = ®El-one-sided A≈B A≈B′ t∼a
