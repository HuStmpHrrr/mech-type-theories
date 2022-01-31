{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

-- prove that the gluing model is cumulative
module kMLTT.Soundness.Cumulativity (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib

open import kMLTT.Statics.Properties
open import kMLTT.Semantics.Readback
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
     with ®El-resp-T≈ (iA (mt I)) (v0®x (iA (mt I)) (ΠRel.IT-rel (GluΠ.krip T∼A (⊢rI ⊢Γ)))) ([]-cong-Se′ ([I] ⊢IT) (s-wk (⊢∷ ⊢Γ (t[σ]-Se ⊢IT (s-I ⊢Γ)))))
...     | v∼l               = begin
  T                                    ≈⟨ T.T≈ ⟩
  Π T.IT T.OT                          ≈˘⟨ Π-cong ([I] ⊢IT) ([wk,v0] (ctxeq-tm (∷-cong (⊢≈-refl ⊢Γ) (≈-sym ([I] ⊢IT))) T.⊢OT)) ⟩
  Π (T.IT [ I ]) (T.OT [ wk , v 0 ])   ≈⟨ Π-cong ([]-cong-Se′ IT≈IT′ (s-I ⊢Γ))
                                                 (®⇒≈ (ΠRT.T≈T′ (RT (mt wk) l∈))
                                                      (ΠRel.OT-rel (T.krip (⊢rwk ⊢ITΓ)) v∼l l∈)
                                                      (ΠRel.OT-rel (T′.krip (⊢rwk ⊢ITΓ)) (®El-resp-T≈ (iA vone) v∼l ([]-cong-Se′ IT≈IT′ (s-wk ⊢ITΓ))) l∈)) ⟩
  Π (T′.IT [ I ]) (T′.OT [ wk , v 0 ]) ≈⟨ Π-cong ([I] (®Π-wf iA RT T′∼A)) ([wk,v0] (ctxeq-tm (∷-cong (⊢≈-refl ⊢Γ) (≈-sym ([I] ⊢IT′))) T′.⊢OT)) ⟩
  Π T′.IT T′.OT                        ≈˘⟨ T′.T≈ ⟩
  T′                                   ∎
  where module T  = GluΠ T∼A
        module T′ = GluΠ T′∼A
        open ER
        IT-rel = ΠRel.IT-rel (T.krip (⊢rI ⊢Γ))
        IT-rel′ = ΠRel.IT-rel (T′.krip (⊢rI ⊢Γ))
        IT≈IT′ = ≈-trans (≈-sym ([I] ⊢IT)) (≈-trans (®⇒≈ (iA (mt I)) IT-rel IT-rel′) ([I] (®Π-wf iA RT T′∼A)))
        l∈ = ®El⇒∈El (iA vone) v∼l
        ⊢ITΓ = ⊢∷ ⊢Γ (t[σ]-Se ⊢IT (s-I ⊢Γ))


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
        ⊢OT′         = ctxeq-tm (∷-cong (⊢≈-refl ⊢Γ) (≈-sym IT≈IT′)) r′.⊢OT
        v∼l          = v0®x (iA vone) IT-rel
        l∈           = ®El⇒∈El (iA vone) v∼l
        open ΛRel (r.krip (⊢rwk (⊢∷ ⊢Γ ⊢IT))) using (ap-rel)
        open ΛRel (r′.krip (⊢rwk (⊢∷ ⊢Γ ⊢IT))) using () renaming (ap-rel to ap-rel′)
        module k     = ΛKripke (ap-rel v∼l l∈)
        module k′    = ΛKripke (ap-rel′ (®El-resp-T≈ (iA vone) v∼l ([]-cong-Se′ IT≈IT′ (s-wk (⊢∷ ⊢Γ ⊢IT)))) l∈)
        open ΠRT (RT vone l∈) using (T≈T′)
        OT≈OT′[wkv0] = ®⇒≈ T≈T′ (®El⇒® T≈T′ k.®fa) (®El⇒® T≈T′ k′.®fa)
        OT≈OT′       = ≈-trans (≈-sym ([wk,v0] r.⊢OT)) (≈-trans OT≈OT′[wkv0] ([wk,v0] ⊢OT′))
        ⊢t           = conv r.t∶T r.T≈
        ⊢t′          = conv r′.t∶T (≈-trans r′.T≈ (≈-sym (Π-cong IT≈IT′ OT≈OT′)))
