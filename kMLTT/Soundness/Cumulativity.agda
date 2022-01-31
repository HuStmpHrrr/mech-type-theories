{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

-- prove that the gluing model is cumulative
module kMLTT.Soundness.Cumulativity (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib

open import kMLTT.Statics.Properties
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
