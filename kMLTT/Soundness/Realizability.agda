{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Soundness.Realizability (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Data.List.Properties as Lₚ
open import Data.Nat.Properties as ℕₚ

open import kMLTT.Statics.Properties
open import kMLTT.Semantics.Readback
open import kMLTT.Semantics.Properties.Domain fext
open import kMLTT.Semantics.Properties.PER fext
open import kMLTT.Soundness.LogRel
open import kMLTT.Soundness.Properties.LogRel fext
open import kMLTT.Soundness.Properties.Mt fext


var-arith : ∀ Ψ″ (T : Typ) Ψ′ → len (Ψ″ ++ T ∷ Ψ′) ∸ len Ψ′ ∸ 1 ≡ len Ψ″
var-arith Ψ″ T Ψ′ = begin
  len (Ψ″ ++ T ∷ Ψ′) ∸ len Ψ′ ∸ 1
    ≡⟨ cong (λ n → n ∸ len Ψ′ ∸ 1) (Lₚ.length-++ Ψ″) ⟩
  len Ψ″ + suc (len Ψ′) ∸ len Ψ′ ∸ 1
    ≡⟨ cong (_∸ 1) (ℕₚ.+-∸-assoc (len Ψ″) {suc (len Ψ′)} (ℕₚ.≤-step ℕₚ.≤-refl)) ⟩
  len Ψ″ + (suc (len Ψ′) ∸ len Ψ′) ∸ 1
    ≡⟨ cong (λ n → len Ψ″ + n ∸ 1) (ℕₚ.m+n∸n≡m 1 (len Ψ′)) ⟩
  len Ψ″ + 1 ∸ 1
    ≡⟨ ℕₚ.m+n∸n≡m (len Ψ″) 1 ⟩
  len Ψ″
    ∎
  where open ≡-Reasoning


v0∼x-gen : ∀ Ψ → Δ ⊢r σ ∶ Γ → head Γ ≡ Ψ ++ T ∷ Ψ′ → Δ ⊢ v (len Ψ) [ σ ] ≈ v (len (head Δ) ∸ len Ψ′ ∸ 1) ∶ T [wk]* (1 + len Ψ) [ σ ]
v0∼x-gen {Δ} {σ} {.Δ} {T} {Ψ′} Ψ (r-I σ≈) refl
  with presup-s-≈ σ≈
...  | _ , _ , _ , ⊢Γ = ≈-trans ([]-cong (v-≈ ⊢Γ n∈) σ≈)
                        (≈-trans ([I] (conv (vlookup ⊢Γ n∈) (≈-sym (≈-trans ([]-cong-Se″ ⊢T[wk]* σ≈) ([I] ⊢T[wk]*)))))
                                 helper)
  where n∈      = n∶T[wk]n∈!ΨTΓ ⊢Γ refl
        ⊢T[wk]* = proj₂ (proj₂ (presup-tm (⊢vn∶T[wk]suc[n] ⊢Γ refl)))
        [wkσ]≈  = []-cong-Se″ ⊢T[wk]* (s-≈-sym σ≈)
        helper : (Ψ ++ T ∷ Ψ′) ∷ tail Δ ⊢ v (len Ψ) ≈ v (len (Ψ ++ T ∷ Ψ′) ∸ len Ψ′ ∸ 1) ∶ T [wk]* (1 + len Ψ) [ σ ]
        helper
          rewrite var-arith Ψ T Ψ′ = ≈-conv (v-≈ ⊢Γ n∈) (≈-trans (≈-sym ([I] ⊢T[wk]*)) [wkσ]≈)
v0∼x-gen {Δ} {σ} {_} {_} {Ψ′} Ψ (r-p {_} {τ} {T′} ⊢τ σ≈) refl
  with presup-s (⊢r⇒⊢s ⊢τ)
...  | _ , ⊢∷ ⊢Γ ⊢T′  = begin
  v (len Ψ) [ σ ]               ≈⟨ []-cong (v-≈ ⊢Γ n∈) σ≈ ⟩
  v (len Ψ) [ p τ ]             ≈⟨ ≈-conv ([∘] ⊢τ′ (s-wk ⊢TΓ) (vlookup ⊢Γ n∈)) [wkτ]≈ ⟩
  v (len Ψ) [ wk ] [ τ ]        ≈⟨ ≈-conv ([]-cong ([wk] ⊢TΓ n∈) (s-≈-refl ⊢τ′)) wkτ≈ ⟩
  v (1 + len Ψ) [ τ ]           ≈⟨ ≈-conv (v0∼x-gen (T′ ∷ Ψ) ⊢τ refl) wkτ≈ ⟩
  v (len (head Δ) ∸ len Ψ′ ∸ 1) ∎
  where open ER
        n∈      = n∶T[wk]n∈!ΨTΓ ⊢Γ refl
        ⊢TΓ     = ⊢∷ ⊢Γ ⊢T′
        ⊢τ′     = ⊢r⇒⊢s ⊢τ
        ⊢T[wk]* = proj₂ (proj₂ (presup-tm (⊢vn∶T[wk]suc[n] ⊢Γ refl)))
        [wkτ]≈  = []-cong-Se″ ⊢T[wk]* (s-≈-sym σ≈)
        wkτ≈    = ≈-trans ([∘]-Se ⊢T[wk]* (s-wk ⊢TΓ) ⊢τ′) [wkτ]≈
v0∼x-gen [] (r-； _ _ _ _) ()
v0∼x-gen (_ ∷ _) (r-； _ _ _ _) ()

v0∼x : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
       Γ ⊢ T ®[ i ] A≈B →
       T ∺ Γ ⊢ v 0 ∶ T [ wk ] ®↓[ i ] l (len (head Γ)) ∈El A≈B
v0∼x {_} {_} {Γ} A≈B T∼A
  with ®⇒ty A≈B T∼A
...  | _ , ⊢T
     with presup-tm ⊢T
...     | ⊢Γ , _ = record
  { t∶T  = vlookup ⊢TΓ here
  ; T∼A  = ®-≡ (𝕌-mon vone A≈B) A≈B (®-mon A≈B (𝕌-mon vone A≈B) T∼A (r-p (⊢rI ⊢TΓ) (s-≈-sym (∘-I (s-wk ⊢TΓ))))) (D-ap-vone _)
  ; c∈⊥  = Bot-l (len (head Γ))
  ; krip = λ {Δ} {σ} ⊢σ → v0∼x-gen [] ⊢σ refl
  }
  where ⊢TΓ = ⊢∷ ⊢Γ ⊢T


private
  module Real i (rec : ∀ j → j < i → ∀ {A B Γ T Δ σ} (A≈B : A ≈ B ∈ 𝕌 j) → Γ ⊢ T ®[ j ] A≈B → Δ ⊢r σ ∶ Γ → ∃ λ W → Rty map len Δ - A [ mt σ ] ↘ W × Δ ⊢ T [ σ ] ≈ Nf⇒Exp W) where
    mutual

      ®↓El⇒®El : (A≈B : A ≈ B ∈ 𝕌 i) → Γ ⊢ t ∶ T ®↓[ i ] c ∈El A≈B → Γ ⊢ t ∶ T ®[ i ] ↑ A c ∈El A≈B
      ®↓El⇒®El (ne C≈C′) t∼c  = ne c∈⊥ , t∶T , λ ⊢σ → proj₂ T∼A ⊢σ , krip ⊢σ
        where open _⊢_∶_®↓[_]_∈El_ t∼c
      ®↓El⇒®El N t∼c          = ne c∈⊥ (λ ⊢σ → ≈-conv (krip ⊢σ) (≈-trans ([]-cong-Se′ (proj₂ T∼A) (⊢r⇒⊢s ⊢σ)) (N-[] _ (⊢r⇒⊢s ⊢σ)))) , T∼A
        where open _⊢_∶_®↓[_]_∈El_ t∼c
      ®↓El⇒®El (U j<i eq) t∼c = record
        { t∶T = t∶T
        ; T≈  = T∼A
        ; A∈𝕌 = ne c∈⊥
        ; rel = subst (λ f → f _ _ _)
                      (sym (Glu-wellfounded-≡ j<i))
                      ((-, conv t∶T (proj₂ T∼A))
                      , λ ⊢σ → -, ≈-conv (krip ⊢σ) (≈-trans (lift-⊢≈-Se-max ([]-cong-Se′ (proj₂ T∼A) (⊢r⇒⊢s ⊢σ))) (lift-⊢≈-Se-max′ (Se-[] _ (⊢r⇒⊢s ⊢σ)))))
        }
        where open _⊢_∶_®↓[_]_∈El_ t∼c
      ®↓El⇒®El {□ A} {_} {Γ} {t} {_} {c} (□ A≈B) t∼c       = record
        { GT   = GT
        ; t∶T  = t∶T
        ; a∈El = {!!} -- realizability of PER
        ; T≈   = T≈
        ; krip = λ {Δ} {σ} Ψs ⊢σ →
          let ⊢σ′   = ⊢r⇒⊢s ⊢σ
              ⊢GT   = proj₂ (®□⇒wf A≈B T∼A)
              Gk    = G.krip Ψs ⊢σ
              ⊢ΨsΔ  = proj₁ (presup-tm (proj₂ (®⇒ty _ Gk)))
              Aσ；≈ = A≈B (ins (mt σ) (len Ψs))
              ⊢t    = conv t∶T (proj₂ T≈)
              ⊢tσ   = conv (t[σ] ⊢t ⊢σ′) (□-[] ⊢σ′ ⊢GT)
          in record
          { ua  = unbox′ (A [ ins (mt σ) (len Ψs) ]) (len Ψs) (c [ mt σ ])
          ; ↘ua = subst (λ B → unbox∙ len Ψs , ↑ (□ (A [ ins (mt σ) 1 ])) (c [ mt σ ]) ↘ unbox′ B (len Ψs) (c [ mt σ ])) (D-ins-ins A (mt σ) (len Ψs)) (unbox∙ (len Ψs))
          ; rel = ®El-resp-T≈ Aσ；≈
                              (®↓El⇒®El Aσ；≈
                                        record
                                        { t∶T  = □-E Ψs ⊢tσ ⊢ΨsΔ refl
                                        ; T∼A  = ®-resp-≈ Aσ；≈ Gk (-, []-∘-；′ Ψs ⊢ΨsΔ ⊢GT ⊢σ′)
                                        ; c∈⊥  = unbox-Bot (len Ψs) (Bot-mon (mt σ) c∈⊥)
                                        ; krip = helper Ψs ⊢t ⊢σ
                                        })
                              (-, ≈-sym ([]-∘-；′ Ψs ⊢ΨsΔ ⊢GT ⊢σ′))
          }
        }
        where module ↓ = _⊢_∶_®↓[_]_∈El_ t∼c
              open ↓
              module G = Glu□ T∼A
              open G
              helper : ∀ Ψs →
                       Γ ⊢ t ∶ □ GT →
                       Δ ⊢r σ ∶ Γ →
                       Δ′ ⊢r τ ∶ Ψs ++⁺ Δ →
                       Δ′ ⊢ (unbox (len Ψs) (t [ σ ])) [ τ ] ≈ unbox (O (mt τ) (len Ψs)) (Ne⇒Exp (proj₁ (c∈⊥ (map len Δ′ ∥ (O (mt τ) (len Ψs))) (mt σ ø mt τ ∥ len Ψs)))) ∶ GT [ σ ； 1 ] [ I ； len Ψs ] [ τ ]
              helper {_} {σ} {_} {τ} Ψs ⊢t ⊢σ ⊢τ
                with ⊢r-∥′ Ψs ⊢τ
              ...  | Ψs′ , Δ″ , refl , eql , ⊢τ∥
                   with ↓.krip (⊢r-∘ ⊢σ ⊢τ∥)
              ...     | equiv
                      rewrite sym (O-resp-mt τ (len Ψs))
                            | sym eql = {!!}
      ®↓El⇒®El {Π A S ρ} {_} {Γ} {t} {T} {c} (Π iA RT) t∼c = record
        { t∶T  = t∶T
        ; a∈El = {!!} -- realizability
        ; IT   = IT
        ; OT   = OT
        ; ⊢OT  = ⊢OT
        ; T≈   = T≈
        ; krip = λ {Δ} {σ} ⊢σ → record
          { IT-rel = ΠRel.IT-rel (G.krip ⊢σ)
          ; ap-rel = λ s∼b b∈ →
            let a , ↘a , ∼a = ap-rel ⊢σ s∼b b∈
            in record
            { fa  = a
            ; ↘fa = ↘a
            ; ®fa = ∼a
            }
          }
        }
        where module ↓ = _⊢_∶_®↓[_]_∈El_ t∼c
              open ↓
              module G = GluΠ T∼A
              open G
              ap-rel : Δ ⊢r σ ∶ Γ →
                       Δ ⊢ s ∶ IT [ σ ] ®[ i ] b ∈El (iA (mt σ)) →
                       (b∈ : b ∈′ El i (iA (mt σ))) →
                       ∃ λ a → ↑ (Π A S ρ [ mt σ ]) (c [ mt σ ]) ∙ b ↘ a × Δ ⊢ t [ σ ] $ s ∶ OT [ σ , s ] ®[ i ] a ∈El (ΠRT.T≈T′ (RT (mt σ) b∈))
              ap-rel {_} {σ} {s} {b} ⊢σ s∼b b∈ = [ ΠRT.⟦T⟧ (RT (mt σ) b∈) ] c [ mt σ ] $′ ↓ (A [ mt σ ]) b
                                               , $∙ (A [ mt σ ]) (c [ mt σ ]) (ΠRT.↘⟦T⟧ (RT (mt σ) b∈))
                                               , ®↓El⇒®El (ΠRT.T≈T′ (RT (mt σ) b∈)) record
                                                 { t∶T  = conv (Λ-E ⊢tσ ⊢s) (≈-sym ([]-q-∘-,′ (proj₂ ⊢OT) ⊢σ′ ⊢s))
                                                 ; T∼A  = ΠRel.OT-rel (G.krip ⊢σ) s∼b b∈
                                                 ; c∈⊥  = $-Bot (Bot-mon (mt σ) c∈⊥) (Top-trans ↑.a∈⊤ (Top-sym ↑.a∈⊤))
                                                 ; krip = λ {_} {τ} ⊢τ →
                                                   let ⊢τ′ = ⊢r⇒⊢s ⊢τ
                                                       ⊢στ = s-∘ ⊢τ′ ⊢σ′
                                                       eq  = begin
                                                         OT [ (σ ∘ τ) , s [ τ ] ] ≈˘⟨ []-cong-Se″ (proj₂ ⊢OT) (,-∘ ⊢σ′ ⊢IT ⊢s ⊢τ′) ⟩
                                                         OT [ σ , s ∘ τ ]         ≈˘⟨ [∘]-Se (proj₂ ⊢OT) (s-, ⊢σ′ ⊢IT ⊢s) ⊢τ′ ⟩
                                                         OT [ σ , s ] [ τ ]       ∎
                                                   in begin
                                                   (t [ σ ] $ s) [ τ ]     ≈⟨ ≈-conv ($-[] ⊢τ′ ⊢tσ ⊢s) (≈-trans (≈-sym ([]-q-∘-, (proj₂ ⊢OT) ⊢σ′ ⊢τ′ (t[σ] ⊢s ⊢τ′)))
                                                                                                                eq) ⟩
                                                   t [ σ ] [ τ ] $ s [ τ ] ≈⟨ ≈-conv ($-cong (≈-conv (≈-trans (≈-sym ([∘] ⊢τ′ ⊢σ′ t∶T)) (↓.krip (⊢r-∘ ⊢σ ⊢τ)))
                                                                                                     (≈-trans (lift-⊢≈-Se-max (proj₂ (helper ⊢στ)))
                                                                                                              (lift-⊢≈-Se-max′ {j = proj₁ (helper (s-∘ ⊢τ′ ⊢σ′))}
                                                                                                                               (Π-cong (≈-sym ([∘]-Se (lift-⊢-Se-max ⊢IT) ⊢σ′ ⊢τ′))
                                                                                                                                       (≈-refl (lift-⊢-Se-max′ (t[σ]-Se (proj₂ ⊢OT) (⊢q ⊢στ ⊢IT))))))))
                                                                                             (↑.krip ⊢τ))
                                                                                     (≈-trans (≈-sym ([]-q-∘-,′ (proj₂ ⊢OT) ⊢στ (conv (t[σ] ⊢s ⊢τ′) ([∘]-Se ⊢IT ⊢σ′ ⊢τ′))))
                                                                                              eq) ⟩
                                                   _ $ _                   ∎
                                                 }
                where ⊢σ′ = ⊢r⇒⊢s ⊢σ
                      ⊢IT = proj₂ (®Π-wf iA RT T∼A)
                      ⊢s  = ®El⇒tm (iA (mt σ)) s∼b
                      helper : ∀ {Δ σ} → Δ ⊢s σ ∶ Γ → Δ ⊢ T [ σ ] ≈ Π (IT [ σ ]) (OT [ q σ ])
                      helper ⊢σ = -, ≈-trans (lift-⊢≈-Se-max ([]-cong-Se′ (proj₂ T≈) ⊢σ)) (lift-⊢≈-Se-max′ {j = proj₁ T≈} (Π-[] ⊢σ (lift-⊢-Se-max ⊢IT) (lift-⊢-Se-max′ (proj₂ ⊢OT))))
                      ⊢tσ = conv (t[σ] t∶T ⊢σ′) (proj₂ (helper ⊢σ′))
                      open ER
                      module ↑ = _⊢_∶_®↑[_]_∈El_ (®El⇒®↑El (iA (mt σ)) s∼b)

      ®El⇒®↑El : (A≈B : A ≈ B ∈ 𝕌 i) → Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B → Γ ⊢ t ∶ T ®↑[ i ] a ∈El A≈B
      ®El⇒®↑El (ne C≈C′) t∼a  = {!!}
      ®El⇒®↑El N (t∼a , _ , T≈N)
        with presup-≈ T≈N
      ...  | ⊢Γ , _ = record
        { t∶T  = conv (®Nat⇒∶Nat t∼a ⊢Γ) (≈-sym T≈N)
        ; T∼A  = -, T≈N
        ; a∈⊤  = ®Nat⇒∈Top t∼a
        ; krip = λ ⊢σ → ≈-conv (®Nat⇒≈ t∼a ⊢σ) (≈-sym (≈-trans ([]-cong-Se′ T≈N (⊢r⇒⊢s ⊢σ)) (N-[] _ (⊢r⇒⊢s ⊢σ))))
        }
      ®El⇒®↑El (U j<i eq) t∼a = {!!}
        where open GluU t∼a
      ®El⇒®↑El (□ A≈B) t∼a    = {!!}
      ®El⇒®↑El (Π iA RT) t∼a  = {!!}

      ®⇒Rty-eq : (A≈B : A ≈ B ∈ 𝕌 i) → Γ ⊢ T ®[ i ] A≈B → Δ ⊢r σ ∶ Γ → ∃ λ W → Rty map len Δ - A [ mt σ ] ↘ W × Δ ⊢ T [ σ ] ≈ Nf⇒Exp W
      ®⇒Rty-eq (ne C≈C′) T∼A ⊢σ  = {!!}
      ®⇒Rty-eq N T∼A ⊢σ          = {!!}
      ®⇒Rty-eq (U j<i eq) T∼A ⊢σ = {!!}
      ®⇒Rty-eq (□ A≈B) T∼A ⊢σ    = {!!}
      ®⇒Rty-eq (Π iA RT) T∼A ⊢σ  = {!!}
