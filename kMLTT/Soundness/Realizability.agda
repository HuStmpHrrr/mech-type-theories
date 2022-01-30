{-# OPTIONS --without-K --safe #-}

open import Axiom.Extensionality.Propositional

module kMLTT.Soundness.Realizability (fext : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′) where

open import Lib
open import Data.List.Properties as Lₚ
open import Data.Nat.Properties as ℕₚ

open import kMLTT.Statics.Properties
open import kMLTT.Semantics.Readback
open import kMLTT.Semantics.Realizability fext
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
...  | ⊢T
     with presup-tm ⊢T
...     | ⊢Γ , _ = record
  { t∶T  = vlookup ⊢TΓ here
  ; T∼A  = ®-≡ (𝕌-mon vone A≈B) A≈B (®-mon A≈B (𝕌-mon vone A≈B) T∼A (r-p (⊢rI ⊢TΓ) (s-≈-sym (∘-I (s-wk ⊢TΓ))))) (D-ap-vone _)
  ; c∈⊥  = Bot-l (len (head Γ))
  ; krip = λ {Δ} {σ} ⊢σ → v0∼x-gen [] ⊢σ refl
  }
  where ⊢TΓ = ⊢∷ ⊢Γ ⊢T


private
  module Real i (rec : ∀ {j} → j < i → ∀ {A B Γ T Δ σ} (A≈B : A ≈ B ∈ 𝕌 j) → Γ ⊢ T ®[ j ] A≈B → Δ ⊢r σ ∶ Γ → ∃ λ W → Rty map len Δ - A [ mt σ ] ↘ W × Δ ⊢ T [ σ ] ≈ Nf⇒Exp W ∶ Se j) where
    mutual

      ®↓El⇒®El : (A≈B : A ≈ B ∈ 𝕌 i) → Γ ⊢ t ∶ T ®↓[ i ] c ∈El A≈B → Γ ⊢ t ∶ T ®[ i ] ↑ A c ∈El A≈B
      ®↓El⇒®El R@(ne C≈C′) t∼c                             = ne c∈⊥ , record
        { t∶T  = t∶T
        ; ⊢T   = ®⇒ty R T∼A
        ; krip = λ ⊢σ → proj₂ T∼A ⊢σ , krip ⊢σ
        }
        where open _⊢_∶_®↓[_]_∈El_ t∼c
      ®↓El⇒®El N t∼c                                       = ne c∈⊥ (λ ⊢σ → ≈-conv (krip ⊢σ) (≈-trans ([]-cong-Se′ T∼A (⊢r⇒⊢s ⊢σ)) (N-[] _ (⊢r⇒⊢s ⊢σ)))) , T∼A
        where open _⊢_∶_®↓[_]_∈El_ t∼c
      ®↓El⇒®El (U j<i eq) t∼c                              = record
        { t∶T = t∶T
        ; T≈  = T∼A
        ; A∈𝕌 = ne c∈⊥
        ; rel = subst (λ f → f _ _ _)
                      (sym (Glu-wellfounded-≡ j<i))
                      (conv t∶T T∼A , λ ⊢σ → ≈-conv (krip ⊢σ) (≈-trans ([]-cong-Se′ T∼A (⊢r⇒⊢s ⊢σ)) (lift-⊢≈-Se (Se-[] _ (⊢r⇒⊢s ⊢σ)) j<i)))
        }
        where open _⊢_∶_®↓[_]_∈El_ t∼c
      ®↓El⇒®El {□ A} {_} {Γ} {t} {_} {c} (□ A≈B) t∼c       = record
        { GT   = GT
        ; t∶T  = t∶T
        ; a∈El = El-refl (□ A≈B) (realizability-Re (□ A≈B) c∈⊥)
        ; T≈   = T≈
        ; krip = λ {Δ} {σ} Ψs ⊢σ →
          let ⊢σ′   = ⊢r⇒⊢s ⊢σ
              Gk    = G.krip Ψs ⊢σ
              ⊢ΨsΔ  = proj₁ (presup-tm (®⇒ty _ Gk))
              Aσ；≈ = A≈B (ins (mt σ) (len Ψs))
              ⊢t    = conv t∶T T≈
              ⊢tσ   = conv (t[σ] ⊢t ⊢σ′) (□-[] ⊢σ′ ⊢GT)
          in record
          { ua  = unbox′ (A [ ins (mt σ) (len Ψs) ]) (len Ψs) (c [ mt σ ])
          ; ↘ua = subst (λ B → unbox∙ len Ψs , ↑ (□ (A [ ins (mt σ) 1 ])) (c [ mt σ ]) ↘ unbox′ B (len Ψs) (c [ mt σ ])) (D-ins-ins A (mt σ) (len Ψs)) (unbox∙ (len Ψs))
          ; rel = ®El-resp-T≈ Aσ；≈
                              (®↓El⇒®El Aσ；≈
                                        record
                                        { t∶T  = □-E Ψs ⊢tσ ⊢ΨsΔ refl
                                        ; T∼A  = ®-resp-≈ Aσ；≈ Gk ([]-∘-；′ Ψs ⊢ΨsΔ ⊢GT ⊢σ′)
                                        ; c∈⊥  = unbox-Bot (len Ψs) (Bot-mon (mt σ) c∈⊥)
                                        ; krip = helper Ψs ⊢t ⊢σ
                                        })
                              (≈-sym ([]-∘-；′ Ψs ⊢ΨsΔ ⊢GT ⊢σ′))
          }
        }
        where module ↓ = _⊢_∶_®↓[_]_∈El_ t∼c
              open ↓
              module G = Glu□ T∼A
              open G
              open ER
              ⊢GT = ®□⇒wf A≈B T∼A
              helper : ∀ Ψs →
                       Γ ⊢ t ∶ □ GT →
                       Δ ⊢r σ ∶ Γ →
                       Δ′ ⊢r τ ∶ Ψs ++⁺ Δ →
                       Δ′ ⊢ (unbox (len Ψs) (t [ σ ])) [ τ ] ≈ unbox (O (mt τ) (len Ψs)) (Ne⇒Exp (proj₁ (c∈⊥ (map len Δ′ ∥ (O (mt τ) (len Ψs))) (mt σ ø mt τ ∥ len Ψs)))) ∶ GT [ σ ； 1 ] [ I ； len Ψs ] [ τ ]
              helper {_} {σ} {_} {τ} Ψs ⊢t ⊢σ ⊢τ
                with ⊢r-∥′ Ψs ⊢τ | presup-s (⊢r⇒⊢s ⊢σ) | presup-s (⊢r⇒⊢s ⊢τ)
              ...  | Ψs′ , Δ″ , refl , eql , ⊢τ∥ | ⊢Δ , _ | ⊢Δ′ , ⊢ΨsΔ
                   with ↓.krip (⊢r-∘ ⊢σ ⊢τ∥)
              ...     | equiv
                      rewrite sym (O-resp-mt τ (len Ψs))
                            | sym eql
                            | map-++⁺-commute len Ψs′ Δ″
                            | drop+-++⁺ (len Ψs′) (L.map len Ψs′) (map len Δ″) (Lₚ.length-map len Ψs′)
                            | mt-∥ τ (len Ψs) = ≈-conv
                            (begin
                              unbox (len Ψs) (t [ σ ]) [ τ ]                                     ≈⟨ ≈-conv (unbox-[] Ψs ⊢tσ ⊢τ′ refl)
                                                                                                           (≈-trans (≈-sym (subst (λ n → _ ⊢ GT [ _ ； _ ] ≈ GT [ σ ； 1 ] [ _ ； n ] ∶ Se _) eql
                                                                                                                                  ([]-∘-； Ψs′ ⊢Δ′ ⊢GT ⊢σ′ ⊢τ∥′)))
                                                                                                                    ([]-∘-；′ Ψs′ ⊢Δ′ ⊢GT ⊢στ∥)) ⟩
                              unbox (O τ (len Ψs)) (t [ σ ] [ τ ∥ len Ψs ])                      ≈⟨ subst (λ n → _ ⊢ unbox n _ ≈ unbox _ _ ∶ GT [ _ ] [ _ ]) eql
                                                                                                          (unbox-cong Ψs′ (≈-conv (≈-sym ([∘] ⊢τ∥′ ⊢σ′ ⊢t)) (□-[] ⊢στ∥ ⊢GT)) ⊢Δ′ refl) ⟩
                              unbox (len Ψs′) (t [ σ ∘ τ ∥ len Ψs ])                             ≈⟨ unbox-cong Ψs′ (≈-conv equiv (≈-trans ([]-cong-Se′ T≈ ⊢στ∥) (□-[] ⊢στ∥ ⊢GT))) ⊢Δ′ refl ⟩
                              unbox (len Ψs′)
                                    (Ne⇒Exp (proj₁ (c∈⊥ (map len Δ″) (mt σ ø (mt τ ∥ len Ψs))))) ∎)
                            (begin
                              GT [ (σ ∘ τ ∥ len Ψs) ； 1 ] [ I ； len Ψs′ ] ≈˘⟨ []-∘-；′ Ψs′ ⊢Δ′ ⊢GT (s-∘ ⊢τ∥′ ⊢σ′) ⟩
                              GT [ (σ ∘ τ ∥ len Ψs) ； len Ψs′ ]            ≈⟨ subst (λ n → _ ⊢ GT [ _ ； n ] ≈ _ ∶ Se _) (sym eql) ([]-；-∘ Ψs ⊢GT ⊢σ′ ⊢τ′) ⟩
                              GT [ σ ； len Ψs ] [ τ ]                      ≈⟨ []-cong-Se′ ([]-∘-；′ Ψs ⊢ΨsΔ ⊢GT ⊢σ′) ⊢τ′ ⟩
                              GT [ σ ； 1 ] [ I ； len Ψs ] [ τ ]           ∎)
                where ⊢σ′  = ⊢r⇒⊢s ⊢σ
                      ⊢τ′  = ⊢r⇒⊢s ⊢τ
                      ⊢τ∥′ = ⊢r⇒⊢s ⊢τ∥
                      ⊢στ∥ = s-∘ ⊢τ∥′ ⊢σ′
                      ⊢tσ  = conv (t[σ] ⊢t ⊢σ′) (□-[] ⊢σ′ ⊢GT)
      ®↓El⇒®El {Π A S ρ} {_} {Γ} {t} {T} {c} (Π iA RT) t∼c = record
        { t∶T  = t∶T
        ; a∈El = El-refl (Π iA RT) (realizability-Re (Π iA RT) c∈⊥)
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
                                                 { t∶T  = conv (Λ-E ⊢tσ ⊢s) (≈-sym ([]-q-∘-,′ ⊢OT ⊢σ′ ⊢s))
                                                 ; T∼A  = ΠRel.OT-rel (G.krip ⊢σ) s∼b b∈
                                                 ; c∈⊥  = $-Bot (Bot-mon (mt σ) c∈⊥) (Top-trans ↑.a∈⊤ (Top-sym ↑.a∈⊤))
                                                 ; krip = λ {_} {τ} ⊢τ →
                                                   let ⊢τ′ = ⊢r⇒⊢s ⊢τ
                                                       ⊢στ = s-∘ ⊢τ′ ⊢σ′
                                                       eq  = begin
                                                         OT [ (σ ∘ τ) , s [ τ ] ] ≈˘⟨ []-cong-Se″ ⊢OT (,-∘ ⊢σ′ ⊢IT ⊢s ⊢τ′) ⟩
                                                         OT [ σ , s ∘ τ ]         ≈˘⟨ [∘]-Se ⊢OT (s-, ⊢σ′ ⊢IT ⊢s) ⊢τ′ ⟩
                                                         OT [ σ , s ] [ τ ]       ∎
                                                   in begin
                                                   (t [ σ ] $ s) [ τ ]     ≈⟨ ≈-conv ($-[] ⊢τ′ ⊢tσ ⊢s) (≈-trans (≈-sym ([]-q-∘-, ⊢OT ⊢σ′ ⊢τ′ (t[σ] ⊢s ⊢τ′)))
                                                                                                                eq) ⟩
                                                   t [ σ ] [ τ ] $ s [ τ ] ≈⟨ ≈-conv ($-cong (≈-conv (≈-trans (≈-sym ([∘] ⊢τ′ ⊢σ′ t∶T)) (↓.krip (⊢r-∘ ⊢σ ⊢τ)))
                                                                                                     (≈-trans (helper ⊢στ)
                                                                                                              (Π-cong (≈-sym ([∘]-Se ⊢IT ⊢σ′ ⊢τ′))
                                                                                                                      (≈-refl (t[σ]-Se ⊢OT (⊢q ⊢στ ⊢IT))))))
                                                                                             (↑.krip ⊢τ))
                                                                                     (≈-trans (≈-sym ([]-q-∘-,′ ⊢OT ⊢στ (conv (t[σ] ⊢s ⊢τ′) ([∘]-Se ⊢IT ⊢σ′ ⊢τ′))))
                                                                                              eq) ⟩
                                                   _ $ _                   ∎
                                                 }
                where ⊢σ′ = ⊢r⇒⊢s ⊢σ
                      ⊢IT = ®Π-wf iA RT T∼A
                      ⊢s  = ®El⇒tm (iA (mt σ)) s∼b
                      helper : ∀ {Δ σ} → Δ ⊢s σ ∶ Γ → Δ ⊢ T [ σ ] ≈ Π (IT [ σ ]) (OT [ q σ ]) ∶ Se i
                      helper ⊢σ = ≈-trans ([]-cong-Se′ T≈ ⊢σ) (Π-[] ⊢σ ⊢IT ⊢OT)
                      ⊢tσ = conv (t[σ] t∶T ⊢σ′) (helper ⊢σ′)
                      open ER
                      module ↑ = _⊢_∶_®↑[_]_∈El_ (®El⇒®↑El (iA (mt σ)) s∼b)


      ®El⇒®↑El : (A≈B : A ≈ B ∈ 𝕌 i) → Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B → Γ ⊢ t ∶ T ®↑[ i ] a ∈El A≈B
      ®El⇒®↑El (ne C≈C′) (ne c∈⊥ , glu)                = record
        { t∶T  = t∶T
        ; T∼A  = ⊢T , λ ⊢σ → proj₁ (krip ⊢σ)
        ; a∈⊤  = Bot⊆Top c∈⊥
        ; krip = λ ⊢σ → proj₂ (krip ⊢σ)
        }
        where open GluNe glu
      ®El⇒®↑El N (t∼a , T≈N)
        with presup-≈ T≈N
      ...  | ⊢Γ , _                                    = record
        { t∶T  = conv (®Nat⇒∶Nat t∼a ⊢Γ) (≈-sym T≈N)
        ; T∼A  = T≈N
        ; a∈⊤  = ®Nat⇒∈Top t∼a
        ; krip = λ ⊢σ → ≈-conv (®Nat⇒≈ t∼a ⊢σ) (≈-sym (≈-trans ([]-cong-Se′ T≈N (⊢r⇒⊢s ⊢σ)) (N-[] _ (⊢r⇒⊢s ⊢σ))))
        }
      ®El⇒®↑El (U′ j<i) t∼a                            = record
        { t∶T  = t∶T
        ; T∼A  = T≈
        ; a∈⊤  = realizability-Rty A∈𝕌
        ; krip = λ {Δ} {σ} ⊢σ →
          let W , ↘W , eq = rec j<i A∈𝕌 (subst (λ f → f _ _ _) (Glu-wellfounded-≡ j<i) rel) ⊢σ
          in ≈-conv (subst (_ ⊢ _ ≈_∶ Se _) (cong Nf⇒Exp (Rty-det ↘W (helper _ (proj₁ (proj₂ (realizability-Rty A∈𝕌 (map len Δ) (mt σ))))))) eq)
                    (≈-sym (≈-trans ([]-cong-Se′ T≈ (⊢r⇒⊢s ⊢σ)) (lift-⊢≈-Se (Se-[] _ (⊢r⇒⊢s ⊢σ)) j<i)))
        }
        where open GluU t∼a
              helper : ∀ {j} n → Rf n - ↓ (U j) A ↘ W → Rty n - A ↘ W
              helper n (RU .n ↘W) = ↘W
      ®El⇒®↑El {□ A} {_} {Γ} {t} {T} (□ A≈B) t∼a       = record
        { t∶T  = t∶T
        ; T∼A  = ®El⇒® (□ A≈B) t∼a
        ; a∈⊤  = realizability-Rf (□ A≈B) a∈El
        ; krip = helper
        }
        where open Glubox t∼a
              helper : Δ ⊢r σ ∶ Γ → Δ ⊢ t [ σ ] ≈ Nf⇒Exp (proj₁ (realizability-Rf (□ A≈B) a∈El (map len Δ) (mt σ))) ∶ T [ σ ]
              helper {Δ} {σ} ⊢σ = help (®El⇒®↑El (A≈B (ins (mt σ) 1)) rel)
                where open □Krip (krip L.[ [] ] ⊢σ)
                      open ER
                      ⊢σ′ = ⊢r⇒⊢s ⊢σ
                      ⊢GT = ®□⇒wf A≈B (®El⇒® (□ A≈B) t∼a)
                      ⊢tσ  = conv (t[σ] t∶T ⊢σ′) (≈-trans ([]-cong-Se′ T≈ ⊢σ′) (□-[] ⊢σ′ ⊢GT))
                      help : [] ∷⁺ Δ ⊢ unbox 1 (t [ σ ]) ∶ GT [ σ ； 1 ] ®↑[ i ] ua ∈El A≈B (ins (mt σ) 1) →
                             Δ ⊢ t [ σ ] ≈ Nf⇒Exp (proj₁ (realizability-Rf (□ A≈B) a∈El (map len Δ) (mt σ))) ∶ T [ σ ]
                      help record { a∈⊤ = a∈⊤ ; krip = krip }
                        with presup-s ⊢σ′
                      ...  | ⊢Δ , _
                           with realizability-Rf (□ A≈B) a∈El (map len Δ) (mt σ)
                              | a∈⊤ (map len ([] ∷⁺ Δ)) vone
                              | krip (⊢rI (⊢κ ⊢Δ))
                      ...     | box w , R□ .(map len Δ) ↘ub ↘w , _
                              | w′ , ↘w′ , _
                              | equiv
                              rewrite unbox-det ↘ub ↘ua
                                    | D-ap-vone (A [ ins (mt σ) 1 ])
                                    | D-ap-vone ua
                                    | Rf-det ↘w′ ↘w = ≈-conv (begin
                                                                t [ σ ]                       ≈⟨ □-η ⊢tσ ⟩
                                                                box (unbox 1 (t [ σ ]))       ≈˘⟨ box-cong ([I] (conv (□-E L.[ [] ] ⊢tσ (⊢κ ⊢Δ) refl) ([I；1] ⊢GT[σ；1]))) ⟩
                                                                box (unbox 1 (t [ σ ]) [ I ]) ≈⟨ box-cong (≈-conv equiv ([I] ⊢GT[σ；1])) ⟩
                                                                box (Nf⇒Exp w)                ∎)
                                                             (≈-sym (≈-trans ([]-cong-Se′ T≈ ⊢σ′) (□-[] ⊢σ′ ⊢GT)))
                        where ⊢GT[σ；1] = t[σ]-Se ⊢GT (s-； L.[ [] ] ⊢σ′ (⊢κ ⊢Δ) refl)
      ®El⇒®↑El {Π A S ρ} {_} {Γ} {t} {T} (Π iA RT) t∼a = record
        { t∶T  = t∶T
        ; T∼A  = ®El⇒® (Π iA RT) t∼a
        ; a∈⊤  = realizability-Rf (Π iA RT) a∈El
        ; krip = helper
        }
        where open GluΛ t∼a
              ⊢IT = ®Π-wf iA RT (®El⇒® (Π iA RT) t∼a)

              helper : Δ ⊢r σ ∶ Γ → Δ ⊢ t [ σ ] ≈ Nf⇒Exp (proj₁ (realizability-Rf (Π iA RT) a∈El (map len Δ) (mt σ))) ∶ T [ σ ]
              helper {Δ} {σ} ⊢σ
                with presup-s (⊢r⇒⊢s ⊢σ)
              ...  | ⊢Δ , _ = help
                where ⊢σ′   = ⊢r⇒⊢s ⊢σ
                      Tσ≈   = ≈-trans ([]-cong-Se′ T≈ ⊢σ′) (Π-[] ⊢σ′ ⊢IT ⊢OT)
                      ⊢tσ   = conv (t[σ] t∶T ⊢σ′) Tσ≈
                      ⊢ITσ  = t[σ]-Se ⊢IT ⊢σ′
                      ⊢ITσΔ = ⊢∷ ⊢Δ (t[σ]-Se ⊢IT ⊢σ′)
                      ⊢qσ   = ⊢q ⊢σ′ ⊢IT
                      ⊢OTqσ = t[σ]-Se ⊢OT ⊢qσ
                      ⊢σwk  = s-∘ (s-wk ⊢ITσΔ) ⊢σ′
                      open ΛRel (krip ⊢σ) using (IT-rel)
                      open ΛRel (krip (⊢r-∘ ⊢σ (⊢rwk ⊢ITσΔ))) using (ap-rel)
                      open ER
                      help : Δ ⊢ t [ σ ] ≈ Nf⇒Exp (proj₁ (realizability-Rf (Π iA RT) a∈El (map len Δ) (mt σ))) ∶ T [ σ ]
                      help
                        with ap-rel
                           | realizability-Rf (Π iA RT) a∈El (map len Δ) (mt σ)
                           | ®↓El⇒®El (iA (mt σ)) (v0∼x (iA (mt σ)) IT-rel)
                      ...  | ap-rel | Λ w , RΛ .(map len Δ) ↘a ↘⟦S⟧ ↘w , _ | v∼l
                           rewrite ø-vone (mt σ)
                           with RT (mt σ) (®El⇒∈El (iA (mt σ)) v∼l)
                              | ap-rel (®El-resp-T≈ (iA (mt σ)) v∼l ([∘]-Se ⊢IT ⊢σ′ (s-wk ⊢ITσΔ))) (®El⇒∈El (iA (mt σ)) v∼l)
                      ...     | record { ⟦T⟧ = ⟦T⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; T≈T′ = T≈T′ }
                              | record { fa = fa ; ↘fa = ↘fa ; ®fa = ®fa }
                              with ®El⇒®↑El T≈T′ ®fa
                      ...        | record { a∈⊤ = a∈⊤ ; krip = krip }
                                 with a∈⊤ (map len ((IT [ σ ]) ∺ Δ)) vone
                                    | krip (⊢rI ⊢ITσΔ)
                      ...           | w′ , ↘w′ , _
                                    | equiv
                                    rewrite D-ap-vone ⟦T⟧
                                          | D-ap-vone fa
                                          | ap-det ↘a ↘fa
                                          | ⟦⟧-det ↘⟦S⟧ ↘⟦T⟧
                                          | Rf-det ↘w′ ↘w = ≈-conv (begin
                                                                     t [ σ ]                        ≈⟨ Λ-η ⊢tσ ⟩
                                                                     Λ (t [ σ ] [ wk ] $ v 0)       ≈˘⟨ Λ-cong (≈-conv ($-cong (≈-conv ([∘] (s-wk ⊢ITσΔ) ⊢σ′ t∶T) eq)
                                                                                                                               (v-≈ ⊢ITσΔ here))
                                                                                                                       eq′) ⟩
                                                                     Λ (t [ σ ∘ wk ] $ v 0)         ≈˘⟨ Λ-cong ([I] (conv (Λ-E (conv (t[σ] t∶T ⊢σwk) eq) (vlookup ⊢ITσΔ here)) eq′)) ⟩
                                                                     Λ ((t [ σ ∘ wk ] $ v 0) [ I ]) ≈⟨ ≈-conv (Λ-cong equiv) (Π-cong (≈-refl ⊢ITσ) ([I] ⊢OTqσ)) ⟩
                                                                     Λ (Nf⇒Exp w)                   ∎)
                                                                   (≈-sym Tσ≈)
                        where ITσwk≈ = [∘]-Se ⊢IT ⊢σ′ (s-wk ⊢ITσΔ)
                              eq = begin
                                T [ σ ∘ wk ]                            ≈⟨ []-cong-Se′ T≈ ⊢σwk ⟩
                                Π IT OT [ σ ∘ wk ]                      ≈⟨ Π-[] ⊢σwk ⊢IT ⊢OT ⟩
                                Π (IT [ σ ∘ wk ]) (OT [ q (σ ∘ wk) ])   ≈⟨ Π-cong (≈-sym ITσwk≈) (≈-refl (t[σ]-Se ⊢OT (⊢q ⊢σwk ⊢IT))) ⟩
                                Π (IT [ σ ] [ wk ]) (OT [ q (σ ∘ wk) ]) ∎
                              eq′ = ≈-sym ([]-q-∘-,′ ⊢OT ⊢σwk (conv (vlookup ⊢ITσΔ here) ITσwk≈))


      ®⇒Rty-eq : (A≈B : A ≈ B ∈ 𝕌 i) → Γ ⊢ T ®[ i ] A≈B → Δ ⊢r σ ∶ Γ → ∃ λ W → Rty map len Δ - A [ mt σ ] ↘ W × Δ ⊢ T [ σ ] ≈ Nf⇒Exp W ∶ Se i
      ®⇒Rty-eq {↑ _ C} {Δ = Δ} {σ} (ne C≈C′) (⊢T , rel) ⊢σ
        with C≈C′ (map len Δ) (mt σ) | rel ⊢σ
      ...  | V , ↘V , _ | r              = ne V , Rne (map len Δ) ↘V , r
      ®⇒Rty-eq N T∼A ⊢σ                  = N , RN _ , ≈-trans ([]-cong-Se′ T∼A (⊢r⇒⊢s ⊢σ)) (N-[] _ (⊢r⇒⊢s ⊢σ))
      ®⇒Rty-eq {Δ = Δ} (U j<i eq) T∼A ⊢σ = Se _ , RU (map len Δ) , (≈-trans ([]-cong-Se′ T∼A (⊢r⇒⊢s ⊢σ)) (lift-⊢≈-Se (Se-[] _ (⊢r⇒⊢s ⊢σ)) j<i))
      ®⇒Rty-eq (□ A≈B) T∼A ⊢σ            = {!!}
      ®⇒Rty-eq (Π iA RT) T∼A ⊢σ          = {!!}
