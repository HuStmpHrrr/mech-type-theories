{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional


-- Realizability of the gluing models
--
-- Realizability of the gluing models state that if a term in the syntax and a value
-- in the semantics are related, then the term and the readback of the value are
-- equivalent up to any restricted weakening.
--
-- Similar to the realizability of the PER model, we show the following relations:
--
--     ®↓El ⊆ ®El ⊆ ®↑El     (1)
--            ®   ⊆ ®↑       (2)
--
-- where (1) are for terms and (2) are for types.
--
-- Due to ®El ⊆ ®↑El in particular, we can eventually derive that a term is equivalent
-- to its βη normal form.
module MLTT.Soundness.Realizability (fext : Extensionality 0ℓ (suc 0ℓ)) where

open import Lib
open import Data.List.Properties as Lₚ
open import Data.Nat.Properties as ℕₚ

open import MLTT.Statics.Properties
open import MLTT.Semantics.Readback
open import MLTT.Semantics.Realizability fext
open import MLTT.Semantics.Properties.PER fext
open import MLTT.Soundness.LogRel
open import MLTT.Soundness.Properties.LogRel fext


var-arith : ∀ Γ₁ (T : Typ) Γ₂ → len (Γ₁ ++ T ∷ Γ₂) ∸ len Γ₂ ∸ 1 ≡ len Γ₁
var-arith Γ₁ T Γ₂ = begin
  len (Γ₁ ++ T ∷ Γ₂) ∸ len Γ₂ ∸ 1
    ≡⟨ cong (λ n → n ∸ len Γ₂ ∸ 1) (Lₚ.length-++ Γ₁) ⟩
  len Γ₁ + ℕ.suc (len Γ₂) ∸ len Γ₂ ∸ 1
    ≡⟨ cong (_∸ 1) (ℕₚ.+-∸-assoc (len Γ₁) {ℕ.suc (len Γ₂)} (ℕₚ.m≤n⇒m≤1+n ℕₚ.≤-refl)) ⟩
  len Γ₁ + (ℕ.suc (len Γ₂) ∸ len Γ₂) ∸ 1
    ≡⟨ cong (λ n → len Γ₁ + n ∸ 1) (ℕₚ.m+n∸n≡m 1 (len Γ₂)) ⟩
  len Γ₁ + 1 ∸ 1
    ≡⟨ ℕₚ.m+n∸n≡m (len Γ₁) 1 ⟩
  len Γ₁
    ∎
  where open ≡-Reasoning



v0∼x-gen : ∀ Γ₁ {Γ₂} → Δ ⊢w σ ∶ Γ → Γ ≡ Γ₁ ++ T ∷ Γ₂ → Δ ⊢ v (len Γ₁) [ σ ] ≈ v (len Δ ∸ len Γ₂ ∸ 1) ∶ T [wk]* (1 + len Γ₁) [ σ ]
v0∼x-gen {Δ} {σ} {Γ} {T} Γ₁ {Γ₂} (r-I σ≈) refl
  with presup-s-≈ σ≈
...  | ⊢Δ , _ , ⊢I , ⊢Γ
     with ⊢≈-sym (⊢I-inv ⊢I)
...     | Γ≈Δ        = ≈-trans ([]-cong (v-≈ ⊢Γ n∈) σ≈)
                       (≈-trans ([I] (conv (ctxeq-tm Γ≈Δ (vlookup ⊢Γ n∈)) (≈-sym (≈-trans ([]-cong-Se″ ⊢T[wk]* σ≈) ([I] (ctxeq-tm Γ≈Δ ⊢T[wk]*))))))
                                helper)
  where n∈      = n∶T[wk]n∈!ΔTΓ ⊢Γ refl
        ⊢T[wk]* = proj₂ (proj₂ (presup-tm (⊢vn∶T[wk]suc[n] ⊢Γ refl)))
        [wkσ]≈  = []-cong-Se″ ⊢T[wk]* (s-≈-sym σ≈)
        helper : Δ ⊢ v (len Γ₁) ≈ v (len Δ ∸ len Γ₂ ∸ 1) ∶ T [wk]* (1 + len Γ₁) [ σ ]
        helper
          rewrite sym (⊢≈⇒len-head≡ Γ≈Δ)
                | var-arith Γ₁ T Γ₂ = ≈-conv (ctxeq-≈ Γ≈Δ (v-≈ ⊢Γ n∈)) (≈-trans (≈-sym ([I] (ctxeq-tm Γ≈Δ ⊢T[wk]*))) [wkσ]≈)
v0∼x-gen {Δ} {σ} {_} {_} Γ₁ {Γ₂} (r-p {_} {τ} {T′} ⊢τ σ≈) refl
  with presup-s (⊢w⇒⊢s ⊢τ)
...  | _ , ⊢∷ ⊢Γ ⊢T′ = begin
  v (len Γ₁) [ σ ]        ≈⟨ []-cong (v-≈ ⊢Γ n∈) σ≈ ⟩
  v (len Γ₁) [ p τ ]      ≈⟨ ≈-conv ([∘] ⊢τ′ (s-wk ⊢TΓ) (vlookup ⊢Γ n∈)) [wkτ]≈ ⟩
  v (len Γ₁) [ wk ] [ τ ] ≈⟨ ≈-conv ([]-cong ([wk] ⊢TΓ n∈) (s-≈-refl ⊢τ′)) wkτ≈ ⟩
  v (1 + len Γ₁) [ τ ]    ≈⟨ ≈-conv (v0∼x-gen (T′ ∷ Γ₁) ⊢τ refl) wkτ≈ ⟩
  v (len Δ ∸ len Γ₂ ∸ 1)  ∎
  where open ER
        n∈      = n∶T[wk]n∈!ΔTΓ ⊢Γ refl
        ⊢TΓ     = ⊢∷ ⊢Γ ⊢T′
        ⊢τ′     = ⊢w⇒⊢s ⊢τ
        ⊢T[wk]* = proj₂ (proj₂ (presup-tm (⊢vn∶T[wk]suc[n] ⊢Γ refl)))
        [wkτ]≈  = []-cong-Se″ ⊢T[wk]* (s-≈-sym σ≈)
        wkτ≈    = ≈-trans ([∘]-Se ⊢T[wk]* (s-wk ⊢TΓ) ⊢τ′) [wkτ]≈

v0∼x : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
       Γ ⊢ T ®[ i ] A≈B →
       T ∷ Γ ⊢ v 0 ∶ T [ wk ] ®↓[ i ] l (len Γ) ∈El A≈B
v0∼x {_} {_} {Γ} A≈B T∼A
  with ®⇒ty A≈B T∼A
...  | ⊢T
     with presup-tm ⊢T
...     | ⊢Γ , _ = record
  { t∶T  = vlookup ⊢TΓ here
  ; T∼A  = ®-one-sided A≈B A≈B (®-mon′ A≈B T∼A (r-p (⊢wI ⊢TΓ) (s-≈-sym (∘-I (s-wk ⊢TΓ)))))
  ; c∈⊥  = Bot-l (len Γ)
  ; krip = λ {Δ} {σ} ⊢σ → v0∼x-gen [] ⊢σ refl
  }
  where ⊢TΓ = ⊢∷ ⊢Γ ⊢T

-- The main realizability proof
--
-- This proof is done by well-founded induction. We list the induction hypothesis as a
-- module argument. In each level, we do a strctural induction on the PER model 𝕌
-- i. Mostly of the time we can get through by structural induction. We only need the
-- well-founded one when handling unvierses.
private
  module Real i (rec : ∀ {j} → j < i → ∀ {A B Γ T Δ σ} (A≈B : A ≈ B ∈ 𝕌 j) → Γ ⊢ T ®[ j ] A≈B → Δ ⊢w σ ∶ Γ → ∃ λ W → Rty len Δ - A ↘ W × Δ ⊢ T [ σ ] ≈ Nf⇒Exp W ∶ Se j) where
    mutual

      ®↓El⇒®El : (A≈B : A ≈ B ∈ 𝕌 i) → Γ ⊢ t ∶ T ®↓[ i ] c ∈El A≈B → Γ ⊢ t ∶ T ®[ i ] ↑ A c ∈El A≈B
      ®↓El⇒®El R@(ne C≈C′) t∼c                             = ne c∈⊥ , record
        { t∶T  = t∶T
        ; ⊢T   = ®⇒ty R T∼A
        ; krip = λ ⊢σ → proj₂ T∼A ⊢σ , krip ⊢σ
        }
        where open _⊢_∶_®↓[_]_∈El_ t∼c
      ®↓El⇒®El N t∼c                                       = ne c∈⊥ (λ ⊢σ → ≈-conv (krip ⊢σ) (≈-trans ([]-cong-Se′ T∼A (⊢w⇒⊢s ⊢σ)) (N-[] _ (⊢w⇒⊢s ⊢σ)))) , T∼A
        where open _⊢_∶_®↓[_]_∈El_ t∼c
      ®↓El⇒®El (U j<i eq) t∼c                              = record
        { t∶T = t∶T
        ; T≈  = T∼A
        ; A∈𝕌 = ne c∈⊥
        ; rel = subst (λ f → f _ _ _)
                      (sym (Glu-wellfounded-≡ j<i))
                      (conv t∶T T∼A , λ ⊢σ → ≈-conv (krip ⊢σ) (≈-trans ([]-cong-Se′ T∼A (⊢w⇒⊢s ⊢σ)) (lift-⊢≈-Se (Se-[] _ (⊢w⇒⊢s ⊢σ)) j<i)))
        }
        where open _⊢_∶_®↓[_]_∈El_ t∼c
      ®↓El⇒®El {Π A S ρ} {_} {Γ} {t} {T} {c} (Π iA RT) t∼c = record
        { t∶T  = t∶T
        ; a∈El = El-refl (Π iA RT) (Bot⊆El (Π iA RT) c∈⊥)
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
              ap-rel : Δ ⊢w σ ∶ Γ →
                       Δ ⊢ s ∶ IT [ σ ] ®[ i ] b ∈El iA →
                       (b∈ : b ∈′ El i iA) →
                       ∃ λ a → ↑ (Π A S ρ) (c) ∙ b ↘ a × Δ ⊢ t [ σ ] $ s ∶ OT [ σ , s ] ®[ i ] a ∈El (ΠRT.T≈T′ (RT b∈))
              ap-rel {_} {σ} {s} {b} ⊢σ s∼b b∈ = [ ΠRT.⟦T⟧ (RT b∈) ] c $′ ↓ (A) b
                                               , $∙ A c (ΠRT.↘⟦T⟧ (RT b∈))
                                               , ®↓El⇒®El (ΠRT.T≈T′ (RT b∈)) record  -- structural IH is invoked here
                                                 { t∶T  = conv (Λ-E ⊢tσ ⊢s) (≈-sym ([]-q-∘-,′ ⊢OT ⊢σ′ ⊢s))
                                                 ; T∼A  = ΠRel.OT-rel (G.krip ⊢σ) s∼b b∈
                                                 ; c∈⊥  = $-Bot c∈⊥ (Top-trans ↑.a∈⊤ (Top-sym ↑.a∈⊤))
                                                 ; krip = λ {_} {τ} ⊢τ →
                                                   let ⊢τ′ = ⊢w⇒⊢s ⊢τ
                                                       ⊢στ = s-∘ ⊢τ′ ⊢σ′
                                                       eq  = begin
                                                         OT [ (σ ∘ τ) , s [ τ ] ] ≈˘⟨ []-cong-Se″ ⊢OT (,-∘ ⊢σ′ ⊢IT ⊢s ⊢τ′) ⟩
                                                         OT [ σ , s ∘ τ ]         ≈˘⟨ [∘]-Se ⊢OT (s-, ⊢σ′ ⊢IT ⊢s) ⊢τ′ ⟩
                                                         OT [ σ , s ] [ τ ]       ∎
                                                   in begin
                                                   (t [ σ ] $ s) [ τ ]     ≈⟨ ≈-conv ($-[] ⊢τ′ ⊢tσ ⊢s) (≈-trans (≈-sym ([]-q-∘-, ⊢OT ⊢σ′ ⊢τ′ (t[σ] ⊢s ⊢τ′)))
                                                                                                                eq) ⟩
                                                   t [ σ ] [ τ ] $ s [ τ ] ≈⟨ ≈-conv ($-cong (≈-conv (≈-trans (≈-sym ([∘] ⊢τ′ ⊢σ′ t∶T)) (↓.krip (⊢w-∘ ⊢σ ⊢τ)))
                                                                                                     (≈-trans (helper ⊢στ)
                                                                                                              (Π-cong (≈-sym ([∘]-Se ⊢IT ⊢σ′ ⊢τ′))
                                                                                                                      (≈-refl (t[σ]-Se ⊢OT (⊢q ⊢στ ⊢IT))))))
                                                                                             (↑.krip ⊢τ))
                                                                                     (≈-trans (≈-sym ([]-q-∘-,′ ⊢OT ⊢στ (conv (t[σ] ⊢s ⊢τ′) ([∘]-Se ⊢IT ⊢σ′ ⊢τ′))))
                                                                                              eq) ⟩
                                                   _ $ _                   ∎
                                                 }
                where ⊢σ′ = ⊢w⇒⊢s ⊢σ
                      ⊢IT = ®Π-wf iA RT T∼A
                      ⊢s  = ®El⇒tm iA s∼b
                      helper : ∀ {Δ σ} → Δ ⊢s σ ∶ Γ → Δ ⊢ T [ σ ] ≈ Π (IT [ σ ]) (OT [ q σ ]) ∶ Se i
                      helper ⊢σ = ≈-trans ([]-cong-Se′ T≈ ⊢σ) (Π-[] ⊢σ ⊢IT ⊢OT)
                      ⊢tσ = conv (t[σ] t∶T ⊢σ′) (helper ⊢σ′)
                      open ER
                      module ↑ = _⊢_∶_®↑[_]_∈El_ (®El⇒®↑El iA s∼b)  -- structural IH is invoked here


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
        ; krip = λ ⊢σ → ≈-conv (®Nat⇒≈ t∼a ⊢σ) (≈-sym (≈-trans ([]-cong-Se′ T≈N (⊢w⇒⊢s ⊢σ)) (N-[] _ (⊢w⇒⊢s ⊢σ))))
        }
      ®El⇒®↑El (U′ j<i) t∼a                            = record
        { t∶T  = t∶T
        ; T∼A  = T≈
        ; a∈⊤  = λ ns → let W , ↘W , ↘W′ = 𝕌⊆TopT A∈𝕌 ns
                        in W , RU _ ↘W , RU _ ↘W′
        ; krip = λ {Δ} {σ} ⊢σ →
          let W , ↘W , eq = rec j<i A∈𝕌 (subst (λ f → f _ _ _) (Glu-wellfounded-≡ j<i) rel) ⊢σ  -- well-founded IH is invoked here
          in ≈-conv (subst (_ ⊢ _ ≈_∶ Se _) (cong Nf⇒Exp (Rty-det ↘W (proj₁ (proj₂ (𝕌⊆TopT A∈𝕌 (len Δ)))))) eq)
                    (≈-sym (≈-trans ([]-cong-Se′ T≈ (⊢w⇒⊢s ⊢σ)) (lift-⊢≈-Se (Se-[] _ (⊢w⇒⊢s ⊢σ)) j<i)))
        }
        where open GluU t∼a
      ®El⇒®↑El {Π A S ρ} {_} {Γ} {t} {T} {a} (Π iA RT) t∼a = record
        { t∶T  = t∶T
        ; T∼A  = ®El⇒® (Π iA RT) t∼a
        ; a∈⊤  = El⊆Top (Π iA RT) a∈El
        ; krip = helper
        }
        where open GluΛ t∼a
              ⊢IT = ®Π-wf iA RT (®El⇒® (Π iA RT) t∼a)

              helper : Δ ⊢w σ ∶ Γ → Δ ⊢ t [ σ ] ≈ Nf⇒Exp (proj₁ (El⊆Top (Π iA RT) a∈El (len Δ))) ∶ T [ σ ]
              helper {Δ} {σ} ⊢σ
                with presup-s (⊢w⇒⊢s ⊢σ)
              ...  | ⊢Δ , _ = let w , ↘w , _ = El⊆Top (Π iA RT) a∈El (len Δ) in help w ↘w
                where ⊢σ′   = ⊢w⇒⊢s ⊢σ
                      Tσ≈   = ≈-trans ([]-cong-Se′ T≈ ⊢σ′) (Π-[] ⊢σ′ ⊢IT ⊢OT)
                      ⊢tσ   = conv (t[σ] t∶T ⊢σ′) Tσ≈
                      ⊢ITσ  = t[σ]-Se ⊢IT ⊢σ′
                      ⊢ITσΔ = ⊢∷ ⊢Δ (t[σ]-Se ⊢IT ⊢σ′)
                      ⊢qσ   = ⊢q ⊢σ′ ⊢IT
                      ⊢OTqσ = t[σ]-Se ⊢OT ⊢qσ
                      ⊢σwk  = s-∘ (s-wk ⊢ITσΔ) ⊢σ′
                      open ΛRel (krip ⊢σ) using (IT-rel)
                      open ΛRel (krip (⊢w-∘ ⊢σ (⊢wwk ⊢ITσΔ))) using (ap-rel)
                      open ER
                      help : ∀ w → Rf L.length Δ - ↓ (Π A S ρ) a ↘ w → Δ ⊢ t [ σ ] ≈ Nf⇒Exp w ∶ T [ σ ]
                      help (Λ w) (RΛ .(len Δ) ↘a ↘⟦S⟧ ↘w)
                        with ap-rel
                           | ®↓El⇒®El iA (v0∼x iA IT-rel)  -- structural IH is invoked here
                      ...  | ap-rel | v∼l
                           with RT (®El⇒∈El iA v∼l)
                              | ap-rel (®El-resp-T≈ iA v∼l ([∘]-Se ⊢IT ⊢σ′ (s-wk ⊢ITσΔ))) (®El⇒∈El iA v∼l)
                      ...     | record { ⟦T⟧ = ⟦T⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; T≈T′ = T≈T′ }
                              | record { fa = fa ; ↘fa = ↘fa ; ®fa = ®fa }
                              with ®El⇒®↑El T≈T′ ®fa  -- structural IH is invoked here
                      ...        | record { a∈⊤ = a∈⊤ ; krip = krip }
                                 with a∈⊤ (length ((IT [ σ ]) ∷ Δ))
                                    | krip (⊢wI ⊢ITσΔ)
                      ...           | w′ , ↘w′ , _
                                    | equiv
                                    rewrite ap-det ↘a ↘fa
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


      ®⇒Rty-eq : (A≈B : A ≈ B ∈ 𝕌 i) → Γ ⊢ T ®[ i ] A≈B → Δ ⊢w σ ∶ Γ → ∃ λ W → Rty len Δ - A ↘ W × Δ ⊢ T [ σ ] ≈ Nf⇒Exp W ∶ Se i
      ®⇒Rty-eq {↑ _ C} {Δ = Δ} {σ} (ne C≈C′) (⊢T , rel) ⊢σ
        with C≈C′ (len Δ) | rel ⊢σ
      ...  | V , ↘V , _ | r                          = ne V , Rne (len Δ) ↘V , r
      ®⇒Rty-eq N T∼A ⊢σ                              = N , RN _ , ≈-trans ([]-cong-Se′ T∼A (⊢w⇒⊢s ⊢σ)) (N-[] _ (⊢w⇒⊢s ⊢σ))
      ®⇒Rty-eq {Δ = Δ} (U j<i eq) T∼A ⊢σ             = Se _ , RU (len Δ) , (≈-trans ([]-cong-Se′ T∼A (⊢w⇒⊢s ⊢σ)) (lift-⊢≈-Se (Se-[] _ (⊢w⇒⊢s ⊢σ)) j<i))
      ®⇒Rty-eq {Π A S ρ} {_} {_} {T} {Δ} {σ} (Π iA RT) T∼A ⊢σ
        with presup-s (⊢w⇒⊢s ⊢σ)
      ...  | ⊢Δ , _ = helper
        where open GluΠ T∼A
              ⊢σ′   = ⊢w⇒⊢s ⊢σ
              ⊢IT   = ®Π-wf iA RT T∼A
              ⊢ITσ  = t[σ]-Se ⊢IT ⊢σ′
              ⊢ITσΔ = ⊢∷ ⊢Δ (t[σ]-Se ⊢IT ⊢σ′)
              ⊢qσ   = ⊢q ⊢σ′ ⊢IT
              ⊢OTqσ = t[σ]-Se ⊢OT ⊢qσ
              open ΠRel (krip ⊢σ) using (IT-rel)
              open ΠRel (krip (⊢w-∘ ⊢σ (⊢wwk ⊢ITσΔ))) using (OT-rel)
              open ER

              helper : ∃ λ W → Rty len Δ - Π A S ρ ↘ W × Δ ⊢ T [ σ ] ≈ Nf⇒Exp W ∶ Se i
              helper
                with ®⇒Rty-eq iA IT-rel (⊢wI ⊢Δ)
                   | ®↓El⇒®El iA (v0∼x iA IT-rel)
                   | OT-rel
              ...  | WI , ↘WI , ≈WI
                   | v∼l
                   | OT-rel
                   with RT (®El⇒∈El iA v∼l)
                      | OT-rel (®El-resp-T≈ iA v∼l ([∘]-Se ⊢IT ⊢σ′ (s-wk ⊢ITσΔ))) (®El⇒∈El iA v∼l)
              ...     | record { ⟦T⟧ = ⟦S⟧ ; ↘⟦T⟧ = ↘⟦S⟧ ; T≈T′ = T≈T′ }
                      | rel
                      with ®⇒Rty-eq T≈T′ rel (⊢wI ⊢ITσΔ)
              ...        | WO , ↘WO , ≈WO = Π WI WO , RΠ (len Δ) ↘WI ↘⟦S⟧ ↘WO
                                          , (begin
                                              T [ σ ]                               ≈⟨ []-cong-Se′ T≈ ⊢σ′ ⟩
                                              Π IT OT [ σ ]                         ≈⟨ Π-[] ⊢σ′ ⊢IT ⊢OT ⟩
                                              Π (IT [ σ ]) (OT [ q σ ])             ≈˘⟨ Π-cong ([I] ⊢ITσ) ([I] (ctxeq-tm (∷-cong (⊢≈-refl ⊢Δ) (≈-sym ([I] ⊢ITσ))) ⊢OTqσ)) ⟩
                                              Π (IT [ σ ] [ I ]) (OT [ q σ ] [ I ]) ≈⟨ Π-cong ≈WI (ctxeq-≈ (∷-cong (⊢≈-refl ⊢Δ) (≈-sym ([I] ⊢ITσ))) ≈WO) ⟩
                                              Nf⇒Exp (Π WI WO)                      ∎)


-- Wrap up the well-founded induction.
®⇒Rty-eq : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
           Γ ⊢ T ®[ i ] A≈B →
           Δ ⊢w σ ∶ Γ →
           ----------------------------------
           ∃ λ W → Rty len Δ - A ↘ W × Δ ⊢ T [ σ ] ≈ Nf⇒Exp W ∶ Se i
®⇒Rty-eq {i = i} = <-Measure.wfRec (λ i → ∀ {A B Γ T Δ σ} →
                                          (A≈B : A ≈ B ∈ 𝕌 i) →
                                          Γ ⊢ T ®[ i ] A≈B →
                                          Δ ⊢w σ ∶ Γ →
                                          ∃ λ W → Rty len Δ - A ↘ W × Δ ⊢ T [ σ ] ≈ Nf⇒Exp W ∶ Se i)
                                   Real.®⇒Rty-eq i


®↓El⇒®El : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
           Γ ⊢ t ∶ T ®↓[ i ] c ∈El A≈B →
           -------------------------------
           Γ ⊢ t ∶ T ®[ i ] ↑ A c ∈El A≈B
®↓El⇒®El {i = i} = Real.®↓El⇒®El i (λ _ → ®⇒Rty-eq)


®El⇒®↑El : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
           Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
           -----------------------------
           Γ ⊢ t ∶ T ®↑[ i ] a ∈El A≈B
®El⇒®↑El {i = i} = Real.®El⇒®↑El i (λ _ → ®⇒Rty-eq)


-- From what we have, we are ready for concluding ® ⊆ ®↑ for types.
®⇒®↑ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
       Γ ⊢ T ®[ i ] A≈B →
       --------------------
       Γ ⊢ T ®↑[ i ] A≈B
®⇒®↑ A≈B T∼A = record
  { t∶T  = ®⇒ty A≈B T∼A
  ; A∈⊤  = 𝕌⊆TopT A≈B
  ; krip = λ {Δ} {σ} ⊢σ → let W , ↘W , Tσ≈ = ®⇒Rty-eq A≈B T∼A ⊢σ
                          in subst (λ t → _ ⊢ _ [ _ ] ≈ Nf⇒Exp t ∶ Se _)
                                   (Rty-det ↘W (proj₁ (proj₂ (𝕌⊆TopT A≈B (len Δ)))))
                                   Tσ≈
  }

v0®x : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
       Γ ⊢ T ®[ i ] A≈B →
       T ∷ Γ ⊢ v 0 ∶ T [ wk ] ®[ i ] ↑ A (l (len Γ)) ∈El A≈B
v0®x A≈B T∼A = ®↓El⇒®El A≈B (v0∼x A≈B T∼A)


-- As a corollary, if two types are related to the same semantic types, then both
-- types are equivalent.
®⇒≈ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
      Γ ⊢ T ®[ i ] A≈B →
      Γ ⊢ T′ ®[ i ] A≈B →
      ----------------------------
      Γ ⊢ T ≈ T′ ∶ Se i
®⇒≈ {_} {_} {_} {T} {T′} A≈B T∼A T′∼A
  with presup-tm (®⇒ty A≈B T∼A)
...  | ⊢Γ , _
    with ®⇒Rty-eq A≈B T∼A (⊢wI ⊢Γ) | ®⇒Rty-eq A≈B T′∼A (⊢wI ⊢Γ)
...    | W , ↘W , T≈W | _ , ↘W₁ , T′≈W₁
      rewrite Rty-det ↘W₁ ↘W = begin
        T        ≈⟨ [I]-≈ˡ-Se T≈W ⟩
        Nf⇒Exp W ≈˘⟨ [I]-≈ˡ-Se T′≈W₁ ⟩
        T′       ∎
  where
    open ER


-- If two terms are related to the same semantic value, then both terms are
-- equivalent.
®El⇒≈ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
        Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
        Γ ⊢ t′ ∶ T ®[ i ] a ∈El A≈B →
        ----------------------------
        Γ ⊢ t ≈ t′ ∶ T
®El⇒≈ {_} {_} {Γ} {t} {_} {_} {t′} A≈B t∼a t′∼a
  with presup-tm (®El⇒ty A≈B t∼a)
...  | ⊢Γ , _
     with ®El⇒®↑El A≈B t∼a | ®El⇒®↑El A≈B t′∼a
...     | record { a∈⊤ = t∈⊤ ; krip = tkrip }
        | record { a∈⊤ = t′∈⊤ ; krip = t′krip }
        with t∈⊤ (len Γ)  | tkrip (⊢wI ⊢Γ)
           | t′∈⊤ (len Γ) | t′krip (⊢wI ⊢Γ)
...        | w  , ↘w  , _ | ≈w
           | w′ , ↘w′ , _ | ≈w′
           rewrite Rf-det ↘w′ ↘w = ≈-trans ([I]-≈ˡ ≈w) (≈-sym ([I]-≈ˡ ≈w′))


®El⇒≈-gen : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
            Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
            Γ ⊢ t′ ∶ T′ ®[ i ] a ∈El A≈B →
            ----------------------------
            Γ ⊢ t ≈ t′ ∶ T
®El⇒≈-gen A≈B t∼a t′∼a = ®El⇒≈ A≈B t∼a (®El-resp-T≈ A≈B t′∼a (®⇒≈ A≈B (®El⇒® A≈B t′∼a) (®El⇒® A≈B t∼a)))
