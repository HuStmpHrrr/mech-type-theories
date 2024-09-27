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
module NonCumulative.Soundness.Realizability (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂) where

open import Lib
open import Data.List.Properties as Lₚ
open import Data.Nat.Properties as ℕₚ

open import NonCumulative.Statics.Ascribed.Misc
open import NonCumulative.Statics.Ascribed.CtxEquiv
open import NonCumulative.Statics.Ascribed.Refl
open import NonCumulative.Statics.Ascribed.Presup
open import NonCumulative.Statics.Ascribed.Properties.Contexts
open import NonCumulative.Statics.Ascribed.Properties
open import NonCumulative.Semantics.Readback
open import NonCumulative.Semantics.Realizability fext
open import NonCumulative.Semantics.Properties.PER fext
open import NonCumulative.Soundness.LogRel
open import NonCumulative.Soundness.Properties.LogRel fext
open import NonCumulative.Soundness.Properties.Bundle fext

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

var-arith : ∀ (Γ₁ : List lTyp) (T : Typ) Γ₂ i → len (Γ₁ ++ (T ↙ i) ∷ Γ₂) ∸ len Γ₂ ∸ 1 ≡ len Γ₁
var-arith Γ₁ T Γ₂ i = begin
    len (Γ₁ ++ (T ↙ i) ∷ Γ₂) ∸ len Γ₂ ∸ 1
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

v0∼x-gen : ∀ Γ₁ {Γ₂ i} → Δ ⊢w σ ∶ Γ → Γ ≡ Γ₁ ++ (T ↙ i) ∷ Γ₂ → Δ ⊢ v (len Γ₁) [ σ ] ≈ v (len Δ ∸ len Γ₂ ∸ 1) ∶[ i ] T [wk]* (1 + len Γ₁) [ σ ]
v0∼x-gen {Δ} {σ} {.(Γ₁ L.++ (T ↙ i) L.∷ Γ₂)} {T} Γ₁ {Γ₂} {i} (r-I σ≈) refl
  with presup-s-≈ σ≈
... | ⊢Δ , ⊢σ , ⊢I , ⊢Γ
    with ⊢≈-sym (⊢I-inv ⊢I)
... | Γ≈Δ = ≈-trans ([]-cong (v-≈ ⊢Γ n∈) σ≈) (≈-trans ([I] (conv (ctxeq-tm Γ≈Δ (vlookup ⊢Γ n∈)) (≈-sym (≈-trans ([]-cong-Se‴ ⊢T[wk]* σ≈) ([I] (ctxeq-tm Γ≈Δ ⊢T[wk]*)))))) helper)
  where 
    n∈      = n∶T[wk]n∈!ΔTΓ Γ₁ refl
    ⊢T[wk]* = proj₂ (presup-tm (⊢vn∶T[wk]suc[n] ⊢Γ refl))
    [wkσ]≈  = []-cong-Se‴ ⊢T[wk]* σ≈
    helper : Δ ⊢ v (len Γ₁) ≈ v (len Δ ∸ len Γ₂ ∸ 1) ∶[ i ] T [wk]* (1 + len Γ₁) [ σ ]
    helper
      rewrite sym (≈⇒len≡ Γ≈Δ)
            | var-arith Γ₁ T Γ₂ i = ≈-conv (ctxeq-≈ Γ≈Δ (v-≈ ⊢Γ n∈)) (≈-trans (≈-sym ([I] (ctxeq-tm Γ≈Δ ⊢T[wk]*))) (≈-sym [wkσ]≈))
v0∼x-gen {Δ} {σ} {.(Γ₁ L.++ (T ↙ i) L.∷ Γ₂)} {T} Γ₁ {Γ₂} {i} (r-p {_} {τ} {T′} {_} {_} {i₁} ⊢τ σ≈) refl
  with presup-s-≈ σ≈
... | _ , ⊢σ , _ , _
    with presup-s (⊢w⇒⊢s ⊢τ)
... | _ , ⊢∷ ⊢Γ ⊢T′ = begin
    v (len Γ₁) [ σ ] ≈⟨ []-cong (v-≈ ⊢Γ n∈) σ≈ ⟩
    v (len Γ₁) [ p τ ] ≈⟨ ≈-conv ([∘] ⊢τ′ (s-wk ⊢TΓ) (vlookup ⊢Γ n∈)) (≈-sym [wkτ]≈) ⟩
    v (len Γ₁) [ wk ] [ τ ] ≈⟨ ≈-conv ([]-cong ([wk] ⊢Γ ⊢T′ n∈) (s-≈-refl ⊢τ′)) wkτ≈ ⟩
    v (1 + len Γ₁) [ τ ] ≈⟨ ≈-conv (v0∼x-gen (( T′ ↙ i₁) ∷ Γ₁) ⊢τ refl) wkτ≈ ⟩
    v (len Δ ∸ len Γ₂ ∸ 1) 
  ∎
  where 
    open ER
    n∈      = n∶T[wk]n∈!ΔTΓ Γ₁ refl
    ⊢TΓ     = ⊢∷ ⊢Γ ⊢T′
    ⊢τ′     = ⊢w⇒⊢s ⊢τ
    ⊢T[wk]* = proj₂ (presup-tm (⊢vn∶T[wk]suc[n] ⊢Γ refl))
    [wkτ]≈  = []-cong-Se‴ ⊢T[wk]* σ≈
    wkτ≈    = ≈-trans ([∘]-Se ⊢T[wk]* (s-wk ⊢TΓ) ⊢τ′) (≈-sym [wkτ]≈)

v0∼x : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
       Γ ⊢ T ®[ i ] A≈B →
       (T ↙ i) ∷ Γ ⊢ v 0 ∶ T [ wk ] ®↓[ i ] l (len Γ) ∈El A≈B
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

private
  module Real where
    mutual
      ®↓El⇒®El : ∀ {i} → (rc : ∀ {j} → j < i → ∀ {A B Γ T Δ σ} (A≈B : A ≈ B ∈ 𝕌 j) → Γ ⊢ T ®[ j ] A≈B → Δ ⊢w σ ∶ Γ → ∃ λ W → Rty len Δ - A at j ↘ W × Δ ⊢ T [ σ ] ≈ Nf⇒Exp W ∶[ 1 + j ] Se j) →
                 (A≈B : A ≈ B ∈ 𝕌 i) → Γ ⊢ t ∶ T ®↓[ i ] c ∈El A≈B → Γ ⊢ t ∶ T ®[ i ] ↑ i A c ∈El A≈B
      ®↓El⇒®El rc R@(ne′ C≈C′) t®↓ = ne′ c∈⊥ , record
        { t∶T = t∶T
        ; ⊢T = ®⇒ty R T∼A
        ; krip = λ ⊢σ → proj₂ T∼A ⊢σ , (krip ⊢σ)
        }
        where open _⊢_∶_®↓[_]_∈El_ t®↓
      ®↓El⇒®El rc N′ t®↓ = ne c∈⊥ (λ ⊢σ → ≈-conv (krip ⊢σ) (≈-trans ([]-cong-Se′ T∼A (⊢w⇒⊢s ⊢σ)) (N-[] (⊢w⇒⊢s ⊢σ)))) , T∼A
        where open _⊢_∶_®↓[_]_∈El_ t®↓
      ®↓El⇒®El rc U′ t®↓ = record
        { t∶T = t∶T
        ; T≈ = T∼A
        ; A∈𝕌 = ne′ c∈⊥
        ; rel = (conv t∶T T∼A) , λ ⊢σ → ≈-conv (krip ⊢σ) (≈-trans ([]-cong-Se′ T∼A (⊢w⇒⊢s ⊢σ)) (Se-[] _ (⊢w⇒⊢s ⊢σ)))
        }
        where open _⊢_∶_®↓[_]_∈El_ t®↓
      ®↓El⇒®El {Π j A (S ↙ k) ρ} {_} {Γ} {t} {T} {c} rc (Π′ {_} {_} jA RT) record { t∶T = t∶T ; T∼A = T∼A ; c∈⊥ = c∈⊥ ; krip = Πkrip } 
        rewrite 𝕌-wf-gen j (ΠI≤′ j k refl)
              | 𝕌-wf-gen k (ΠO≤′ j k refl)
              | Glu-wf-gen j (ΠI≤′ j k refl)
              | Glu-wf-gen k (ΠO≤′ j k refl) = record
        { t∶T = t∶T
        ; a∈El = El-Π-𝕌 refl jA RT (El-refl (Π-𝕌 jA RT refl) (Bot⊆El (Π-𝕌 jA RT refl) c∈⊥))
        ; IT = IT
        ; OT = OT
        ; ⊢IT = ⊢IT
        ; ⊢OT = ⊢OT
        ; T≈ = T≈
        ; krip = λ {Δ} {σ} ⊢σ → record
          { IT-rel = ΠRel.IT-rel (G.krip ⊢σ)
          ; ap-rel = λ s® b∈ → helper ⊢σ jA RT b∈ s® G.krip
          }
        }
        where 
          module G = GluΠ T∼A
          open G
          helper :  Δ ⊢w σ ∶ Γ →
                    (jA : A ≈ A′ ∈ 𝕌 j) →
                    (RT : ∀ {a a′} → a ≈ a′ ∈ El j jA → ΠRT S (ρ ↦ a) T′ (ρ′ ↦ a′) (𝕌 k)) →
                    (b∈ : b ∈′ El j jA) →
                    Δ ⊢ s ∶ IT [ σ ] ®[ j ] b ∈El jA →
                    (∀ {Δ σ} → Δ ⊢w σ ∶ Γ →
                      ΠRel j Δ IT OT σ (𝕌-wellfounded j) jA
                        (_⊢_®[ j ] jA)
                        (λ a∈ Γ t → Γ ⊢ t ®[ k ] ΠRT.T≈T′ (RT a∈))
                        (_⊢_∶_®[ j ]_∈El jA)) →
                    ------------------------------
                    ΛKripke Δ (t [ σ ] $ s) (OT [ σ , s ∶ IT ↙ j ]) (↑ (max j k) (Π j A (S ↙ k) ρ) (c)) b (_⊢_∶_®[ k ]_∈El (ΠRT.T≈T′ (RT b∈)))
          helper {Δ} {σ = σ} {b = b} {s} ⊢σ jA RT b∈ s® Gkrip
            with ⊢Δ , _ ← presup-s (⊢w⇒⊢s ⊢σ) = record 
              { fa = [ ΠRT.⟦T⟧ (RT b∈) ↙ k ] c $′ ↓ j A b 
              ; ↘fa = $∙ A c (ΠRT.↘⟦T⟧ (RT b∈)) refl
              ; ®fa = ®↓El⇒®El (λ l<k → rc (ΠO≤ refl l<k)) (ΠRT.T≈T′ (RT b∈)) (record 
                { t∶T = conv (Λ-E ⊢ITσ ⊢OTqσ t∶IT[σ]OT[qσ] ⊢s refl) (≈-sym ([]-q-∘-,′ ⊢OT ⊢σ′ ⊢s)) 
                ; T∼A = ΠRel.OT-rel (Gkrip ⊢σ) s® b∈ 
                ; c∈⊥ = $-Bot c∈⊥ (Top-trans ↑.a∈⊤ (Top-sym ↑.a∈⊤)) 
                ; krip = λ {Δ′} {τ} ⊢τ → helper₁ ⊢τ }) }
            where ⊢σ′ = ⊢w⇒⊢s ⊢σ
                  ⊢s = ®El⇒tm jA s®
                  Tσ≈   = ≈-trans ([]-cong-Se′ T≈ ⊢σ′) (Π-[] ⊢σ′ ⊢IT ⊢OT refl)
                  t∶IT[σ]OT[qσ] = conv (t[σ] t∶T ⊢σ′) Tσ≈
                  ⊢ITσ  = t[σ]-Se ⊢IT ⊢σ′
                  ⊢ITσΔ = ⊢∷ ⊢Δ (t[σ]-Se ⊢IT ⊢σ′)
                  ⊢qσ   = ⊢q ⊢Δ ⊢σ′ ⊢IT
                  ⊢OTqσ = t[σ]-Se ⊢OT ⊢qσ
                  open ER
                  module ↑ = _⊢_∶_®↑[_]_∈El_≈_ (®El⇒®↑El (λ l<j → rc (ΠI≤ refl l<j)) jA s®)

                  helper₁ : Δ′ ⊢w τ ∶ Δ →
                            Δ′ ⊢ (t [ σ ] $ s) [ τ ] ≈ Ne⇒Exp (proj₁ (c∈⊥ (len Δ′))) $ Nf⇒Exp (proj₁ ((Top-trans ↑.a∈⊤ (Top-sym ↑.a∈⊤)) (len Δ′)))∶[ k ] OT [ σ , s ∶ IT ↙ j ] [ τ ]
                  helper₁ {Δ′} {τ} ⊢τ = begin
                                          (t [ σ ] $ s) [ τ ] ≈⟨ ≈-conv ($-[] ⊢ITσ ⊢OTqσ ⊢τ′ t∶IT[σ]OT[qσ] ⊢s refl) (≈-trans (≈-sym ([]-q-∘-, ⊢OT ⊢σ′ ⊢τ′ (t[σ] ⊢s ⊢τ′))) eq) ⟩
                                          t [ σ ] [ τ ] $ s [ τ ] ≈⟨ ≈-conv ($-cong ⊢IT[σ][τ] ⊢OT[qστ]′
                                                                                    (≈-conv (≈-trans (≈-sym ([∘] ⊢τ′ ⊢σ′ t∶T)) (Πkrip (⊢w-∘ ⊢σ ⊢τ)))
                                                                                            (≈-trans (eq′ ⊢στ) (Π-cong ⊢IT[σ∘τ] (≈-sym ITστ≈) (≈-refl ⊢OT[qστ]) refl)))
                                                                                    (↑.krip ⊢τ) refl)
                                                                              (≈-trans (≈-trans ([]-cong-Se (≈-refl ⊢OT[qστ]′) (s-, (s-I ⊢Δ′) ⊢IT[σ][τ] ⊢sτ) (,-cong (I-≈ ⊢Δ′)  ⊢IT[σ][τ] ITστ≈ (≈-refl ⊢sτ)))
                                                                                                (≈-sym ([]-q-∘-,′ ⊢OT ⊢στ (conv (t[σ] ⊢s ⊢τ′) ([∘]-Se ⊢IT ⊢σ′ ⊢τ′)))) ) eq) ⟩
                                          _ $ _
                                        ∎
                      where 
                        ⊢τ′ = ⊢w⇒⊢s ⊢τ
                        ⊢Δ′ = proj₁ (presup-s ⊢τ′)
                        ⊢στ = s-∘ ⊢τ′ ⊢σ′
                        ITστ≈ = [∘]-Se ⊢IT ⊢σ′ ⊢τ′
                        ⊢OT[qστ] = t[σ]-Se ⊢OT (⊢q ⊢Δ′ ⊢στ ⊢IT)
                        ⊢IT[σ][τ] = proj₁ (proj₂ (presup-≈ ITστ≈))
                        ⊢IT[σ∘τ] = proj₁ (proj₂ (proj₂ (presup-≈ ITστ≈)))
                        ⊢OT[qστ]′ = ctxeq-tm (∷-cong (⊢≈-refl ⊢Δ′) ⊢IT[σ∘τ] ⊢IT[σ][τ] (≈-sym ITστ≈) (≈-sym ITστ≈)) (t[σ]-Se ⊢OT (⊢q ⊢Δ′ ⊢στ ⊢IT))
                        ⊢sτ : Δ′ ⊢ s [ τ ] ∶[ j ] IT [ σ ] [ τ ] [ I ]
                        ⊢sτ = conv (t[σ] ⊢s ⊢τ′) (≈-sym ([I] ⊢IT[σ][τ]))
                        eq = begin
                              OT [ (σ ∘ τ) , s [ τ ] ∶ IT ↙ j ] ≈˘⟨ []-cong-Se‴ ⊢OT (,-∘ ⊢σ′ ⊢IT ⊢s ⊢τ′) ⟩
                              OT [ σ , s ∶ IT ↙ j ∘ τ ]         ≈˘⟨ [∘]-Se ⊢OT (s-, ⊢σ′ ⊢IT ⊢s) ⊢τ′ ⟩
                              OT [ σ , s ∶ IT ↙ j ] [ τ ]
                            ∎
                        eq′ : ∀ {Δ σ} → Δ ⊢s σ ∶ Γ → Δ ⊢ T [ σ ] ≈ Π (IT [ σ ] ↙ j) (OT [ q (IT ↙ j) σ ] ↙ k) ∶[ 1 + max j k ] Se (max j k)
                        eq′ ⊢σ = ≈-trans ([]-cong-Se′ T≈ ⊢σ) (Π-[] ⊢σ ⊢IT ⊢OT refl)
      ®↓El⇒®El {Li j k A} {Γ = Γ} {t = t} {T = T} {c = c} rc (L′ kA) record { t∶T = t∶T ; T∼A = T∼A ; c∈⊥ = c∈⊥ ; krip = lkrip } 
        rewrite 𝕌-wf-gen k (Li≤′ j k refl)
              | Glu-wf-gen k (Li≤′ j k refl) = record 
          { t∶T = t∶T 
          ; ⊢UT = ⊢UT 
          ; a∈El = El-L-𝕌 kA refl (El-refl (L-𝕌 kA refl) (Bot⊆El (L-𝕌 kA refl) c∈⊥))
          ; T≈ = T≈ 
          ; krip = λ ⊢σ → record { ua = ↑ k A (unli c) ; ↘ua = unli↘ refl ; ®ua = helper ⊢σ kA (G.krip ⊢σ) } 
          }
        where 
          module G = GluL T∼A
          open G
          helper : Δ ⊢w σ ∶ Γ →
                    (kA : A ≈ A′ ∈ 𝕌 k) →
                    Δ ⊢ UT [ σ ] ®[ k ] kA →
                    -------------------------------
                    Δ ⊢ (unlift t) [ σ ] ∶ UT [ σ ] ®[ k ] ↑ k A (unli c) ∈El kA
          helper {Δ = Δ} ⊢σ kA UTkrip = ®↓El⇒®El (λ l<k → rc (Li≤ refl l<k)) kA (record
                { t∶T = t[σ] (L-E _ ⊢UT (conv t∶T T≈)) (⊢w⇒⊢s ⊢σ)
                ; T∼A = UTkrip
                ; c∈⊥ = λ n → let V , ↘V , _ = c∈⊥ n in (unlift V) , (Runli _ ↘V) , (Runli _ ↘V)
                ; krip = λ {Δ′} {τ} ⊢τ →
                  let t≈ = lkrip (⊢w-∘ ⊢σ ⊢τ)
                      ⊢σ′ = ⊢w⇒⊢s ⊢σ
                      ⊢τ′ = ⊢w⇒⊢s ⊢τ
                      ⊢στ′ = s-∘ ⊢τ′ ⊢σ′
                  in
                  ≈-conv (≈-trans (≈-sym ([∘] ⊢τ′ ⊢σ′ (L-E _ ⊢UT (conv t∶T T≈)))) (≈-trans (unlift-[] _ ⊢UT ⊢στ′ (conv t∶T T≈))
                          (unlift-cong _ (t[σ]-Se ⊢UT ⊢στ′) (≈-conv t≈ (≈-trans ([]-cong-Se′ T≈ ⊢στ′) (Liftt-[] _ ⊢στ′ ⊢UT)))))) (≈-sym ([∘]-Se ⊢UT ⊢σ′ ⊢τ′))
                }
              )

      ®El⇒®↑El : ∀ {i} → (rc : ∀ {j} → j < i → ∀ {A B Γ T Δ σ} (A≈B : A ≈ B ∈ 𝕌 j) → Γ ⊢ T ®[ j ] A≈B → Δ ⊢w σ ∶ Γ → ∃ λ W → Rty len Δ - A at j ↘ W × Δ ⊢ T [ σ ] ≈ Nf⇒Exp W ∶[ 1 + j ] Se j) →
                 (A≈B : A ≈ B ∈ 𝕌 i) → Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B → Γ ⊢ t ∶ T ®↑[ i ] a ∈El A ≈ B
      ®El⇒®↑El rc (ne′ C≈C′) (ne c≈c refl _ , glu) = record 
        { t∶T = t∶T 
        ; A≈B = ne′ C≈C′ 
        ; T∼A = ⊢T , λ ⊢σ → proj₁ (krip ⊢σ) 
        ; a∈⊤ = Bot⊆Top c≈c 
        ; krip = λ ⊢σ → proj₂ (krip ⊢σ) 
        }
        where open GluNe glu
      ®El⇒®↑El rc N′ (t∶Nat® , T≈N) 
        with ⊢Γ , _ ← presup-≈ T≈N = record
          { t∶T = conv (®Nat⇒∶Nat t∶Nat® ⊢Γ) (≈-sym T≈N)
          ; A≈B = N′
          ; T∼A = T≈N
          ; a∈⊤ = ®Nat⇒∈Top t∶Nat®
          ; krip = λ ⊢σ → ≈-conv (®Nat⇒≈ t∶Nat® ⊢σ) (≈-sym (≈-trans ([]-cong-Se′ T≈N (⊢w⇒⊢s ⊢σ)) (N-[] (⊢w⇒⊢s ⊢σ))))
          }
      ®El⇒®↑El {Γ = Γ} {t = t} {T = T} rc (U′ {j}) record { t∶T = t∶T ; T≈ = T≈ ; A∈𝕌 = A∈𝕌 ; rel = rel } 
        rewrite Glu-wf-gen j (U≤′) = record 
          { t∶T = t∶T 
          ; A≈B = U′ 
          ; T∼A = T≈ 
          ; a∈⊤ = λ n → let W , ↘W , ↘W′ = 𝕌⊆TopT A∈𝕌 n in W , (RU _ ↘W refl) , RU _ ↘W′ refl 
          ; krip = λ ⊢σ → helper ⊢σ 
          }
        where helper : ∀ {Δ} →
                       Δ ⊢w σ ∶ Γ →
                       ---------------
                       Δ ⊢ t [ σ ] ≈ Nf⇒Exp (proj₁ (𝕌⊆TopT A∈𝕌 (len Δ))) ∶[ ℕ.suc j ] T [ σ ]
              helper {Δ = Δ} ⊢σ
                with W′ , ↘W′ , _ ← 𝕌⊆TopT A∈𝕌 (len Δ)
                   | W , ↘W , W≈ ← rc (≤-reflexive refl) A∈𝕌 rel ⊢σ -- well-founded induction
                rewrite Rty-det ↘W ↘W′ = ≈-conv W≈ (≈-trans (≈-sym (Se-[] _ (⊢w⇒⊢s ⊢σ))) ([]-cong-Se′ (≈-sym T≈) (⊢w⇒⊢s ⊢σ)))
      ®El⇒®↑El {Π j A (S ↙ k) ρ} {Γ = Γ} {t = t} {T = T} rc (Π′ {j} {k} jA RT) t® 
        rewrite 𝕌-wf-gen j (ΠI≤′ j k refl)
              | 𝕌-wf-gen k (ΠO≤′ j k refl)
              | Glu-wf-gen j (ΠI≤′ j k refl)
              | Glu-wf-gen k (ΠO≤′ j k refl) = record 
            { t∶T = t∶T 
            ; A≈B = proj₁ Π-bund 
            ; T∼A = ®El⇒® (proj₁ Π-bund) (®El-Π-𝕌 refl jA RT (proj₁ Π-bund) t®) 
            ; a∈⊤ = a∈⊤
            ; krip = λ {Δ} {σ} ⊢σ →
                    let W , ↘W , _ = a∈⊤ (len Δ)
                    in subst (_ ⊢ _ ≈_∶[ _ ] _) (cong Nf⇒Exp (Rf-det ↘W (proj₁ (proj₂ (a∈⊤ (len Δ))))))
                          (helper ⊢σ jA RT krip ↘W )            
            }
        where
          open GluΛ t®
          Π-bund = Π-bundle jA (λ a≈a′ → RT a≈a′ , a∈El a≈a′) refl
          a∈⊤ = El⊆Top (proj₁ Π-bund) (proj₂ Π-bund)
          helper :  Δ ⊢w σ ∶ Γ →
                    (jA : A ≈ A′ ∈ 𝕌 j) →
                    (RT : ∀ {a a′} → a ≈ a′ ∈ El j jA → ΠRT S (ρ ↦ a) T′ (ρ′ ↦ a′) (𝕌 k) ) →
                    (∀ {Δ σ} → Δ ⊢w σ ∶ Γ → ΛRel j Δ t IT OT σ a (𝕌-wellfounded j) jA
                      (_⊢_®[ j ] jA)
                      (_⊢_∶_®[ j ]_∈El jA)
                      (λ a∈ Δ′ s S b → Δ′ ⊢ s ∶ S ®[ k ] b ∈El ΠRT.T≈T′ (RT a∈))) →
                    Rf L.foldr (λ _ → ℕ.suc) 0 Δ - ↓ (max j k) (Π j A (S ↙ k) ρ) a ↘ W →
                    --------------------------
                    Δ ⊢ t [ σ ] ≈ Nf⇒Exp W ∶[ max j k ] T [ σ ]
          helper {Δ = Δ} {σ = σ} {W = Λ (W ↙ _) w} ⊢σ jA RT krip (RΛ .(len Δ) ↘W ↘a ↘⟦S⟧ ↘w _) = helper₁
            where 
              ⊢σ′   = ⊢w⇒⊢s ⊢σ
              Tσ≈   = ≈-trans ([]-cong-Se′ T≈ ⊢σ′) (Π-[] ⊢σ′ ⊢IT ⊢OT refl)
              ⊢tσ   = conv (t[σ] t∶T ⊢σ′) Tσ≈
              ⊢Δ    = proj₁ (presup-s ⊢σ′)
              ⊢Γ    = proj₂ (presup-s ⊢σ′)
              ⊢ITσ  = t[σ]-Se ⊢IT ⊢σ′
              ⊢ITσΔ = ⊢∷ ⊢Δ (t[σ]-Se ⊢IT ⊢σ′)
              ⊢qσ   = ⊢q ⊢Δ ⊢σ′ ⊢IT
              ⊢OTqσ = t[σ]-Se ⊢OT ⊢qσ
              ⊢σwk  = s-∘ (s-wk ⊢ITσΔ) ⊢σ′
              open ΛRel (krip ⊢σ) using (IT-rel)
              open ΛRel (krip (⊢w-∘ ⊢σ (⊢wwk ⊢ITσΔ))) using (ap-rel)
              open ER
              helper₁ : Δ ⊢ t [ σ ] ≈ Λ (Nf⇒Exp W ↙ j) (Nf⇒Exp w) ∶[ max j k ] T [ σ ]
              helper₁ with WI , ↘WI , ≈WI ← ®⇒Rty-eq (λ l<j → rc (ΠI≤ refl l<j))jA IT-rel (⊢wI ⊢Δ)
                      with v∼l ← ®↓El⇒®El (λ l<j → rc (ΠI≤ refl l<j)) jA (v0∼x jA IT-rel)
                      with record { ⟦T⟧ = ⟦T⟧ ; ↘⟦T⟧ = ↘⟦T⟧ ; T≈T′ = T≈T′ } ← RT (®El⇒∈El jA v∼l)
                          | record { fa = fa ; ↘fa = ↘fa ; ®fa = ®fa } ← ap-rel (®El-resp-T≈ jA v∼l ([∘]-Se ⊢IT ⊢σ′ (s-wk ⊢ITσΔ))) (®El⇒∈El jA v∼l)
                      with record { a∈⊤ = a∈⊤ ; krip = krip′ } ← ®El⇒®↑El (λ l<k → rc (ΠO≤ refl l<k)) T≈T′ ®fa
                      with w′ , ↘w′ , _ ← a∈⊤ (length (((IT [ σ ]) ↙ j) ∷ Δ))
                        | equiv ← krip′ (⊢wI ⊢ITσΔ)
                      rewrite ap-det ↘a ↘fa
                            | ⟦⟧-det ↘⟦S⟧ ↘⟦T⟧
                            | Rf-det ↘w′ ↘w
                            | Rty-det ↘WI ↘W
                          = ≈-conv
                              ( begin
                                  t [ σ ] ≈⟨ Λ-η ⊢ITσ ⊢OTqσ ⊢tσ refl ⟩
                                  Λ (IT [ σ ] ↙ j) (t [ σ ] [ wk ] $ v 0) ≈⟨ Λ-cong ⊢ITσ (≈-refl ⊢ITσ)
                                                                                  (≈-conv ($-cong (t[σ]-Se ⊢ITσ (s-wk ⊢ITσΔ)) ⊢OT[q]
                                                                                                          (≈-conv (≈-sym ([∘] (s-wk ⊢ITσΔ) ⊢σ′ t∶T)) eq)
                                                                                                          (v-≈ ⊢ITσΔ here) refl) eq‴ ) refl ⟩
                                  Λ (IT [ σ ] ↙ j) (t [ σ ∘ wk ] $ v 0) ≈˘⟨ Λ-cong ⊢ITσ (≈-refl ⊢ITσ) ([I] (conv (Λ-E ⊢IT[σ][wk] ⊢OT[q] (conv (t[σ] t∶T ⊢σwk) eq) (vlookup ⊢ITσΔ here) refl) eq‴ )) refl ⟩
                                  Λ (IT [ σ ] ↙ j) ((t [ σ ∘ wk ] $ v 0) [ I ]) ≈⟨ ≈-conv (Λ-cong ⊢ITσ (≈-trans (≈-sym ([I] ⊢ITσ)) ≈WI) equiv refl) (Π-cong ⊢ITσ (≈-refl ⊢ITσ) ([I] ⊢OTqσ) refl) ⟩
                                  Λ (Nf⇒Exp W ↙ j) (Nf⇒Exp w)
                                ∎
                              )
                              (≈-sym Tσ≈)
                      where ITσwk≈ = [∘]-Se ⊢IT ⊢σ′ (s-wk ⊢ITσΔ)
                            ⊢IT[σ][wk] = proj₁ (proj₂ (presup-≈ ITσwk≈))
                            ⊢IT[σ∘wk] = proj₁ (proj₂ (proj₂ (presup-≈ ITσwk≈)))
                            eq = begin
                                    T [ σ ∘ wk ] ≈⟨ []-cong-Se′ T≈ ⊢σwk ⟩
                                    Π (IT ↙ j) (OT ↙ k) [ σ ∘ wk ] ≈⟨ Π-[] ⊢σwk ⊢IT ⊢OT refl ⟩
                                    Π (IT [ σ ∘ wk ] ↙ j) (OT [ q (IT ↙ j) (σ ∘ wk) ] ↙ k) ≈⟨ Π-cong ⊢IT[σ∘wk] (≈-sym ITσwk≈) (≈-refl (t[σ]-Se ⊢OT (⊢q ⊢ITσΔ ⊢σwk ⊢IT))) refl ⟩
                                    Π (IT [ σ ] [ wk ] ↙ j) (OT [ q (IT ↙ j) (σ ∘ wk) ] ↙ k)
                                  ∎
                            eq″ = ctxeq-s (∷-cong (⊢≈-refl ⊢ITσΔ) ⊢IT[σ∘wk] ⊢IT[σ][wk] (≈-sym ITσwk≈) (≈-sym ITσwk≈)) (⊢q ⊢ITσΔ ⊢σwk ⊢IT)
                            ⊢OT[q] = t[σ]-Se ⊢OT eq″
                            eq‴ = begin
                                    OT [ q (IT ↙ j) (σ ∘ wk) ] [| v 0 ∶ IT [ σ ] [ wk ] ↙ j ] ≈⟨ []-cong-Se (≈-refl ⊢OT[q])
                                                                                                              (s-, (s-I ⊢ITσΔ) ⊢IT[σ][wk] (conv (vlookup ⊢ITσΔ here) (≈-sym ([I] ⊢IT[σ][wk]))))
                                                                                                              (,-cong (s-≈-refl (s-I ⊢ITσΔ)) ⊢IT[σ][wk] ITσwk≈ (≈-refl (conv (vlookup ⊢ITσΔ here) (≈-sym ([I] ⊢IT[σ][wk]))))) ⟩
                                    OT [ q (IT ↙ j) (σ ∘ wk) ] [| v 0 ∶ IT [ σ ∘ wk ] ↙ j ] ≈⟨ ≈-sym ([]-q-∘-,′ ⊢OT ⊢σwk (conv (vlookup ⊢ITσΔ here) ITσwk≈)) ⟩
                                    OT [ (σ ∘ wk) , v 0 ∶ IT ↙ j ]
                                  ∎
      ®El⇒®↑El {Γ = Γ} {t = t} {T = T} {a = a} rc (L′ {j} {k} kA) t®
        rewrite 𝕌-wf-gen k (Li≤′ j k refl)
              | Glu-wf-gen k (Li≤′ j k refl) = record 
            { t∶T = t∶T 
            ; A≈B = proj₁ L-bund 
            ; T∼A = ®El⇒® (proj₁ L-bund) (®El-Li-𝕌 refl kA (proj₁ L-bund) t®) 
            ; a∈⊤ = a∈⊤
            ; krip = λ {Δ} {σ} ⊢σ → let open lKripke (krip ⊢σ) in helper ⊢σ kA a∈El ↘ua ®ua a∈⊤   
            }
            where 
              open Glul t®
              L-bund = L-bundle {j = j} kA a∈El refl
              a∈⊤ = El⊆Top (proj₁ L-bund) (proj₂ L-bund) 
              helper : ∀ {ua : D} →
                         Δ ⊢w σ ∶ Γ →
                         (kA : A ≈ A′ ∈ 𝕌 k) →
                         (a∈El : a ∈′ Unli (El k kA)) →
                         (↘ua : unli∙ a ↘ ua) →
                         Δ ⊢ (unlift t) [ σ ] ∶ UT [ σ ] ®[ k ] ua ∈El kA →
                         (a∈⊤ : ↓ ( j + k) (Li j k A) a ≈ ↓ (j + k) (Li j k A′) a ∈ Top) →
                         -----------------
                         Δ ⊢ t [ σ ] ≈ Nf⇒Exp (proj₁ (a∈⊤ (L.length Δ))) ∶[ j + k ] T [ σ ]
              helper {Δ = Δ} ⊢σ kA a∈El ↘ua t® a∈⊤
                with ⊢Δ , _ ← presup-s (⊢w⇒⊢s ⊢σ)
                with record { t∶T = ut∶UT ; T∼A = UT∼A ; a∈⊤ = ua∈⊤ ; krip = ukrip } ← ®El⇒®↑El (λ l<k → rc (Li≤ refl l<k)) kA t®
                with WU , ↘WU , _ ← (ua∈⊤ (len Δ))
                    | liftt _ WU′ , Rli .(len Δ) unli∙↘ ↘WU′ j+k≡ , _ ← (a∈⊤ (len Δ))
                with unlit≈WU ← ukrip (⊢wI ⊢Δ)
                rewrite Rf-det (proj₁ (proj₂( ua∈⊤ (len Δ)))) ↘WU | unli-det unli∙↘ ↘ua | Rf-det ↘WU′ ↘WU
                  = ≈-conv (≈-trans (L-η j (proj₂ (presup-tm ut∶UT)) (conv (t[σ] t∶T ⊢σ′) (≈-trans ([]-cong-Se′ T≈ ⊢σ′) (Liftt-[] _ ⊢σ′ ⊢UT))))
                                    (liftt-cong j (≈-trans (≈-trans (≈-sym (unlift-[] j ⊢UT ⊢σ′ (conv t∶T T≈))) (≈-sym ([I] ut∶UT))) (≈-conv unlit≈WU ([I] (t[σ]-Se ⊢UT ⊢σ′))))))
                           (≈-trans (≈-sym (Liftt-[] _ ⊢σ′ ⊢UT)) ([]-cong-Se′ (≈-sym T≈) ⊢σ′))
                where ⊢σ′ = ⊢w⇒⊢s ⊢σ

      ®⇒Rty-eq : ∀ {i} → (rc : ∀ {j} → j < i → ∀ {A B Γ T Δ σ} (A≈B : A ≈ B ∈ 𝕌 j) → Γ ⊢ T ®[ j ] A≈B → Δ ⊢w σ ∶ Γ → ∃ λ W → Rty len Δ - A at j ↘ W × Δ ⊢ T [ σ ] ≈ Nf⇒Exp W ∶[ 1 + j ] Se j) →
                 (A≈B : A ≈ B ∈ 𝕌 i) → Γ ⊢ T ®[ i ] A≈B → Δ ⊢w σ ∶ Γ → ∃ λ W → Rty len Δ - A at i ↘ W × Δ ⊢ T [ σ ] ≈ Nf⇒Exp W ∶[ 1 + i ] Se i
      ®⇒Rty-eq {Δ = Δ} rc (ne′ C≈C′) (⊢T , rel) ⊢σ
        with C≈C′ (len Δ) | rel ⊢σ
      ...  | V , ↘V , _ | r = (ne V) , (Rne (len Δ) ↘V refl) , r
      ®⇒Rty-eq rc N′ T® ⊢σ = N , (RN _) , ≈-trans ([]-cong-Se′ T® (⊢w⇒⊢s ⊢σ)) (N-[] (⊢w⇒⊢s ⊢σ))
      ®⇒Rty-eq rc (U {j} i≡1+j j≡j′) T® ⊢σ 
        rewrite i≡1+j = Se j , (RU _ refl) , ≈-trans ([]-cong-Se′ T® (⊢w⇒⊢s ⊢σ)) (Se-[] _ (⊢w⇒⊢s ⊢σ))
      ®⇒Rty-eq {Π j A (S ↙ k) ρ} {_} {_} {T} {Δ} {σ} rc (Π′ {j} {k} jA RT) record { IT = IT ; OT = OT ; ⊢IT = ⊢IT ; ⊢OT = ⊢OT ; T≈ = T≈ ; krip = krip } ⊢σ
        rewrite 𝕌-wf-gen j (ΠI≤′ j k refl) 
              | 𝕌-wf-gen k (ΠO≤′ j k refl)
              | Glu-wf-gen j (ΠI≤′ j k refl) 
              | Glu-wf-gen k (ΠO≤′ j k refl) 
              with ⊢Δ , ⊢Γ ← presup-s (⊢w⇒⊢s ⊢σ) = helper
          where
            open ER
            ⊢σ′   = ⊢w⇒⊢s ⊢σ
            ⊢ITσ  = t[σ]-Se ⊢IT ⊢σ′
            ⊢ITσΔ = ⊢∷ ⊢Δ (t[σ]-Se ⊢IT ⊢σ′)
            ⊢qσ   = ⊢q ⊢Δ ⊢σ′ ⊢IT
            ⊢OTqσ = t[σ]-Se ⊢OT ⊢qσ
            open ΠRel (krip ⊢σ) using (IT-rel)
            open ΠRel (krip (⊢w-∘ ⊢σ (⊢wwk ⊢ITσΔ))) using (OT-rel)
            helper : ∃ λ W → Rty len Δ - Π j A (S ↙ k) ρ at (max j k) ↘ W × Δ ⊢ T [ σ ] ≈ Nf⇒Exp W ∶[ 1 + max j k ] Se (max j k)
            helper with WI , ↘WI , ≈WI ← ®⇒Rty-eq (λ l<j → rc (ΠI≤ refl l<j)) jA IT-rel (⊢wI ⊢Δ)
                   with v0®l ← ®↓El⇒®El (λ l<j → rc (ΠI≤ refl l<j)) jA (v0∼x jA IT-rel)
                   with rel ← OT-rel (®El-resp-T≈ jA v0®l ([∘]-Se ⊢IT ⊢σ′ (s-wk ⊢ITσΔ))) (®El⇒∈El jA v0®l)
                   with record { ⟦T⟧ = ⟦S⟧ ; ↘⟦T⟧ = ↘⟦S⟧ ; T≈T′ = T≈T′ } ← RT (®El⇒∈El jA v0®l)
                   with WO , ↘WO , ≈WO ← ®⇒Rty-eq (λ l<k → rc (ΠO≤ refl l<k)) T≈T′ rel (⊢wI ⊢ITσΔ) =
                        ( Π (WI ↙ j) (WO ↙ k)
                        , (RΠ _ ↘WI ↘⟦S⟧ ↘WO refl)
                        , (begin
                              T [ σ ] ≈⟨ []-cong-Se′ T≈ ⊢σ′ ⟩
                              Π (IT ↙ j) (OT ↙ k) [ σ ] ≈⟨ Π-[] ⊢σ′ ⊢IT ⊢OT refl ⟩
                              Π ((IT ↙ j) [ σ ]) (OT [ q (IT ↙ j) σ ] ↙ k) ≈⟨ Π-cong ⊢ITσ (≈-sym ([I] ⊢ITσ)) (≈-sym ([I] ⊢OTqσ)) refl ⟩
                              Π ((IT ↙ j) [ σ ] [ I ]) (OT [ q (IT ↙ j) σ ] [ I ] ↙ k) ≈⟨ Π-cong (proj₁ (proj₂ (presup-≈ ≈WI))) ≈WI (ctxeq-≈ (∷-cong (⊢≈-refl ⊢Δ) ⊢ITσ (proj₁ (proj₂ (presup-≈ ≈WI))) (≈-sym ([I] ⊢ITσ)) (≈-sym ([I] ⊢ITσ))) ≈WO) refl ⟩
                              Nf⇒Exp (Π (WI ↙ j) (WO ↙ k))
                            ∎)
                        )
      ®⇒Rty-eq {Δ = Δ} rc (L′ {j = j} {k = k} kA) record { UT = UT ; ⊢UT = ⊢UT ; T≈ = T≈ ; krip = krip } ⊢σ
        rewrite 𝕌-wf-gen k (Li≤′ j k refl)
              | Glu-wf-gen k (Li≤′ j k refl) 
        with ⊢Δ , ⊢Γ ← presup-s (⊢w⇒⊢s ⊢σ)
        with W , ↘W , ≈W ← ®⇒Rty-eq (λ l<k → rc (Li≤ refl l<k)) kA (krip ⊢σ) (r-I (I-≈ ⊢Δ)) =
            ( Liftt j (W ↙ k)
            , RL _ ↘W refl
            , ≈-trans ([]-cong-Se′ T≈ ⊢σ′) (≈-trans (Liftt-[] _ ⊢σ′ ⊢UT) (Liftt-cong _ (≈-trans (≈-sym ([I] (t[σ]-Se ⊢UT ⊢σ′))) ≈W)))
            )
        where ⊢σ′ = ⊢w⇒⊢s ⊢σ

-- Wrap up the well-founded induction.
®⇒Rty-eq : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
           Γ ⊢ T ®[ i ] A≈B →
           Δ ⊢w σ ∶ Γ →
           ----------------------------------
           ∃ λ W → Rty len Δ - A at i ↘ W × Δ ⊢ T [ σ ] ≈ Nf⇒Exp W ∶[ 1 + i ] Se i
®⇒Rty-eq {i = i} = <-Measure.wfRec (λ i → ∀ {A B Γ T Δ σ} →
                                           (A≈B : A ≈ B ∈ 𝕌 i) →
                                          Γ ⊢ T ®[ i ] A≈B →
                                          Δ ⊢w σ ∶ Γ →
                                          ∃ λ W → Rty len Δ - A at i ↘ W × Δ ⊢ T [ σ ] ≈ Nf⇒Exp W ∶[ 1 + i ] Se i)
                                    (λ _ rc A≈B T® ⊢σ → Real.®⇒Rty-eq rc A≈B T® ⊢σ) i

®↓El⇒®El : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
           Γ ⊢ t ∶ T ®↓[ i ] c ∈El A≈B →
           -------------------------------
           Γ ⊢ t ∶ T ®[ i ] ↑ i A c ∈El A≈B
®↓El⇒®El {i = i} = Real.®↓El⇒®El (λ _ → ®⇒Rty-eq)


®El⇒®↑El : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
           Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
           -----------------------------
           Γ ⊢ t ∶ T ®↑[ i ] a ∈El A ≈ B
®El⇒®↑El {i = i} = Real.®El⇒®↑El (λ _ → ®⇒Rty-eq)

-- From what we have, we are ready for concluding ® ⊆ ®↑ for types.
®⇒®↑ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
       Γ ⊢ T ®[ i ] A≈B →
       --------------------
       Γ ⊢ T ®↑[ i ] A ≈ B
®⇒®↑ A≈B T∼A = record
  { t∶T  = ®⇒ty A≈B T∼A
  ; A∈⊤  = 𝕌⊆TopT A≈B
  ; krip = λ {Δ} {σ} ⊢σ → let W , ↘W , Tσ≈ = ®⇒Rty-eq A≈B T∼A ⊢σ
                          in subst (λ t → _ ⊢ _ [ _ ] ≈ Nf⇒Exp t ∶[ _ ] Se _)
                                   (Rty-det ↘W (proj₁ (proj₂ (𝕌⊆TopT A≈B (len Δ)))))
                                   Tσ≈
  }

v0®x : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
       Γ ⊢ T ®[ i ] A≈B →
       (T ↙ i)∷ Γ ⊢ v 0 ∶ T [ wk ] ®[ i ] ↑ i A (l (len Γ)) ∈El A≈B
v0®x A≈B T∼A = ®↓El⇒®El A≈B (v0∼x A≈B T∼A)

-- As a corollary, if two types are related to the same semantic types, then both
-- types are equivalent.
®⇒≈ : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
      Γ ⊢ T ®[ i ] A≈B →
      Γ ⊢ T′ ®[ i ] A≈B →
      ----------------------------
      Γ ⊢ T ≈ T′ ∶[ 1 + i ] Se i
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
        Γ ⊢ t ≈ t′ ∶[ i ] T
®El⇒≈ {_} {_} {Γ} {t} {_} {_} {t′} A≈B t∼a t′∼a
  with presup-tm (®El⇒ty A≈B t∼a)
...  | ⊢Γ , _
     with ®El⇒®↑El A≈B t∼a | ®El⇒®↑El A≈B t′∼a
...     | record { a∈⊤ = t∈⊤ ; krip = tkrip }
        | record { a∈⊤ = t′∈⊤ ; krip = t′krip }
        with t∈⊤ (len Γ) | tkrip (⊢wI ⊢Γ)
           | t′∈⊤ (len Γ) | t′krip (⊢wI ⊢Γ)
...        | w  , ↘w  , _ | ≈w
           | w′ , ↘w′ , _ | ≈w′
           rewrite Rf-det ↘w′ ↘w = ≈-trans ([I]-≈ˡ ≈w) (≈-sym ([I]-≈ˡ ≈w′))

®El⇒≈-gen : ∀ {i} (A≈B : A ≈ B ∈ 𝕌 i) →
            Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B →
            Γ ⊢ t′ ∶ T′ ®[ i ] a ∈El A≈B →
            ----------------------------
            Γ ⊢ t ≈ t′ ∶[ i ] T
®El⇒≈-gen A≈B t∼a t′∼a = ®El⇒≈ A≈B t∼a (®El-resp-T≈ A≈B t′∼a (®⇒≈ A≈B (®El⇒® A≈B t′∼a) (®El⇒® A≈B t∼a)))