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
      ®↓El⇒®El {□ A} {c = c} (□ A≈B) t∼c = record
        { GT   = GT
        ; t∶T  = t∶T
        ; a∈El = {!!}
        ; T≈   = T≈
        ; krip = λ {_} {σ} Ψs ⊢σ →
          let ⊢σ′ = ⊢r⇒⊢s ⊢σ
              ⊢GT = proj₂ (®□⇒wf A≈B T∼A)
              Gk  = G.krip Ψs ⊢σ
          in record
          { ua  = unbox′ (A [ ins (mt σ) 1 ] [ ins vone (len Ψs) ]) (len Ψs) (c [ mt σ ])
          ; ↘ua = unbox∙ (len Ψs)
          ; rel = ®El-≡ {!!} (A≈B (ins (mt σ) (len Ψs)))
                        (®El-resp-T≈ {!!}
                                     (®↓El⇒®El {!!} (record
                                       { t∶T  = □-E Ψs (conv (t[σ] t∶T ⊢σ′) (≈-trans (lift-⊢≈-Se-max ([]-cong-Se′ (proj₂ T≈) ⊢σ′)) (□-[] ⊢σ′ (lift-⊢-Se-max′ ⊢GT))))
                                                    {!!}
                                                    refl
                                       ; T∼A  = {!Gk!}
                                       ; c∈⊥  = {!!}
                                       ; krip = {!!}
                                       }))
                                     {!!})
                        {!!}
          }
        }
        where module ↓ = _⊢_∶_®↓[_]_∈El_ t∼c
              open ↓
              module G = Glu□ T∼A
              open G
      ®↓El⇒®El (Π iA RT) t∼c  = {!!}
        where open _⊢_∶_®↓[_]_∈El_ t∼c

      ®El⇒®↑El : (A≈B : A ≈ B ∈ 𝕌 i) → Γ ⊢ t ∶ T ®[ i ] a ∈El A≈B → Γ ⊢ t ∶ T ®↑[ i ] a ∈El A≈B
      ®El⇒®↑El (ne C≈C′) t∼a  = {!!}
      ®El⇒®↑El N t∼a          = {!!}
      ®El⇒®↑El (U j<i eq) t∼a = {!!}
      ®El⇒®↑El (□ A≈B) t∼a    = {!!}
      ®El⇒®↑El (Π iA RT) t∼a  = {!!}

      ®⇒Rty-eq : (A≈B : A ≈ B ∈ 𝕌 i) → Γ ⊢ T ®[ i ] A≈B → Δ ⊢r σ ∶ Γ → ∃ λ W → Rty map len Δ - A [ mt σ ] ↘ W × Δ ⊢ T [ σ ] ≈ Nf⇒Exp W
      ®⇒Rty-eq (ne C≈C′) T∼A ⊢σ  = {!!}
      ®⇒Rty-eq N T∼A ⊢σ          = {!!}
      ®⇒Rty-eq (U j<i eq) T∼A ⊢σ = {!!}
      ®⇒Rty-eq (□ A≈B) T∼A ⊢σ    = {!!}
      ®⇒Rty-eq (Π iA RT) T∼A ⊢σ  = {!!}
