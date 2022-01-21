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

-- var-arith′ : ∀ Γ″ (T : Typ) Γ′ → len (Γ″ ++ T ∷ Γ′) ∸ len Γ″ ∸ 1 ≡ len Γ′
-- var-arith′ Γ″ T Γ′ = begin
--   len (Γ″ ++ T ∷ Γ′) ∸ len Γ″ ∸ 1
--     ≡⟨ cong (λ n → n ∸ len Γ″ ∸ 1) (Lₚ.length-++ Γ″) ⟩
--   len Γ″ + suc (len Γ′) ∸ len Γ″ ∸ 1
--     ≡⟨ cong (_∸ 1) (m+n∸m≡n (len Γ″) (suc (len Γ′))) ⟩
--   len Γ′
--     ∎
--   where open ≡-Reasoning


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
  ; c∈El = {!!} -- need realizability of the semantics
  ; krip = λ {Δ} {σ} ⊢σ → v (len (head Δ) ∸ len (head Γ) ∸ 1)
                        , Rl (map (len) Δ) (len (head Γ))
                        , v0∼x-gen [] ⊢σ refl
  }
  where ⊢TΓ = ⊢∷ ⊢Γ ⊢T
