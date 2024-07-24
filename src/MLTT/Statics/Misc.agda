{-# OPTIONS --without-K --safe #-}

-- Some miscellaneous properties
module MLTT.Statics.Misc where

open import Lib
open import Data.Nat
import Data.Nat.Properties as ℕₚ
import Data.List.Properties as Lₚ

open import MLTT.Statics.Full

lift-⊢-Se-step : ∀ {i} j →
                 Γ ⊢ T ∶ Se i →
                 Γ ⊢ T ∶ Se (j + i)
lift-⊢-Se-step zero ⊢T = ⊢T
lift-⊢-Se-step (suc j) ⊢T = cumu (lift-⊢-Se-step j ⊢T)

lift-⊢-Se : ∀ {i j} →
            Γ ⊢ T ∶ Se i →
            i ≤ j →
            Γ ⊢ T ∶ Se j
lift-⊢-Se ⊢T i≤j
  rewrite sym (trans (ℕₚ.+-comm (≤-diff i≤j) _) (≤-diff-+ i≤j)) = lift-⊢-Se-step _ ⊢T

lift-⊢-Se-max : ∀ {i j} → Γ ⊢ T ∶ Se i → Γ ⊢ T ∶ Se (i ⊔ j)
lift-⊢-Se-max ⊢T = lift-⊢-Se ⊢T (ℕₚ.m≤m⊔n _ _)

lift-⊢-Se-max′ : ∀ {i j} → Γ ⊢ T ∶ Se i → Γ ⊢ T ∶ Se (j ⊔ i)
lift-⊢-Se-max′ ⊢T = lift-⊢-Se ⊢T (ℕₚ.m≤n⊔m _ _)

lift-⊢≈-Se-step : ∀ {i} j →
                  Γ ⊢ T ≈ T′ ∶ Se i →
                  Γ ⊢ T ≈ T′ ∶ Se (j + i)
lift-⊢≈-Se-step zero T≈T′    = T≈T′
lift-⊢≈-Se-step (suc j) T≈T′ = ≈-cumu (lift-⊢≈-Se-step j T≈T′)

lift-⊢≈-Se : ∀ {i j} →
             Γ ⊢ T ≈ T′ ∶ Se i →
             i ≤ j →
             Γ ⊢ T ≈ T′ ∶ Se j
lift-⊢≈-Se T≈T′ i≤j
  rewrite sym (trans (ℕₚ.+-comm (≤-diff i≤j) _) (≤-diff-+ i≤j)) = lift-⊢≈-Se-step _ T≈T′

lift-⊢≈-Se-max : ∀ {i j} → Γ ⊢ T ≈ T′ ∶ Se i → Γ ⊢ T ≈ T′ ∶ Se (i ⊔ j)
lift-⊢≈-Se-max T≈T′ = lift-⊢≈-Se T≈T′ (ℕₚ.m≤m⊔n _ _)

lift-⊢≈-Se-max′ : ∀ {i j} → Γ ⊢ T ≈ T′ ∶ Se i → Γ ⊢ T ≈ T′ ∶ Se (j ⊔ i)
lift-⊢≈-Se-max′ T≈T′ = lift-⊢≈-Se T≈T′ (ℕₚ.m≤n⊔m _ _)

t[σ]-Se : ∀ {i} → Δ ⊢ T ∶ Se i → Γ ⊢s σ ∶ Δ → Γ ⊢ T [ σ ] ∶ Se i
t[σ]-Se ⊢T ⊢σ = conv (t[σ] ⊢T ⊢σ) (Se-[] _ ⊢σ)

[]-cong-Se : ∀ {i} → Δ ⊢ T ≈ T′ ∶ Se i → Γ ⊢s σ ∶ Δ → Γ ⊢s σ ≈ σ′ ∶ Δ → Γ ⊢ T [ σ ] ≈ T′ [ σ′ ] ∶ Se i
[]-cong-Se T≈T′ ⊢σ σ≈σ′ = ≈-conv ([]-cong T≈T′ σ≈σ′) (Se-[] _ ⊢σ)

[]-cong-Se′ : ∀ {i} → Δ ⊢ T ≈ T′ ∶ Se i → Γ ⊢s σ ∶ Δ → Γ ⊢ T [ σ ] ≈ T′ [ σ ] ∶ Se i
[]-cong-Se′ T≈T′ ⊢σ = []-cong-Se T≈T′ ⊢σ (s-≈-trans (s-≈-sym (I-∘ ⊢σ)) (I-∘ ⊢σ))

[]-cong-Se″ : ∀ {i} → Δ ⊢ T ∶ Se i → Γ ⊢s σ ∶ Δ → Γ ⊢s σ ≈ σ′ ∶ Δ → Γ ⊢ T [ σ ] ≈ T [ σ′ ] ∶ Se i
[]-cong-Se″ ⊢T ⊢σ σ≈σ′ = []-cong-Se (≈-trans (≈-sym ([I] ⊢T)) ([I] ⊢T)) ⊢σ σ≈σ′

[∘]-Se : ∀ {i} → Δ ⊢ T ∶ Se i → Γ ⊢s σ ∶ Δ → Γ′ ⊢s τ ∶ Γ → Γ′ ⊢ T [ σ ] [ τ ] ≈ T [ σ ∘ τ ] ∶ Se i
[∘]-Se ⊢T ⊢σ ⊢τ = ≈-conv (≈-sym ([∘] ⊢τ ⊢σ ⊢T)) (Se-[] _ (s-∘ ⊢τ ⊢σ))

t[σ]-N : Δ ⊢ t ∶ N → Γ ⊢s σ ∶ Δ → Γ ⊢ t [ σ ] ∶ N
t[σ]-N ⊢t ⊢σ = conv (t[σ] ⊢t ⊢σ) (N-[] 0 ⊢σ)

[]-cong-N : Δ ⊢ t ≈ t′ ∶ N → Γ ⊢s σ ∶ Δ → Γ ⊢s σ ≈ σ′ ∶ Δ → Γ ⊢ t [ σ ] ≈ t′ [ σ′ ] ∶ N
[]-cong-N t≈t′ ⊢σ σ≈σ′ = ≈-conv ([]-cong t≈t′ σ≈σ′) (N-[] 0 ⊢σ)

[]-cong-N′ : Δ ⊢ t ≈ t′ ∶ N → Γ ⊢s σ ∶ Δ → Γ ⊢ t [ σ ] ≈ t′ [ σ ] ∶ N
[]-cong-N′ t≈t′ ⊢σ = []-cong-N t≈t′ ⊢σ (s-≈-trans (s-≈-sym (I-∘ ⊢σ)) (I-∘ ⊢σ))

[]-cong-N″ : Δ ⊢ t ∶ N → Γ ⊢s σ ∶ Δ → Γ ⊢s σ ≈ σ′ ∶ Δ → Γ ⊢ t [ σ ] ≈ t [ σ′ ] ∶ N
[]-cong-N″ ⊢t ⊢σ σ≈σ′ = []-cong-N (≈-trans (≈-sym ([I] ⊢t)) ([I] ⊢t)) ⊢σ σ≈σ′

conv-N-[] : Γ ⊢ t ∶ N [ σ ] → Γ ⊢s σ ∶ Δ → Γ ⊢ t ∶ N
conv-N-[] ⊢t ⊢σ = conv ⊢t (N-[] 0 ⊢σ)

conv-N-[]-sym : Γ ⊢ t ∶ N → Γ ⊢s σ ∶ Δ → Γ ⊢ t ∶ N [ σ ]
conv-N-[]-sym ⊢t ⊢σ = conv ⊢t (≈-sym (N-[] 0 ⊢σ))

≈-conv-N-[] : Γ ⊢ t ≈ t′ ∶ N [ σ ] → Γ ⊢s σ ∶ Δ → Γ ⊢ t ≈ t′ ∶ N
≈-conv-N-[] t≈t′ ⊢σ = ≈-conv t≈t′ (N-[] 0 ⊢σ)

≈-conv-N-[]-sym : Γ ⊢ t ≈ t′ ∶ N → Γ ⊢s σ ∶ Δ → Γ ⊢ t ≈ t′ ∶ N [ σ ]
≈-conv-N-[]-sym t≈t′ ⊢σ = ≈-conv t≈t′ (≈-sym (N-[] 0 ⊢σ))

Se[wk]≈Se : ∀ {i} →
            ⊢ T ∷ Γ →
            T ∷ Γ ⊢ Se i [ wk ] ≈ Se i ∶ Se (suc i)
Se[wk]≈Se ⊢TΓ = Se-[] _ (s-wk ⊢TΓ)

N[wk]≈N : ∀ i →
          ⊢ T ∷ Γ →
          T ∷ Γ ⊢ N [ wk ] ≈ N ∶ Se i
N[wk]≈N _ ⊢TΓ = N-[] _ (s-wk ⊢TΓ)

N-[][] : ∀ i →
        Γ′ ⊢s σ ∶ Γ″ →
        Γ ⊢s τ ∶ Γ′ →
        Γ ⊢ N [ σ ] [ τ ] ≈ N ∶ Se i
N-[][] _ ⊢σ ⊢τ = ≈-trans ([]-cong-Se′ (N-[] _ ⊢σ) ⊢τ) (N-[] _ ⊢τ)

N[wk][wk]≈N : ∀ i →
              ⊢ S ∷ T ∷ Γ →
              S ∷ T ∷ Γ ⊢ N [ wk ] [ wk ] ≈ N ∶ Se i
N[wk][wk]≈N _ ⊢STΓ@(⊢∷ ⊢TΓ _) = N-[][] _ (s-wk ⊢TΓ) (s-wk ⊢STΓ)

N[σ]≈N[τ] : ∀ i →
            Γ ⊢s σ ∶ Δ →
            Γ ⊢s τ ∶ Δ′ →
            Γ ⊢ N [ σ ] ≈ N [ τ ] ∶ Se i
N[σ]≈N[τ] _ ⊢σ ⊢τ = ≈-trans (N-[] _ ⊢σ) (≈-sym (N-[] _ ⊢τ))

⊢q : ∀ {i} → ⊢ Γ → Γ ⊢s σ ∶ Δ → Δ ⊢ T ∶ Se i → (T [ σ ]) ∷ Γ ⊢s q σ ∶ T ∷ Δ
⊢q ⊢Γ ⊢σ ⊢T = s-, (s-∘ (s-wk ⊢TσΓ) ⊢σ)
                  ⊢T
                  (conv (vlookup ⊢TσΓ here) ([∘]-Se ⊢T ⊢σ (s-wk ⊢TσΓ)))
  where ⊢TσΓ = ⊢∷ ⊢Γ (t[σ]-Se ⊢T ⊢σ)

⊢q-N : ⊢ Γ → ⊢ Δ → Γ ⊢s σ ∶ Δ → N ∷ Γ ⊢s q σ ∶ N ∷ Δ
⊢q-N ⊢Γ ⊢Δ ⊢σ = s-, (s-∘ (s-wk ⊢NΓ) ⊢σ)
                (N-wf 0 ⊢Δ)
                (conv (vlookup ⊢NΓ here) (≈-trans (N[wk]≈N 0 ⊢NΓ) (≈-sym (N-[] 0 (s-∘ (s-wk ⊢NΓ) ⊢σ)))))
  where ⊢NΓ = ⊢∷ ⊢Γ (N-wf 0 ⊢Γ)

⊢I,t : ∀ {i} → ⊢ Γ → Γ ⊢ T ∶ Se i → Γ ⊢ t ∶ T → Γ ⊢s I , t ∶ T ∷ Γ
⊢I,t ⊢Γ ⊢T ⊢t = s-, (s-I ⊢Γ) ⊢T (conv ⊢t (≈-sym ([I] ⊢T)))

⊢I,ze : ⊢ Γ → Γ ⊢s I , ze ∶ N ∷ Γ
⊢I,ze ⊢Γ = ⊢I,t ⊢Γ (N-wf 0 ⊢Γ) (ze-I ⊢Γ)

⊢[wk∘wk],su[v1] : ⊢ T ∷ N ∷ Γ → T ∷ N ∷ Γ ⊢s (wk ∘ wk) , su (v 1) ∶ N ∷ Γ
⊢[wk∘wk],su[v1] ⊢TNΓ@(⊢∷ ⊢NΓ@(⊢∷ _ ⊢N) _) = s-, ⊢wk∘wk ⊢N (conv-N-[]-sym (su-I (conv (vlookup ⊢TNΓ (there here)) (N[wk][wk]≈N 0 ⊢TNΓ))) ⊢wk∘wk)
  where
    ⊢wk∘wk = s-∘ (s-wk ⊢TNΓ) (s-wk ⊢NΓ)

_[wk]*_ : Typ → ℕ → Typ
_[wk]*_ T zero = T
_[wk]*_ T (suc n) = (T [wk]* n) [ wk ]

n∶T[wk]n∈!ΔTΓ : ∀ {n} → ⊢ Δ ++ T ∷ Γ → len Δ ≡ n → n ∶ T [wk]* (suc n) ∈! Δ ++ T ∷ Γ
n∶T[wk]n∈!ΔTΓ {Δ = []}    {n = zero} ⊢TΓ            _  = here
n∶T[wk]n∈!ΔTΓ {Δ = T ∷ Δ} {n = suc n} (⊢∷ ⊢ΔTΓ ⊢T) eq = there (n∶T[wk]n∈!ΔTΓ ⊢ΔTΓ (ℕₚ.suc-injective eq))

⊢vn∶T[wk]suc[n] : ∀ {n} → ⊢ Δ ++ T ∷ Γ → len Δ ≡ n → Δ ++ T ∷ Γ ⊢ v n ∶ T [wk]* (suc n)
⊢vn∶T[wk]suc[n] {Γ = Γ} {n = n} ⊢ΔTΓ eq = vlookup ⊢ΔTΓ (n∶T[wk]n∈!ΔTΓ ⊢ΔTΓ eq)

⊢Se[wk]n≈Se : ∀ {n i} Δ → ⊢ Δ ++ Γ → len Δ ≡ n → Δ ++ Γ ⊢ Se i [wk]* n ≈ Se i ∶ Se (suc i)
⊢Se[wk]n≈Se {n = zero}  []       ⊢Γ                _  = ≈-trans (≈-sym (Se-[] _ (s-I ⊢Γ))) (Se-[] _ (s-I ⊢Γ))
⊢Se[wk]n≈Se {n = suc n} (T ∷ Δ) ⊢TΔΓ@(⊢∷ ⊢ΔΓ _) eq = ≈-trans ([]-cong-Se′ (⊢Se[wk]n≈Se Δ ⊢ΔΓ (ℕₚ.suc-injective eq)) (s-wk ⊢TΔΓ)) (Se[wk]≈Se ⊢TΔΓ)

⊢N[wk]n≈N : ∀ {n} i Δ → ⊢ Δ ++ Γ → len Δ ≡ n → Δ ++ Γ ⊢ N [wk]* n ≈ N ∶ Se i
⊢N[wk]n≈N {n = zero}  i []       ⊢Γ                _  = ≈-trans (≈-sym (N-[] i (s-I ⊢Γ))) (N-[] i (s-I ⊢Γ))
⊢N[wk]n≈N {n = suc n} i (T ∷ Δ) ⊢TΔΓ@(⊢∷ ⊢ΔΓ _) eq = ≈-trans ([]-cong-Se′ (⊢N[wk]n≈N i Δ ⊢ΔΓ (ℕₚ.suc-injective eq)) (s-wk ⊢TΔΓ)) (N[wk]≈N i ⊢TΔΓ)

⊢vn∶Se : ∀ {n i} Δ → ⊢ Δ ++ Se i ∷ Γ → len Δ ≡ n → Δ ++ Se i ∷ Γ ⊢ v n ∶ Se i
⊢vn∶Se {Γ = Γ} {n = n} {i = i} Δ ⊢ΔSeΓ refl = conv (⊢vn∶T[wk]suc[n] ⊢ΔSeΓ refl) (lemma ⊢ΔSeΓ)
  where
    eqeq : Δ ++ Se i ∷ Γ ≡ (Δ L.∷ʳ Se i) ++ Γ
    eqeq = sym (Lₚ.++-assoc Δ L.[ _ ] _)


    lemma : ⊢ Δ ++ Se i ∷ Γ → Δ ++ Se i ∷ Γ ⊢ Se i [wk]* (suc n) ≈ Se i ∶ Se (suc i)
    lemma ⊢ΔNΓ rewrite eqeq
      = ⊢Se[wk]n≈Se (Δ L.∷ʳ _) ⊢ΔSeΓ
        (begin
          L.length (Δ L.∷ʳ _)
        ≡⟨ Lₚ.length-++ Δ ⟩
          L.length Δ + 1
        ≡⟨ ℕₚ.+-comm n _ ⟩
          suc n
        ∎)
      where
        open ≡-Reasoning

⊢vn∶N : ∀ {n} Δ → ⊢ Δ ++ N ∷ Γ → len Δ ≡ n → Δ ++ N ∷ Γ ⊢ v n ∶ N
⊢vn∶N {Γ = Γ} {n = n} Δ ⊢ΔNΓ refl = conv (⊢vn∶T[wk]suc[n] ⊢ΔNΓ refl) (lemma ⊢ΔNΓ)
  where
    eqeq : Δ ++ N ∷ Γ ≡ (Δ L.∷ʳ N) ++ Γ
    eqeq = sym (Lₚ.++-assoc Δ L.[ _ ] _)

    lemma : ⊢ Δ ++ N ∷ Γ → Δ ++ N ∷ Γ ⊢ N [wk]* (suc n) ≈ N ∶ Se 0
    lemma ⊢ΔNΓ rewrite eqeq
      = ⊢N[wk]n≈N 0 (Δ L.∷ʳ _) ⊢ΔNΓ
        (begin
          L.length (Δ L.∷ʳ _)
        ≡⟨ Lₚ.length-++ Δ ⟩
          L.length Δ + 1
        ≡⟨ ℕₚ.+-comm n _ ⟩
          suc n
        ∎)
      where
        open ≡-Reasoning
