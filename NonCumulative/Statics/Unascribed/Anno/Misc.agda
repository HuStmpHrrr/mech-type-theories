{-# OPTIONS --without-K --safe #-}

-- Some miscellaneous properties
module NonCumulative.Statics.Unascribed.Anno.Misc where

open import Lib
open import Data.Nat
import Data.Nat.Properties as ℕₚ
import Data.List.Properties as Lₚ

open import NonCumulative.Statics.Unascribed.Anno

t[σ]-Se : ∀ {i} → Δ ⊢ T ∶[ 1 + i ] Se i → Γ ⊢s σ ∶ Δ → Γ ⊢ T [ σ ] ∶[ 1 + i ] Se i
t[σ]-Se ⊢T ⊢σ = conv (t[σ] ⊢T ⊢σ) (Se-[] _ ⊢σ)

[]-cong-Se : ∀ {i} → Δ ⊢ T ≈ T′ ∶[ 1 + i ] Se i → Γ ⊢s σ ∶ Δ → Γ ⊢s σ ≈ σ′ ∶ Δ → Γ ⊢ T [ σ ] ≈ T′ [ σ′ ] ∶[ 1 + i ] Se i
[]-cong-Se T≈T′ ⊢σ σ≈σ′ = ≈-conv ([]-cong T≈T′ σ≈σ′) (Se-[] _ ⊢σ)

[]-cong-Se′ : ∀ {i} → Δ ⊢ T ≈ T′ ∶[ 1 + i ] Se i → Γ ⊢s σ ∶ Δ → Γ ⊢ T [ σ ] ≈ T′ [ σ ] ∶[ 1 + i ] Se i
[]-cong-Se′ T≈T′ ⊢σ = []-cong-Se T≈T′ ⊢σ (s-≈-trans (s-≈-sym (I-∘ ⊢σ)) (I-∘ ⊢σ))

[]-cong-Se″ : ∀ {i} → Δ ⊢ T ∶[ 1 + i ] Se i → Γ ⊢s σ ∶ Δ → Γ ⊢s σ ≈ σ′ ∶ Δ → Γ ⊢ T [ σ ] ≈ T [ σ′ ] ∶[ 1 + i ] Se i
[]-cong-Se″ ⊢T ⊢σ σ≈σ′ = []-cong-Se (≈-trans (≈-sym ([I] ⊢T)) ([I] ⊢T)) ⊢σ σ≈σ′

[∘]-Se : ∀ {i} → Δ ⊢ T ∶[ 1 + i ] Se i → Γ ⊢s σ ∶ Δ → Γ′ ⊢s τ ∶ Γ → Γ′ ⊢ T [ σ ] [ τ ] ≈ T [ σ ∘ τ ] ∶[ 1 + i ] Se i
[∘]-Se ⊢T ⊢σ ⊢τ = ≈-conv (≈-sym ([∘] ⊢τ ⊢σ ⊢T)) (Se-[] _ (s-∘ ⊢τ ⊢σ))

t[σ]-N : Δ ⊢ t ∶[ 0 ] N → Γ ⊢s σ ∶ Δ → Γ ⊢ t [ σ ] ∶[ 0 ] N
t[σ]-N ⊢t ⊢σ = conv (t[σ] ⊢t ⊢σ) (N-[] ⊢σ)

[]-cong-N : Δ ⊢ t ≈ t′ ∶[ 0 ] N → Γ ⊢s σ ∶ Δ → Γ ⊢s σ ≈ σ′ ∶ Δ → Γ ⊢ t [ σ ] ≈ t′ [ σ′ ] ∶[ 0 ] N
[]-cong-N t≈t′ ⊢σ σ≈σ′ = ≈-conv ([]-cong t≈t′ σ≈σ′) (N-[] ⊢σ)

[]-cong-N′ : Δ ⊢ t ≈ t′ ∶[ 0 ] N → Γ ⊢s σ ∶ Δ → Γ ⊢ t [ σ ] ≈ t′ [ σ ] ∶[ 0 ] N
[]-cong-N′ t≈t′ ⊢σ = []-cong-N t≈t′ ⊢σ (s-≈-trans (s-≈-sym (I-∘ ⊢σ)) (I-∘ ⊢σ))

[]-cong-N″ : Δ ⊢ t ∶[ 0 ] N → Γ ⊢s σ ∶ Δ → Γ ⊢s σ ≈ σ′ ∶ Δ → Γ ⊢ t [ σ ] ≈ t [ σ′ ] ∶[ 0 ] N
[]-cong-N″ ⊢t ⊢σ σ≈σ′ = []-cong-N (≈-trans (≈-sym ([I] ⊢t)) ([I] ⊢t)) ⊢σ σ≈σ′

conv-N-[] : Γ ⊢ t ∶[ 0 ] N [ σ ] → Γ ⊢s σ ∶ Δ → Γ ⊢ t ∶[ 0 ] N
conv-N-[] ⊢t ⊢σ = conv ⊢t (N-[] ⊢σ)

conv-N-[]-sym : Γ ⊢ t ∶[ 0 ] N → Γ ⊢s σ ∶ Δ → Γ ⊢ t ∶[ 0 ] N [ σ ]
conv-N-[]-sym ⊢t ⊢σ = conv ⊢t (≈-sym (N-[] ⊢σ))

≈-conv-N-[] : Γ ⊢ t ≈ t′ ∶[ 0 ] N [ σ ] → Γ ⊢s σ ∶ Δ → Γ ⊢ t ≈ t′ ∶[ 0 ] N
≈-conv-N-[] t≈t′ ⊢σ = ≈-conv t≈t′ (N-[] ⊢σ)

≈-conv-N-[]-sym : Γ ⊢ t ≈ t′ ∶[ 0 ] N → Γ ⊢s σ ∶ Δ → Γ ⊢ t ≈ t′ ∶[ 0 ] N [ σ ]
≈-conv-N-[]-sym t≈t′ ⊢σ = ≈-conv t≈t′ (≈-sym (N-[] ⊢σ))

Se[wk]≈Se : ∀ {j i} →
            ⊢ (j , T) ∷ Γ →
            (j , T) ∷ Γ ⊢ Se i [ wk ] ≈ Se i ∶[ 2 + i ] Se (suc i)
Se[wk]≈Se ⊢TΓ = Se-[] _ (s-wk ⊢TΓ)

N[wk]≈N : ∀ {i} →
          ⊢ (i , T) ∷ Γ →
          (i , T) ∷ Γ ⊢ N [ wk ] ≈ N ∶[ 1 ] Se 0
N[wk]≈N ⊢TΓ = N-[] (s-wk ⊢TΓ)

N-[][] : Γ′ ⊢s σ ∶ Γ″ →
         Γ ⊢s τ ∶ Γ′ →
         Γ ⊢ N [ σ ] [ τ ] ≈ N ∶[ 1 ] Se 0
N-[][] ⊢σ ⊢τ = ≈-trans ([]-cong-Se′ (N-[] ⊢σ) ⊢τ) (N-[] ⊢τ)

N[wk][wk]≈N : ∀ {i j} →
              ⊢ (i , S) ∷ (j , T) ∷ Γ →
              (i , S) ∷ (j , T) ∷ Γ ⊢ N [ wk ] [ wk ] ≈ N ∶[ 1 ] Se 0
N[wk][wk]≈N ⊢STΓ@(⊢∷ ⊢TΓ _) = N-[][] (s-wk ⊢TΓ) (s-wk ⊢STΓ)

N[σ]≈N[τ] : Γ ⊢s σ ∶ Δ →
            Γ ⊢s τ ∶ Δ′ →
            Γ ⊢ N [ σ ] ≈ N [ τ ] ∶[ 1 ] Se 0
N[σ]≈N[τ] ⊢σ ⊢τ = ≈-trans (N-[] ⊢σ) (≈-sym (N-[] ⊢τ))

⊢q : ∀ {i} → ⊢ Γ → Γ ⊢s σ ∶ Δ → Δ ⊢ T ∶[ 1 + i ] Se i → (i , T [ σ ]) ∷ Γ ⊢s q σ ∶ (i , T) ∷ Δ
⊢q ⊢Γ ⊢σ ⊢T = s-, (s-∘ (s-wk ⊢TσΓ) ⊢σ)
                  ⊢T
                  (conv (vlookup ⊢TσΓ (here ⊢Γ (t[σ]-Se ⊢T ⊢σ))) ([∘]-Se ⊢T ⊢σ (s-wk ⊢TσΓ)))
  where ⊢TσΓ = ⊢∷ ⊢Γ (t[σ]-Se ⊢T ⊢σ)

⊢q-N : ⊢ Γ → ⊢ Δ → Γ ⊢s σ ∶ Δ → (0 , N) ∷ Γ ⊢s q σ ∶ (0 , N) ∷ Δ
⊢q-N ⊢Γ ⊢Δ ⊢σ = s-, (s-∘ (s-wk ⊢NΓ) ⊢σ)
                (N-wf ⊢Δ)
                (conv (vlookup ⊢NΓ (here ⊢Γ (N-wf ⊢Γ))) (≈-trans (N[wk]≈N ⊢NΓ) (≈-sym (N-[] (s-∘ (s-wk ⊢NΓ) ⊢σ)))))
  where ⊢NΓ = ⊢∷ ⊢Γ (N-wf ⊢Γ)

⊢I,t : ∀ {i} → ⊢ Γ → Γ ⊢ T ∶[ 1 + i ] Se i → Γ ⊢ t ∶[ i ] T → Γ ⊢s I , t ∶ (i , T) ∷ Γ
⊢I,t ⊢Γ ⊢T ⊢t = s-, (s-I ⊢Γ) ⊢T (conv ⊢t (≈-sym ([I] ⊢T)))

⊢I,ze : ⊢ Γ → Γ ⊢s I , ze ∶ (0 , N) ∷ Γ
⊢I,ze ⊢Γ = ⊢I,t ⊢Γ (N-wf ⊢Γ) (ze-I ⊢Γ)

⊢[wk∘wk],su[v1] : ∀ {i} → ⊢ (i , T) ∷ (0 , N) ∷ Γ → (i , T) ∷ (0 , N) ∷ Γ ⊢s (wk ∘ wk) , su (v 1) ∶ (0 , N) ∷ Γ
⊢[wk∘wk],su[v1] ⊢TNΓ@(⊢∷ ⊢NΓ@(⊢∷ ⊢Γ ⊢N) ⊢T) = s-, ⊢wk∘wk ⊢N (conv-N-[]-sym (su-I (conv (vlookup ⊢TNΓ (there (⊢∷ ⊢Γ ⊢N) ⊢T (here ⊢Γ ⊢N))) (N[wk][wk]≈N ⊢TNΓ))) ⊢wk∘wk)
  where
    ⊢wk∘wk = s-∘ (s-wk ⊢TNΓ) (s-wk ⊢NΓ)

_[wk]*_ : Typ → ℕ → Typ
_[wk]*_ T zero = T
_[wk]*_ T (suc n) = (T [wk]* n) [ wk ]

n∶T[wk]n∈!ΔTΓ : ∀ {i n} (⊢ΔTΓ : ⊢ Δ ++ (i , T) ∷ Γ) → len Δ ≡ n → n ∶[ i ] T [wk]* (suc n) ∈ ⊢ΔTΓ
n∶T[wk]n∈!ΔTΓ {Δ = []} {n = zero} (⊢∷ ⊢TΓ ⊢T) _       = here ⊢TΓ ⊢T
n∶T[wk]n∈!ΔTΓ {Δ = T ∷ Δ} {n = suc n} (⊢∷ ⊢ΔTΓ ⊢T) eq = there ⊢ΔTΓ ⊢T (n∶T[wk]n∈!ΔTΓ ⊢ΔTΓ (ℕₚ.suc-injective eq))

⊢vn∶T[wk]suc[n] : ∀ {i n} → ⊢ Δ ++ (i , T) ∷ Γ → len Δ ≡ n → Δ ++ (i , T) ∷ Γ ⊢ v n ∶[ i ] T [wk]* (suc n)
⊢vn∶T[wk]suc[n] {Γ = Γ} {n = n} ⊢ΔTΓ eq = vlookup ⊢ΔTΓ (n∶T[wk]n∈!ΔTΓ ⊢ΔTΓ eq)

⊢Se[wk]n≈Se : ∀ {n i} Δ → ⊢ Δ ++ Γ → len Δ ≡ n → Δ ++ Γ ⊢ Se i [wk]* n ≈ Se i ∶[ 2 + i ] Se (suc i)
⊢Se[wk]n≈Se {n = zero}  []       ⊢Γ             _  = ≈-trans (≈-sym (Se-[] _ (s-I ⊢Γ))) (Se-[] _ (s-I ⊢Γ))
⊢Se[wk]n≈Se {n = suc n} (T ∷ Δ) ⊢TΔΓ@(⊢∷ ⊢ΔΓ _) eq = ≈-trans ([]-cong-Se′ (⊢Se[wk]n≈Se Δ ⊢ΔΓ (ℕₚ.suc-injective eq)) (s-wk ⊢TΔΓ)) (Se[wk]≈Se ⊢TΔΓ)

⊢N[wk]n≈N : ∀ {n} Δ → ⊢ Δ ++ Γ → len Δ ≡ n → Δ ++ Γ ⊢ N [wk]* n ≈ N ∶[ 1 ] Se 0
⊢N[wk]n≈N {n = zero}  []       ⊢Γ                _  = ≈-trans (≈-sym (N-[] (s-I ⊢Γ))) (N-[] (s-I ⊢Γ))
⊢N[wk]n≈N {n = suc n} (T ∷ Δ) ⊢TΔΓ@(⊢∷ ⊢ΔΓ _) eq = ≈-trans ([]-cong-Se′ (⊢N[wk]n≈N Δ ⊢ΔΓ (ℕₚ.suc-injective eq)) (s-wk ⊢TΔΓ)) (N[wk]≈N ⊢TΔΓ)

⊢vn∶Se : ∀ {n i} Δ → ⊢ Δ ++ (1 + i , Se i) ∷ Γ → len Δ ≡ n → Δ ++ (1 + i , Se i) ∷ Γ ⊢ v n ∶[ 1 + i ] Se i
⊢vn∶Se {Γ = Γ} {n = n} {i = i} Δ ⊢ΔSeΓ refl = conv (⊢vn∶T[wk]suc[n] ⊢ΔSeΓ refl) (lemma ⊢ΔSeΓ)
  where
    eqeq : Δ ++ (1 + i , Se i) ∷ Γ ≡ (Δ L.∷ʳ (1 + i , Se i)) ++ Γ
    eqeq = sym (Lₚ.++-assoc Δ L.[ _ ] _)


    lemma : ⊢ Δ ++ (1 + i , Se i) ∷ Γ → Δ ++ (1 + i , Se i) ∷ Γ ⊢ Se i [wk]* (suc n) ≈ Se i ∶[ 2 + i ] Se (suc i)
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

⊢vn∶N : ∀ {n} Δ → ⊢ Δ ++ (0 , N) ∷ Γ → len Δ ≡ n → Δ ++ (0 , N) ∷ Γ ⊢ v n ∶[ 0 ] N
⊢vn∶N {Γ = Γ} {n = n} Δ ⊢ΔNΓ refl = conv (⊢vn∶T[wk]suc[n] ⊢ΔNΓ refl) (lemma ⊢ΔNΓ)
  where
    eqeq : Δ ++ (0 , N) ∷ Γ ≡ (Δ L.∷ʳ (0 , N)) ++ Γ
    eqeq = sym (Lₚ.++-assoc Δ L.[ _ ] _)

    lemma : ⊢ Δ ++ (0 , N) ∷ Γ → Δ ++ (0 , N) ∷ Γ ⊢ N [wk]* (suc n) ≈ N ∶[ 1 ] Se 0
    lemma ⊢ΔNΓ rewrite eqeq
      = ⊢N[wk]n≈N (Δ L.∷ʳ _) ⊢ΔNΓ
        (begin
          L.length (Δ L.∷ʳ _)
        ≡⟨ Lₚ.length-++ Δ ⟩
          L.length Δ + 1
        ≡⟨ ℕₚ.+-comm n _ ⟩
          suc n
        ∎)
      where
        open ≡-Reasoning
