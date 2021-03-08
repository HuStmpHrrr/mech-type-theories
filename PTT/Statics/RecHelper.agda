{-# OPTIONS --without-K --safe #-}

module PTT.Statics.RecHelper where

open import Lib
open import PTT.Statics
open import PTT.Statics.Misc
open import PTT.Statics.Stable
open import PTT.Statics.Complement

import Data.Nat.Properties as ℕₚ


ΠSe-$ : ∀ {i j} →
        ⊢ Γ →
        Γ ⊢ S ∶ Se j →
        Γ ⊢ T ∶ Π S (Se i) →
        Γ ⊢ s ∶ S →
        Γ ⊢ T $ s ∶ Se i
ΠSe-$ ⊢Γ ⊢S ⊢T ⊢s = conv (Λ-E ⊢T ⊢s) (≈-≲ (Se-[] (I-, ⊢Γ ⊢S ⊢s) ℕₚ.≤-refl))

ΠN≈[σ] : ∀ {i} →
         ⊢ Δ →
         ⊢ Γ →
         N ∷ Δ ⊢ T ∶ Se i →
         Γ ⊢s σ ∶ Δ →
         Γ ⊢ Π N T [ σ ] ≈ Π N (T [ q σ ]) ∶ Se i
ΠN≈[σ] ⊢Δ ⊢Γ ⊢T ⊢σ = ≈-trans (Π-[] ⊢σ (N-wf 0 ⊢Δ) ⊢T z≤n ℕₚ.≤-refl)
                             (≈-sym (Π-cong (N-wf 0 ⊢Γ)
                                            (≈-sym (N-[] 0 ⊢σ))
                                            (≈-refl (⊢T⇒⊢Tσ ⊢T (S-, (S-∘ (S-↑ (⊢∷ ⊢Γ (N-wf 0 ⊢Γ))) ⊢σ)
                                                                    (N-wf 0 ⊢Δ)
                                                                    (conv (vlookup (⊢∷ ⊢Γ (N-wf 0 ⊢Γ)) here)
                                                                          (≈-≲ (≈-trans (N-[] 0 (S-↑ (⊢∷ ⊢Γ (N-wf 0 ⊢Γ))))
                                                                                        (≈-sym (N-[] 0 (S-∘ (S-↑ (⊢∷ ⊢Γ (N-wf 0 ⊢Γ))) ⊢σ)))))))))
                                            z≤n
                                            ℕₚ.≤-refl))

ΠN[σ] : ∀ {i} →
          ⊢ Δ →
          ⊢ Γ →
          N ∷ Δ ⊢ T ∶ Se i →
          Δ ⊢ S ∶ Π N T →
          Γ ⊢s σ ∶ Δ →
          Γ ⊢ S [ σ ] ∶ Π N (T [ q σ ])
ΠN[σ] ⊢Δ ⊢Γ ⊢T ⊢S ⊢σ = conv (t[σ] ⊢S ⊢σ) (≈-≲ (ΠN≈[σ] ⊢Δ ⊢Γ ⊢T ⊢σ))

ΠNSe[σ]≈ : ∀ {i} →
           ⊢ Δ →
           ⊢ Γ →
           Δ ⊢ T ∶ Π N (Se i) →
           Γ ⊢s σ ∶ Δ →
           Γ ⊢ Π N (Se i) [ σ ] ≈ Π N (Se i) ∶ Se (suc i)
ΠNSe[σ]≈ {_} {_} {T} {σ} ⊢Δ ⊢Γ ⊢T ⊢σ = begin
  Π N (Se _) [ σ ]           ≈⟨ Π-[] ⊢σ ⊢N (Se-wf (⊢∷ ⊢Δ ⊢N) ℕₚ.≤-refl) _≤_.z≤n ℕₚ.≤-refl ⟩
  Π (N [ σ ]) (Se _ [ q σ ]) ≈!⟨ Π-cong (⊢T⇒⊢Tσ ⊢N ⊢σ) (N-[] 0 ⊢σ) (Se-[] qσ ℕₚ.≤-refl) _≤_.z≤n ℕₚ.≤-refl ⟩
  Π N (Se _)                 ∎
  where open TR
        ⊢N = N-wf 0 ⊢Δ
        qσ = ⊢qσ ⊢Γ (N-wf 0 ⊢Δ) ⊢σ

ΠNSe[σ] : ∀ {i} →
          ⊢ Δ →
          ⊢ Γ →
          Δ ⊢ T ∶ Π N (Se i) →
          Γ ⊢s σ ∶ Δ →
          Γ ⊢ T [ σ ] ∶ Π N (Se i)
ΠNSe[σ] {_} {_} {T} {σ} ⊢Δ ⊢Γ ⊢T ⊢σ = conv (t[σ] ⊢T ⊢σ) (≈-≲ (ΠNSe[σ]≈ ⊢Δ ⊢Γ ⊢T ⊢σ))

t∶N⇒tσ∶N : Δ ⊢ t ∶ N →
           Γ ⊢s σ ∶ Δ →
           Γ ⊢ t [ σ ] ∶ N
t∶N⇒tσ∶N ⊢t ⊢σ = conv (t[σ] ⊢t ⊢σ) (≈-≲ (N-[] 0 ⊢σ))

⊢Tze⇒T[σ]ze : ∀ {i} →
              ⊢ Γ →
              ⊢ Δ →
              Δ ⊢ T ∶ Π N (Se i) →
              Δ ⊢ s ∶ T $ ze →
              Γ ⊢s σ ∶ Δ →
              Γ ⊢ s [ σ ] ∶ T [ σ ] $ ze
⊢Tze⇒T[σ]ze ⊢Γ ⊢Δ ⊢T ⊢s ⊢σ = conv (t[σ] ⊢s ⊢σ) (≈-≲ (≈-trans ($-[]-Se (N-wf 0 ⊢Δ) ⊢σ ⊢T (ze-I ⊢Δ))
                                                             ($-cong-Se ⊢Γ (N-wf 0 ⊢Γ) (≈-refl (ΠNSe[σ] ⊢Δ ⊢Γ ⊢T ⊢σ)) (ze-[] ⊢σ) (t∶N⇒tσ∶N (ze-I ⊢Δ) ⊢σ))))

module _ {i Γ T} (⊢Γ : ⊢ Γ) (⊢T : Γ ⊢ T ∶ Π N (Se i)) where
  private
    ⊢N    = N-wf 0 ⊢Γ
    ⊢NΓ   = ⊢∷ ⊢Γ ⊢N
    v0∶N  = ⊢v0∶N ⊢NΓ
    ⊢T↑   = ΠNSe[σ] ⊢Γ ⊢NΓ ⊢T (S-↑ ⊢NΓ)
    ⊢T0NΓ = ⊢∷ ⊢NΓ (ΠSe-$ ⊢NΓ (N-wf 0 ⊢NΓ) ⊢T↑ (⊢v0∶N ⊢NΓ))
    ⊢↑↑   = S-∘ (S-↑ ⊢T0NΓ) (S-↑ ⊢NΓ)
    v0∶N′ = conv (vlookup ⊢T0NΓ (there here))
                 (≈-≲ (≈-trans (≈-sym (T-[∘] (S-↑ ⊢T0NΓ) (S-↑ ⊢NΓ) ⊢N))
                               (N-[] 0 ⊢↑↑)))
    ⊢Tv0  = ΠSe-$ ⊢NΓ  (N-wf 0 ⊢NΓ) (ΠNSe[σ] ⊢Γ ⊢NΓ ⊢T (S-↑ ⊢NΓ)) v0∶N
    ⊢Tv1  = ΠSe-$ ⊢T0NΓ (N-wf 0 ⊢T0NΓ) (ΠNSe[σ] ⊢Γ ⊢T0NΓ ⊢T ⊢↑↑) (su-I v0∶N′)
    ⊢v1∶N = v1-St ⊢T0NΓ N

  rec$t : N ∷ Γ ⊢ Π (T [ ↑ ] $ v 0) (T [ ↑ ∘ ↑ ] $ su (v 1)) ∶ Se i
  rec$t = Π-wf ⊢Tv0 ⊢Tv1 ℕₚ.≤-refl ℕₚ.≤-refl

  module _ {Δ σ} (⊢Δ : ⊢ Δ) (⊢σ : Δ ⊢s σ ∶ Γ) where
    private
      ⊢N′      = N-wf 0 ⊢Δ
      ⊢NΔ      = ⊢∷ ⊢Δ ⊢N′
      σ↑       = S-∘ (S-↑ ⊢NΔ) ⊢σ
      qσ       = S-, σ↑ ⊢N (conv (⊢v0∶N ⊢NΔ) (≈-≲ (≈-sym (N-[] 0 σ↑))))
      qqσ      = ⊢qσ ⊢NΔ ⊢Tv0 qσ
      ⊢Tv0qσ   = ⊢T⇒⊢Tσ ⊢Tv0 qσ
      ⊢Tv0qσNΔ = ⊢∷ ⊢NΔ ⊢Tv0qσ
      ⊢σ↑      = S-∘ (S-↑ ⊢NΔ) ⊢σ
      ⊢↑↑′     = S-∘ (S-↑ ⊢Tv0qσNΔ) (S-↑ ⊢NΔ)
      ↑∘qσ     = ↑-∘-, ⊢σ↑ ⊢N (v0-St-σ ⊢NΔ ⊢Γ N ⊢σ↑)
      qσ↑      = S-∘ (S-↑ ⊢Tv0qσNΔ) qσ

    T-rec-su[σ] : Δ ⊢ T-rec-su T [ σ ] ≈ T-rec-su (T [ σ ]) ∶ Se i
    T-rec-su[σ] = begin
      T-rec-su T [ σ ]                                           ≈⟨ ΠN≈[σ] ⊢Γ ⊢Δ rec$t ⊢σ ⟩
      (Π N (Π (T [ ↑ ] $ v 0) (T [ ↑ ∘ ↑ ] $ su (v 1)) [ q σ ])) ≈!⟨ Π-cong ⊢N′ (≈-refl ⊢N′) helper z≤n ℕₚ.≤-refl ⟩
      T-rec-su (T [ σ ])                                         ∎
      where aux = begin
              ↑ ∘ ↑ ∘ q (q σ)   ≈⟨ ∘-assoc (S-↑ ⊢NΓ) (S-↑ ⊢T0NΓ) qqσ ⟩
              ↑ ∘ (↑ ∘ q (q σ)) ≈⟨ ∘-cong (↑-∘-q ⊢NΔ ⊢Tv0 qσ) (↑-≈ ⊢NΓ) ⟩
              ↑ ∘ (q σ ∘ ↑)     ≈˘⟨ ∘-assoc (S-↑ ⊢NΓ) qσ (S-↑ ⊢Tv0qσNΔ) ⟩
              ↑ ∘ q σ ∘ ↑       ≈⟨ ∘-cong (↑-≈ ⊢Tv0qσNΔ) ↑∘qσ ⟩
              (σ ∘ ↑ ∘ ↑)       ≈!⟨ ∘-assoc ⊢σ (S-↑ ⊢NΔ) (S-↑ ⊢Tv0qσNΔ) ⟩
              σ ∘ (↑ ∘ ↑)       ∎
              where open TRS
            open TR
            eq = begin
              T [ ↑ ] [ q σ ] ≈˘⟨ [∘]-St ⊢NΔ ⊢Γ (Π N (Se i)) qσ (S-↑ ⊢NΓ) ⊢T ⟩
              T [ ↑ ∘ q σ ]   ≈⟨ []-cong-St ⊢NΔ ⊢Γ (Π N (Se i)) (S-∘ qσ (S-↑ ⊢NΓ)) (≈-refl ⊢T) ↑∘qσ ⟩
              T [ σ ∘ ↑ ]     ≈!⟨ [∘]-St ⊢NΔ ⊢Γ (Π N (Se i)) (S-↑ ⊢NΔ) ⊢σ ⊢T ⟩
              T [ σ ] [ ↑ ]   ∎
            eq′ = [,]-v-ze-St ⊢NΔ ⊢Γ N ⊢σ↑ (⊢v0∶N ⊢NΔ)
            eq″ = begin
              T [ ↑ ∘ ↑ ] [ q (q σ) ] ≈˘⟨ [∘]-St ⊢Tv0qσNΔ ⊢Γ (Π N (Se i)) qqσ ⊢↑↑ ⊢T ⟩
              T [ ↑ ∘ ↑ ∘ q (q σ) ]   ≈⟨ []-cong-St ⊢Tv0qσNΔ ⊢Γ (Π N (Se i)) (S-∘ qqσ ⊢↑↑) (≈-refl ⊢T) aux ⟩
              T [ σ ∘ (↑ ∘ ↑) ]       ≈!⟨ [∘]-St ⊢Tv0qσNΔ ⊢Γ (Π N (Se i)) ⊢↑↑′ ⊢σ ⊢T ⟩
              T [ σ ] [ ↑ ∘ ↑ ]       ∎
            eq‴ = begin
              su (v 1) [ q (q σ) ]   ≈⟨ su-[] qqσ ⊢v1∶N ⟩
              su (v 1 [ q (q σ) ])   ≈⟨ su-cong (≈-conv ([,]-v-su qσ↑ ⊢Tv0 (conv (vlookup ⊢Tv0qσNΔ here)
                                                                                 (≈-≲ (≈-sym ([∘]-St ⊢Tv0qσNΔ ⊢NΓ (Se _) (S-↑ ⊢Tv0qσNΔ) qσ ⊢Tv0))))
                                                                   here)
                                                         (≈-≲ (≈-trans (≈-sym ([∘]-St ⊢Tv0qσNΔ ⊢Γ (Se _) qσ↑ (S-↑ ⊢NΓ) ⊢N))
                                                                       (St-[] ⊢Tv0qσNΔ ⊢Γ N (S-∘ qσ↑ (S-↑ ⊢NΓ)))))) ⟩
              su (v 0 [ q σ ∘ ↑ ])   ≈⟨ su-cong ([∘]-St ⊢Tv0qσNΔ ⊢NΓ N (S-↑ ⊢Tv0qσNΔ) qσ v0∶N) ⟩
              su (v 0 [ q σ ] [ ↑ ]) ≈⟨ su-cong ([]-cong-St ⊢Tv0qσNΔ ⊢NΔ N (S-↑ ⊢Tv0qσNΔ) eq′ (↑-≈ ⊢Tv0qσNΔ)) ⟩
              su (v 0 [ ↑ ])         ≈!⟨ su-cong (≈-conv (↑-lookup ⊢Tv0qσNΔ here)
                                                 (≈-≲ (≈-trans (≈-sym ([∘]-St ⊢Tv0qσNΔ ⊢Δ (Se _) (S-↑ ⊢Tv0qσNΔ) (S-↑ ⊢NΔ) (N-wf 0 ⊢Δ)))
                                                               (St-[] ⊢Tv0qσNΔ ⊢Δ N ⊢↑↑′)))) ⟩
              su (v 1)               ∎
            helper′ = begin
              (T [ ↑ ] $ v 0) [ q σ ]                                            ≈⟨ $-[]-Se (N-wf 0 ⊢NΓ) qσ ⊢T↑ v0∶N ⟩
              T [ ↑ ] [ q σ ] $ v 0 [ q σ ]                                      ≈!⟨ $-cong-Se ⊢NΔ (N-wf 0 ⊢NΔ) eq eq′
                                                                                               (conv (t[σ] (vlookup ⊢NΓ here) qσ)
                                                                                                     (≈-≲ (≈-trans (≈-sym ([∘]-St ⊢NΔ ⊢Γ (Se _) qσ (S-↑ ⊢NΓ) (N-wf 0 ⊢Γ)))
                                                                                                                   (St-[] ⊢NΔ ⊢Γ N (S-∘ qσ (S-↑ ⊢NΓ)))))) ⟩
              T [ σ ] [ ↑ ] $ v 0                                                ∎
            helper″ = begin
              (T [ ↑ ∘ ↑ ] $ su (v 1)) [ q (q σ) ]                               ≈⟨ $-[]-Se (N-wf 0 ⊢T0NΓ) qqσ (ΠNSe[σ] ⊢Γ ⊢T0NΓ ⊢T ⊢↑↑) (su-I v0∶N′) ⟩
              T [ ↑ ∘ ↑ ] [ q (q σ) ] $ su (v 1) [ q (q σ) ]                     ≈!⟨ $-cong-Se ⊢Tv0qσNΔ
                                                                                               (N-wf 0 ⊢Tv0qσNΔ)
                                                                                               eq″
                                                                                               eq‴
                                                                                               (conv (t[σ] (su-I ⊢v1∶N) qqσ)
                                                                                                     (≈-≲ (St-[] ⊢Tv0qσNΔ ⊢T0NΓ N qqσ))) ⟩
              T [ σ ] [ ↑ ∘ ↑ ] $ su (v 1)                                       ∎
            helper  = begin
              Π (T [ ↑ ] $ v 0) (T [ ↑ ∘ ↑ ] $ su (v 1)) [ q σ ]                 ≈⟨ Π-[] qσ ⊢Tv0 ⊢Tv1 ℕₚ.≤-refl ℕₚ.≤-refl ⟩
              Π ((T [ ↑ ] $ v 0) [ q σ ]) ((T [ ↑ ∘ ↑ ] $ su (v 1)) [ q (q σ) ]) ≈!⟨ Π-cong (⊢T⇒⊢Tσ ⊢Tv0 qσ) helper′ helper″ ℕₚ.≤-refl ℕₚ.≤-refl ⟩
              Π (T [ σ ] [ ↑ ] $ v 0) (T [ σ ] [ ↑ ∘ ↑ ] $ su (v 1))             ∎
