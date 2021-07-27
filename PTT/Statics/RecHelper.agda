{-# OPTIONS --without-K --safe #-}

module PTT.Statics.RecHelper where

open import Lib
open import PTT.Statics
open import PTT.Statics.Misc
open import PTT.Statics.Stable
open import PTT.Statics.Complement

import Data.Nat.Properties as ℕₚ


t∶N⇒tσ∶N : Δ ⊢ t ∶ N →
           Γ ⊢s σ ∶ Δ →
           Γ ⊢ t [ σ ] ∶ N
t∶N⇒tσ∶N ⊢t ⊢σ = conv (t[σ] ⊢t ⊢σ) (_ , N-[] 0 ⊢σ)

module _ {i Δ T} (⊢Δ : ⊢ Δ) (⊢T : N ∷ Δ ⊢ T ∶ Se i) where
  private
    ⊢NΔ  = ⊢∷ ⊢Δ (N-wf 0 ⊢Δ)
    ⊢TNΔ = ⊢∷ ⊢NΔ ⊢T

  module _ {Γ} (⊢Γ : ⊢ Γ) (⊢σ : Γ ⊢s σ ∶ Δ) where
    private
      ⊢NΓ       = ⊢∷ ⊢Γ (N-wf 0 ⊢Γ)
      qσ        = S-, (S-∘ (S-↑ ⊢NΓ) ⊢σ) (N-wf 0 ⊢Δ) (conv (vlookup ⊢NΓ here) (_ , ≈-trans (St-[]≈ ⊢NΓ ⊢Γ N (S-↑ ⊢NΓ)) (≈-sym (St-[]≈ ⊢NΓ ⊢Δ N (S-∘ (S-↑ ⊢NΓ) ⊢σ)))))
      qqσ       = ⊢qσ ⊢NΓ ⊢T qσ
      ⊢Tqσ      = ⊢T⇒⊢Tσ ⊢T qσ
      ⊢TNΓ      = ⊢∷ ⊢NΓ ⊢Tqσ
      ⊢suv1     = conv (su-I (v1-St ⊢TNΔ N)) (_ , ≈-sym (St-[]≈ ⊢TNΔ ⊢Δ N (S-∘ (S-↑ ⊢TNΔ) (S-↑ ⊢NΔ))))
      ⊢↑↑       = S-∘ (S-↑ ⊢TNΔ) (S-↑ ⊢NΔ)
      ⊢↑↑′      = S-∘ (S-↑ ⊢TNΓ) (S-↑ ⊢NΓ)
      ⊢suv1′    = conv (su-I (v1-St ⊢TNΓ N)) (_ , ≈-sym (St-[]≈ ⊢TNΓ ⊢Γ N ⊢↑↑′))
      ⊢↑↑,suv1  = S-, (S-∘ (S-↑ ⊢TNΔ) (S-↑ ⊢NΔ)) (N-wf 0 ⊢Δ) ⊢suv1
      ⊢↑↑,suv1′ = S-, (S-∘ (S-↑ ⊢TNΓ) (S-↑ ⊢NΓ)) (N-wf 0 ⊢Γ) ⊢suv1′
      ⊢σ↑       = S-∘ (S-↑ ⊢NΓ) ⊢σ

      eq : T [ q σ ] ∷ N ∷ Γ ⊢s ↑ ∘ ↑ ∘ q (q σ) ≈ σ ∘ ↑ ∘ ↑ ∶ Δ
      eq = begin
        ↑ ∘ ↑ ∘ q (q σ)   ≈⟨ ∘-assoc (S-↑ ⊢NΔ) (S-↑ ⊢TNΔ) qqσ ⟩
        ↑ ∘ (↑ ∘ q (q σ)) ≈⟨ ∘-cong (↑-∘-q ⊢NΓ ⊢T qσ) (S-≈-refl (S-↑ ⊢NΔ)) ⟩
        ↑ ∘ (q σ ∘ ↑)     ≈˘⟨ ∘-assoc (S-↑ ⊢NΔ) qσ (S-↑ ⊢TNΓ) ⟩
        ↑ ∘ q σ ∘ ↑       ≈⟨ ∘-cong (S-≈-refl (S-↑ ⊢TNΓ)) (↑-∘-, ⊢σ↑ (N-wf 0 ⊢Δ) (conv (vlookup ⊢NΓ here) (0 , subst-N-stable (S-↑ ⊢NΓ) ⊢σ↑))) ⟩
        σ ∘ ↑ ∘ ↑         ∎
        where open TRS

      eq′ : T [ q σ ] ∷ N ∷ Γ ⊢ su (v 1) [ q (q σ) ] ≈ su (v 1) ∶ N [ ↑ ∘ ↑ ∘ q (q σ) ]
      eq′ = ≈-conv (≈-trans (su-[] qqσ (v1-St ⊢TNΔ N))
                            (su-cong (≈-trans (≈-conv ([,]-v-su (S-∘ (S-↑ ⊢TNΓ) qσ) ⊢T (conv (vlookup ⊢TNΓ here) (_ , ≈-sym (T-[∘] (S-↑ ⊢TNΓ) qσ ⊢T))) here)
                                                      (_ , ≈-trans (≈-sym (T-[∘] (S-∘ (S-↑ ⊢TNΓ) qσ) (S-↑ ⊢NΔ) (N-wf 0 ⊢Δ))) (N-[] 0 (S-∘ (S-∘ (S-↑ ⊢TNΓ) qσ) (S-↑ ⊢NΔ)))))
                                     (≈-trans (≈-conv ([∘]-St ⊢TNΓ ⊢NΔ N (S-↑ ⊢TNΓ) qσ (v0-St ⊢NΔ N)) (_ , N-≈ 0 ⊢TNΓ))
                                     (≈-trans (≈-conv ([]-cong (↑-≈ ⊢TNΓ) ([,]-v-ze ⊢σ↑ (N-wf 0 ⊢Δ) (conv (⊢v0∶N ⊢NΓ) (_ , ≈-sym (N-[] 0 ⊢σ↑)))))
                                                      (_ , ≈-trans (≈-sym (T-[∘] (S-↑ ⊢TNΓ) ⊢σ↑ (N-wf 0 ⊢Δ))) (N-[] 0 (S-∘ (S-↑ ⊢TNΓ) (S-∘ (S-↑ ⊢NΓ) ⊢σ)))))
                                     (≈-trans (≈-conv (≈-sym ([,]-v-su (S-↑ ⊢TNΓ) (⊢T⇒⊢Tσ ⊢T qσ) (vlookup ⊢TNΓ here) here))
                                                      (_ , ≈-trans (≈-sym (T-[∘] (S-↑ ⊢TNΓ) (S-↑ ⊢NΓ) (N-wf 0 ⊢Γ))) (N-[] 0 (S-∘ (S-↑ ⊢TNΓ) (S-↑ ⊢NΓ)))))
                                     (≈-trans (≈-sym (≈-conv ([]-cong (I-ext ⊢TNΓ) (≈-refl (v1-St ⊢TNΓ N))) (_ , N-[] 0 (S-I ⊢TNΓ))))
                                              ([I] (v1-St ⊢TNΓ N)))))))))
                   (0 , ≈-sym (N-[] 0 (S-∘ qqσ (S-∘ (S-↑ ⊢TNΔ) (S-↑ ⊢NΔ)))))


      helper : T [ q σ ] ∷ N ∷ Γ ⊢s (↑ ∘ ↑) , su (v 1) ∘ q (q σ) ≈ q σ ∘ ((↑ ∘ ↑) , su (v 1)) ∶ N ∷ Δ
      helper = begin
        ((↑ ∘ ↑) , su (v 1)) ∘ q (q σ)                                ≈⟨ ,-ext′ ⊢NΔ ⊢↑↑ qqσ ⊢suv1 ⟩
        (↑ ∘ ↑ ∘ q (q σ)) , (su (v 1) [ q (q σ) ])                    ≈⟨ ,-cong (N-wf 0 ⊢Δ) eq eq′ ⟩
        (σ ∘ ↑ ∘ ↑) , su (v 1)                                        ≈⟨ ,-cong (N-wf 0 ⊢Δ) (S-≈-trans (∘-assoc ⊢σ (S-↑ ⊢NΓ) (S-↑ ⊢TNΓ))
                                                                                            (S-≈-trans (∘-cong (S-≈-sym (↑-∘-, ⊢↑↑′ (N-wf 0 ⊢Γ) ⊢suv1′)) (S-≈-refl ⊢σ))
                                                                                                       (S-≈-sym (∘-assoc ⊢σ (S-↑ ⊢NΓ) ⊢↑↑,suv1′))))
                                                                                            (≈-conv (≈-sym ([,]-v-ze ⊢↑↑′ (N-wf 0 ⊢Γ) ⊢suv1′))
                                                                                                    (0 , subst-N-stable ⊢↑↑′ (S-∘ (S-↑ ⊢TNΓ) ⊢σ↑))) ⟩
        (σ ∘ ↑ ∘ ((↑ ∘ ↑) , su (v 1))) , (v 0 [ (↑ ∘ ↑) , su (v 1) ]) ≈˘⟨ ,-ext′ ⊢NΔ (S-∘ (S-↑ ⊢NΓ) ⊢σ) ⊢↑↑,suv1′ (v0-St-σ ⊢NΓ ⊢Δ N ⊢σ↑) ⟩
        q σ ∘ ((↑ ∘ ↑) , su (v 1))                                    ∎
        where open TRS

    rec-su-T[σ] : T [ q σ ] ∷ N ∷ Γ ⊢ T [ (↑ ∘ ↑) , su (v 1) ] [ q (q σ) ] ≈ T [ q σ ] [ (↑ ∘ ↑) , su (v 1) ] ∶ Se i
    rec-su-T[σ] = ≈-trans (≈-sym (T-[∘] qqσ ⊢↑↑,suv1 ⊢T))
                  (≈-trans (⊢≈⇒⊢≈σ′ (≈-refl ⊢T) helper (S-∘ qqσ ⊢↑↑,suv1))
                           (T-[∘] (S-, ⊢↑↑′ (N-wf 0 ⊢Γ) ⊢suv1′) qσ ⊢T))
