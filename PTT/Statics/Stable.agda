{-# OPTIONS --without-K --safe #-}

module PTT.Statics.Stable where

open import Lib
open import PTT.Statics
open import Data.Nat using (_⊔_)

import Data.Nat.Properties as ℕₚ

data St : Typ → Set where
  Se : ∀ i → St (Se i)
  N  : St N
  Π  : St S → St T → St (Π S T)

St-level : St T → ℕ
St-level (Se i) = suc i
St-level N = 0
St-level (Π S U) = St-level S ⊔ St-level U

St-ty : ⊢ Γ →
        (t : St T) →
        Γ ⊢ T ∶ Se (St-level t)
St-ty ⊢Γ (Se i)  = Se-wf ⊢Γ ℕₚ.≤-refl
St-ty ⊢Γ N       = N-wf 0 ⊢Γ
St-ty ⊢Γ (Π S T) = Π-wf (St-ty ⊢Γ S) (St-ty (⊢∷ ⊢Γ ⊢S) T) (ℕₚ.m≤m⊔n _ _) (ℕₚ.n≤m⊔n _ _)
  where ⊢S = St-ty ⊢Γ S

St-[] : ⊢ Γ →
        ⊢ Δ →
        (t : St T) →
        Γ ⊢s σ ∶ Δ →
        Γ ⊢ T [ σ ] ≈ T ∶ Se (St-level t)
St-[] ⊢Γ ⊢Δ (Se i) ⊢σ  = Se-[] ⊢σ ℕₚ.≤-refl
St-[] ⊢Γ ⊢Δ N ⊢σ       = N-[] 0 ⊢σ
St-[] ⊢Γ ⊢Δ (Π S T) ⊢σ = ≈-trans (Π-[] ⊢σ ⊢S (St-ty (⊢∷ ⊢Δ ⊢S) T) (ℕₚ.m≤m⊔n _ _) (ℕₚ.n≤m⊔n _ _))
                                 (≈-sym (Π-cong (St-ty ⊢Γ S)
                                                (≈-sym (St-[] ⊢Γ ⊢Δ S ⊢σ))
                                                (≈-sym (St-[] ⊢SΓ ⊢SΔ T
                                                       (S-, (S-∘ (S-↑ ⊢SΓ) ⊢σ) ⊢S
                                                            (conv (vlookup ⊢SΓ here)
                                                                  (≈-≲ (≈-trans (St-[] ⊢SΓ ⊢Γ S (S-↑ ⊢SΓ))
                                                                                (≈-sym (St-[] ⊢SΓ ⊢Δ S (S-∘ (S-↑ ⊢SΓ) ⊢σ)))))))))
                                                (ℕₚ.m≤m⊔n _ _)
                                                (ℕₚ.n≤m⊔n _ _)))
  where ⊢S  = St-ty ⊢Δ S
        ⊢S′ = St-ty ⊢Γ S
        ⊢SΓ = ⊢∷ ⊢Γ ⊢S′
        ⊢SΔ = ⊢∷ ⊢Δ ⊢S

t[σ]-Se : ⊢ Γ →
          ⊢ Δ →
          St T →
          Δ ⊢ t ∶ T →
          Γ ⊢s σ ∶ Δ →
          Γ ⊢ t [ σ ] ∶ T
t[σ]-Se ⊢Γ ⊢Δ T ⊢t ⊢σ = conv (t[σ] ⊢t ⊢σ) (≈-≲ (St-[] ⊢Γ ⊢Δ T ⊢σ))

[∘]-St : ⊢ Γ →
         ⊢ Γ″ →
         St T →
         Γ ⊢s τ ∶ Γ′ →
         Γ′ ⊢s σ ∶ Γ″ →
         Γ″ ⊢ S ∶ T →
         ---------------------------------------
         Γ ⊢ S [ σ ∘ τ ] ≈ S [ σ ] [ τ ] ∶ T
[∘]-St ⊢Γ ⊢Γ″ T ⊢τ ⊢σ ⊢S = ≈-conv ([∘] ⊢τ ⊢σ ⊢S)
                                  (≈-≲ (St-[] ⊢Γ ⊢Γ″ T (S-∘ ⊢τ ⊢σ)))

[]-cong-St : ⊢ Γ →
             ⊢ Δ →
             St T →
             Γ ⊢s σ ∶ Δ →
             Δ ⊢ S ≈ S′ ∶ T →
             Γ ⊢s σ ≈ τ ∶ Δ →
             Γ ⊢ S [ σ ] ≈ S′ [ τ ] ∶ T
[]-cong-St ⊢Γ ⊢Δ T ⊢σ S≈S′ σ≈τ = ≈-conv ([]-cong σ≈τ S≈S′) (≈-≲ (St-[] ⊢Γ ⊢Δ T ⊢σ))

$-[]-St : ∀ {i} →
          ⊢ Γ →
          ⊢ Δ →
          St T′ →
          Δ ⊢ S ∶ Se i →
          Γ ⊢s σ ∶ Δ →
          Δ ⊢ T ∶ Π S T′ →
          Δ ⊢ s ∶ S →
          ----------------------------------------------
          Γ ⊢ (T $ s) [ σ ] ≈ T [ σ ] $ s [ σ ] ∶ T′
$-[]-St ⊢Γ ⊢Δ T′ ⊢S ⊢σ ⊢T ⊢s = ≈-conv ($-[] ⊢σ ⊢T ⊢s)
                                      (≈-≲ (St-[] ⊢Γ (⊢∷ ⊢Δ ⊢S) T′ (S-, ⊢σ ⊢S (t[σ] ⊢s ⊢σ))))

$-cong-St : ∀ {i} →
            ⊢ Γ →
            St T′ →
            Γ ⊢ S ∶ Se i →
            Γ ⊢ T ≈ T′ ∶ Π S T′ →
            Γ ⊢ s ≈ s′ ∶ S →
            Γ ⊢ s ∶ S →
            --------------------------
            Γ ⊢ T $ s ≈ T′ $ s′ ∶ T′
$-cong-St ⊢Γ T′ ⊢S T≈T′ s≈s′ ⊢s = ≈-conv ($-cong T≈T′ s≈s′)
                                         (≈-≲ (St-[] ⊢Γ (⊢∷ ⊢Γ ⊢S) T′ (S-, (S-I ⊢Γ) ⊢S (conv ⊢s (≈-≲ (≈-sym ([I] ⊢S)))))))
