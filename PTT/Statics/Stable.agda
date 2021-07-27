{-# OPTIONS --without-K --safe #-}

module PTT.Statics.Stable where

open import Lib
open import PTT.Statics
open import Data.Nat using (_⊔_)
open import PTT.Statics.Misc
open import PTT.Statics.Complement

import Data.Nat.Properties as ℕₚ
open import Relation.Binary.Construct.Closure.ReflexiveTransitive

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
St-ty ⊢Γ (Se i)  = Se-wf i ⊢Γ
St-ty ⊢Γ N       = N-wf 0 ⊢Γ
St-ty ⊢Γ (Π S T) = Π-wf (lift-⊢-Se ⊢S (ℕₚ.m≤m⊔n _ _)) (lift-⊢-Se (St-ty (⊢∷ ⊢Γ ⊢S) T) (ℕₚ.m≤n⊔m _ _))
  where ⊢S = St-ty ⊢Γ S

St-[] : ⊢ Γ →
        ⊢ Δ →
        (t : St T) →
        Γ ⊢s σ ∶ Δ →
        Γ ⊢ T [ σ ] ∶ Se (St-level t)
St-[] ⊢Γ ⊢Δ (Se i) ⊢σ  = conv (t[σ] (Se-wf i ⊢Δ) ⊢σ) (suc (suc i) , Se-[] (suc i) ⊢σ)
St-[] ⊢Γ ⊢Δ N ⊢σ       = conv (t[σ] (N-wf zero ⊢Δ) ⊢σ) (1 , Se-[] zero ⊢σ)
St-[] ⊢Γ ⊢Δ (Π S T) ⊢σ = conv (t[σ] (St-ty ⊢Δ (Π S T)) ⊢σ) (_ , Se-[] _ ⊢σ)

St-[]≈ : ⊢ Γ →
         ⊢ Δ →
         (t : St T) →
         Γ ⊢s σ ∶ Δ →
         Γ ⊢ T [ σ ] ≈ T ∶ Se (St-level t)
St-[]≈ ⊢Γ ⊢Δ (Se i) ⊢σ  = Se-[] i ⊢σ
St-[]≈ ⊢Γ ⊢Δ N ⊢σ       = N-[] 0 ⊢σ
St-[]≈ ⊢Γ ⊢Δ (Π S T) ⊢σ = ≈-trans (Π-[] ⊢σ (lift-⊢-Se ⊢S (ℕₚ.m≤m⊔n _ _)) (lift-⊢-Se (St-ty ⊢SΔ T) (ℕₚ.m≤n⊔m _ _)))
                                  (Π-cong (lift-⊢≈-Se (St-[]≈ ⊢Γ ⊢Δ S ⊢σ) (ℕₚ.m≤m⊔n _ _))
                                          (lift-⊢≈-Se (St-[]≈ (⊢∷ ⊢Γ ⊢Sσ) (⊢∷ ⊢Δ ⊢S) T (⊢qσ ⊢Γ ⊢S ⊢σ)) (ℕₚ.m≤n⊔m _ _)))
  where ⊢S  = St-ty ⊢Δ S
        ⊢Sσ = ⊢T⇒⊢Tσ ⊢S ⊢σ
        ⊢SΔ = ⊢∷ ⊢Δ ⊢S

v0-St : ⊢ T ∷ Γ →
        St T →
        T ∷ Γ ⊢ v 0 ∶ T
v0-St ⊢Γ@(⊢∷ ⊢Γ′ _) T = conv (vlookup ⊢Γ here) (_ , St-[]≈ ⊢Γ ⊢Γ′ T (S-↑ ⊢Γ))

v0-St-σ : ⊢ T ∷ Γ →
          ⊢ Δ →
          St T →
          T ∷ Γ ⊢s σ ∶ Δ →
          T ∷ Γ ⊢ v 0 ∶ T [ σ ]
v0-St-σ ⊢Γ@(⊢∷ ⊢Γ′ _) ⊢Δ T ⊢σ = conv (v0-St ⊢Γ T) (_ , ≈-sym (St-[]≈ ⊢Γ ⊢Δ T ⊢σ))

t[σ]-St : ⊢ Γ →
          ⊢ Δ →
          St T →
          Δ ⊢ t ∶ T →
          Γ ⊢s σ ∶ Δ →
          Γ ⊢ t [ σ ] ∶ T
t[σ]-St ⊢Γ ⊢Δ T ⊢t ⊢σ = conv (t[σ] ⊢t ⊢σ) (_ , St-[]≈ ⊢Γ ⊢Δ T ⊢σ)

[∘]-St : ⊢ Γ →
         ⊢ Γ″ →
         St T →
         Γ ⊢s τ ∶ Γ′ →
         Γ′ ⊢s σ ∶ Γ″ →
         Γ″ ⊢ S ∶ T →
         ---------------------------------------
         Γ ⊢ S [ σ ∘ τ ] ≈ S [ σ ] [ τ ] ∶ T
[∘]-St ⊢Γ ⊢Γ″ T ⊢τ ⊢σ ⊢S = ≈-conv ([∘] ⊢τ ⊢σ ⊢S)
                                  (_ , St-[]≈ ⊢Γ ⊢Γ″ T (S-∘ ⊢τ ⊢σ))

[]-cong-St : ⊢ Γ →
             ⊢ Δ →
             St T →
             Γ ⊢s σ ∶ Δ →
             Δ ⊢ S ≈ S′ ∶ T →
             Γ ⊢s σ ≈ τ ∶ Δ →
             Γ ⊢ S [ σ ] ≈ S′ [ τ ] ∶ T
[]-cong-St ⊢Γ ⊢Δ T ⊢σ S≈S′ σ≈τ = ≈-conv ([]-cong σ≈τ S≈S′) (_ , St-[]≈ ⊢Γ ⊢Δ T ⊢σ)

-- $-[]-St : ∀ {i} →
--           ⊢ Γ →
--           ⊢ Δ →
--           St T′ →
--           Δ ⊢ S ∶ Se i →
--           Γ ⊢s σ ∶ Δ →
--           Δ ⊢ T ∶ Π S T′ →
--           Δ ⊢ s ∶ S →
--           ----------------------------------------------
--           Γ ⊢ (T $ s) [ σ ] ≈ T [ σ ] $ s [ σ ] ∶ T′
-- $-[]-St ⊢Γ ⊢Δ T′ ⊢S ⊢σ ⊢T ⊢s = ≈-conv ($-[] ⊢σ ⊢T ⊢s)
--                                       (≈-≲ (St-[] ⊢Γ (⊢∷ ⊢Δ ⊢S) T′ (S-, ⊢σ ⊢S (t[σ] ⊢s ⊢σ))))

-- $-cong-St : ∀ {i} →
--             ⊢ Γ →
--             St T″ →
--             Γ ⊢ S ∶ Se i →
--             Γ ⊢ T ≈ T′ ∶ Π S T″ →
--             Γ ⊢ s ≈ s′ ∶ S →
--             Γ ⊢ s ∶ S →
--             --------------------------
--             Γ ⊢ T $ s ≈ T′ $ s′ ∶ T″
-- $-cong-St ⊢Γ T′ ⊢S T≈T′ s≈s′ ⊢s = ≈-conv ($-cong T≈T′ s≈s′)
--                                          (≈-≲ (St-[] ⊢Γ (⊢∷ ⊢Γ ⊢S) T′ (S-, (S-I ⊢Γ) ⊢S (conv ⊢s (≈-≲ (≈-sym ([I] ⊢S)))))))

-- [,]-v-ze-St : ⊢ Γ →
--               ⊢ Δ →
--               St S →
--               Γ ⊢s σ ∶ Δ →
--               Γ ⊢ s ∶ S →
--               --------------------------------
--               Γ ⊢ v 0 [ σ , s ] ≈ s ∶ S
-- [,]-v-ze-St ⊢Γ ⊢Δ S ⊢σ ⊢s = ≈-conv ([,]-v-ze ⊢σ (St-ty ⊢Δ S) (conv ⊢s (≈-≲ (≈-sym (St-[] ⊢Γ ⊢Δ S ⊢σ)))))
--                                    (≈-≲ (St-[] ⊢Γ ⊢Δ S ⊢σ))

-- -- [,]-v-su : ∀ {i x} →
-- --            ⊢ Γ →
-- --            ⊢ Δ →
-- --            Γ ⊢s σ ∶ Δ →
-- --            Δ ⊢ S ∶ Se i →
-- --            Γ ⊢ s ∶ S [ σ ] →
-- --            x ∶ T ∈! Δ →
-- --            ---------------------------------------------
-- --            Γ ⊢ v (suc x) [ σ , s ] ≈ v x [ σ ] ∶ T [ σ ]


v1-St : ⊢ S ∷ T ∷ Γ →
        St T →
        S ∷ T ∷ Γ ⊢ v 1 ∶ T
v1-St (⊢∷ (⊢∷ ⊢Γ ⊢T) ⊢S) T = conv (vlookup (⊢∷ (⊢∷ ⊢Γ ⊢T) ⊢S) (there here))
                                  (_ , ≈-trans (⊢≈⇒⊢≈σ (St-[]≈ (⊢∷ ⊢Γ ⊢T) ⊢Γ T (S-↑ (⊢∷ ⊢Γ ⊢T))) (S-↑ (⊢∷ (⊢∷ ⊢Γ ⊢T) ⊢S))) (St-[]≈ (⊢∷ (⊢∷ ⊢Γ ⊢T) ⊢S) (⊢∷ ⊢Γ ⊢T) T (S-↑ (⊢∷ (⊢∷ ⊢Γ ⊢T) ⊢S))))
  where T↑≈ = St-[] (⊢∷ ⊢Γ ⊢T) ⊢Γ T (S-↑ (⊢∷ ⊢Γ ⊢T))
