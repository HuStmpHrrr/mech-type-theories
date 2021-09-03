{-# OPTIONS --without-K --safe #-}

module PTT.Statics.Inv where

open import Lib
open import PTT.Statics
open import PTT.Statics.Misc
open import PTT.Statics.Complement
open import PTT.Statics.Stable
-- open import PTT.Statics.CtxSubst
open import PTT.Statics.RecHelper

import Data.Nat.Properties as ℕₚ
open import Relation.Binary.Construct.Closure.ReflexiveTransitive

mutual
  ty⇒env-ty-wf : Γ ⊢ t ∶ T →
                 ------------
                 ⊢ Γ × Γ ⊢ T
  ty⇒env-ty-wf (N-wf i ⊢Γ)        = ⊢Γ , suc i , Se-wf i ⊢Γ
  ty⇒env-ty-wf (Se-wf i ⊢Γ)       = ⊢Γ , suc (suc i) , Se-wf (suc i) ⊢Γ
  ty⇒env-ty-wf (Π-wf ⊢S ⊢T)       = ty⇒env-ty-wf ⊢S
  ty⇒env-ty-wf (vlookup ⊢Γ T∈Γ)   = ⊢Γ , (∈!⇒ty-wf ⊢Γ T∈Γ)
  ty⇒env-ty-wf (ze-I ⊢Γ)          = ⊢Γ , zero , N-wf zero ⊢Γ
  ty⇒env-ty-wf (su-I ⊢t)          = ty⇒env-ty-wf ⊢t
  ty⇒env-ty-wf (N-E ⊢T ⊢s ⊢u ⊢t)
    with ty⇒env-ty-wf ⊢t
  ...  | ⊢Γ , _                   = ⊢Γ , _ , conv (t[σ] ⊢T I,t) (_ , Se-[] _ I,t)
    where I,t                     = S-, (S-I ⊢Γ) (N-wf 0 ⊢Γ) (conv ⊢t (0 , ≈-sym (N-[] _ (S-I ⊢Γ))))
  ty⇒env-ty-wf (Λ-I ⊢t)
    with ty⇒env-ty-wf ⊢t
  ... | ⊢∷ {i = i} ⊢Γ ⊢S , j , ⊢T = ⊢Γ , max i j , Π-wf (lift-⊢-Se ⊢S (ℕₚ.m≤m⊔n _ _)) (lift-⊢-Se ⊢T (ℕₚ.m≤n⊔m _ _))
  ty⇒env-ty-wf (Λ-E ⊢r ⊢s)
    with ty⇒env-ty-wf ⊢r
  ...  | ⊢Γ , _ , ⊢Π
       with inv-Π-wf′ ⊢Π | inv-Π-wf ⊢Π
  ...     | _ , ⊢S       | _ , ⊢T = ⊢Γ , _ , ⊢T⇒⊢Tσ ⊢T (S-, (S-I ⊢Γ) ⊢S (conv ⊢s (_ , ≈-sym ([I] ⊢S))))
  ty⇒env-ty-wf (t[σ] ⊢t ⊢σ)
    with ty⇒env-ty-wf ⊢t | tys⇒env-wf ⊢σ
  ...  | ⊢Δ , _ , ⊢T | ⊢Γ , _     = ⊢Γ , _ , ⊢T⇒⊢Tσ ⊢T ⊢σ
  ty⇒env-ty-wf (cumu ⊢t)
    with ty⇒env-ty-wf ⊢t
  ...  | ⊢Γ , _                   = ⊢Γ , _ , Se-wf _ ⊢Γ
  ty⇒env-ty-wf (conv ⊢t (_ , S≈T))
    with ty-eq⇒env-ty-wf-gen S≈T
  ...  | ⊢Γ , _ , ⊢T , _          = ⊢Γ , _ , ⊢T

  tys⇒env-wf : Γ ⊢s σ ∶ Δ →
               ------------
               ⊢ Γ × ⊢ Δ
  tys⇒env-wf (S-↑ ⊢SΓ@(⊢∷ ⊢Γ _)) = ⊢SΓ , ⊢Γ
  tys⇒env-wf (S-I ⊢Γ)            = ⊢Γ , ⊢Γ
  tys⇒env-wf (S-∘ ⊢τ ⊢σ)
    with tys⇒env-wf ⊢τ | tys⇒env-wf ⊢σ
  ...  | ⊢Γ , _ | _ , ⊢Δ         = ⊢Γ , ⊢Δ
  tys⇒env-wf (S-, ⊢σ ⊢S ⊢s)
    with tys⇒env-wf ⊢σ
  ...  | ⊢Γ , ⊢Δ                 = ⊢Γ , ⊢∷ ⊢Δ ⊢S

  ty-eq⇒env-ty-wf-gen : Γ ⊢ s ≈ t ∶ T →
                        -----------------------------------
                        ⊢ Γ × Γ ⊢ s ∶ T × Γ ⊢ t ∶ T × Γ ⊢ T
  ty-eq⇒env-ty-wf-gen (N-[] i ⊢σ)
    with tys⇒env-wf ⊢σ
  ...  | ⊢Γ , ⊢Δ                                    = ⊢Γ , lift-⊢-Se (St-[] ⊢Γ ⊢Δ N ⊢σ) z≤n , N-wf i ⊢Γ , _ , Se-wf _ ⊢Γ
  ty-eq⇒env-ty-wf-gen (Se-[] i ⊢σ)
    with tys⇒env-wf ⊢σ
  ...  | ⊢Γ , ⊢Δ                                    = ⊢Γ , lift-⊢-Se (St-[] ⊢Γ ⊢Δ (Se i) ⊢σ) ℕₚ.≤-refl , Se-wf i ⊢Γ , _ , Se-wf (suc i) ⊢Γ
  ty-eq⇒env-ty-wf-gen (Π-[] ⊢σ ⊢S ⊢T)
    with tys⇒env-wf ⊢σ
  ...  | ⊢Γ , _                                     = ⊢Γ , ⊢T⇒⊢Tσ (Π-wf ⊢S ⊢T) ⊢σ , Π-wf (⊢T⇒⊢Tσ ⊢S ⊢σ) (⊢T⇒⊢Tσ ⊢T (⊢qσ ⊢Γ ⊢S ⊢σ)) , _ , Se-wf _ ⊢Γ
  ty-eq⇒env-ty-wf-gen (Π-cong S≈S′ T≈T′)
    with ty-eq⇒env-ty-wf-gen S≈S′ | ty-eq⇒env-ty-wf-gen T≈T′
  ...  | ⊢Γ , ⊢S , ⊢S′ , _ | _ , ⊢T , ⊢T′ , _       = ⊢Γ , Π-wf ⊢S ⊢T , Π-wf ⊢S′ {!!} , _ , Se-wf _ ⊢Γ
  ty-eq⇒env-ty-wf-gen (v-≈ ⊢Γ T∈Γ)                  = ⊢Γ , vlookup ⊢Γ T∈Γ , vlookup ⊢Γ T∈Γ , ∈!⇒ty-wf ⊢Γ T∈Γ
  ty-eq⇒env-ty-wf-gen (ze-≈ ⊢Γ)                     = ⊢Γ , ze-I ⊢Γ , ze-I ⊢Γ , zero , N-wf 0 ⊢Γ
  ty-eq⇒env-ty-wf-gen (su-cong s≈t)
    with ty-eq⇒env-ty-wf-gen s≈t
  ...  | ⊢Γ , ⊢s , ⊢t , _                           = ⊢Γ , su-I ⊢s , su-I ⊢t , _ , N-wf 0 ⊢Γ
  ty-eq⇒env-ty-wf-gen (rec-cong T≈T′ s≈s′ u≈u′ t≈t′)
    with ty-eq⇒env-ty-wf-gen T≈T′
       | ty-eq⇒env-ty-wf-gen s≈s′
       | ty-eq⇒env-ty-wf-gen u≈u′
       | ty-eq⇒env-ty-wf-gen t≈t′
  ...  | ⊢NΓ , ⊢T , ⊢T′ , _
       | ⊢Γ  , ⊢s , ⊢s′ , _
       | _   , ⊢u , ⊢u′ , _
       | _   , ⊢t , ⊢t′ , _                         = ⊢Γ , N-E ⊢T ⊢s ⊢u ⊢t
                                                         , conv (N-E ⊢T′ (conv ⊢s′ (_ , ⊢≈⇒⊢≈σ T≈T′ (S-, (S-I ⊢Γ) (N-wf 0 ⊢Γ) (conv (ze-I ⊢Γ) (_ , ≈-sym (N-[] 0 (S-I ⊢Γ)))))))
                                                                         (conv {!⊢u′!} (_ , ⊢≈⇒⊢≈σ T≈T′ (S-, (S-∘ (S-↑ ⊢T′NΓ) (S-↑ ⊢NΓ)) (N-wf 0 ⊢Γ) (conv (su-I (v1-St ⊢T′NΓ N)) (_ , ≈-sym (N-[] 0 (S-∘ (S-↑ ⊢T′NΓ) (S-↑ ⊢NΓ))))))))
                                                                         ⊢t′)
                                                                (_ , ≈-conv ([]-cong (,-cong (N-wf 0 ⊢Γ) (I-≈ ⊢Γ) (≈-conv (≈-sym t≈t′) (_ , ≈-sym (N-[] 0 (S-I ⊢Γ))))) (≈-sym T≈T′))
                                                                            (_ , Se-[] _ (S-, (S-I ⊢Γ) (N-wf 0 ⊢Γ) (conv ⊢t′ (_ , ≈-sym (N-[] 0 (S-I ⊢Γ)))))))
                                                         , _ , ⊢T⇒⊢Tσ ⊢T (S-, (S-I ⊢Γ) (N-wf 0 ⊢Γ) (conv ⊢t (_ , ≈-sym (N-[] 0 (S-I ⊢Γ)))))
    where ⊢T′NΓ                                     = ⊢∷ ⊢NΓ ⊢T′
  ty-eq⇒env-ty-wf-gen (Λ-cong s≈t)
    with ty-eq⇒env-ty-wf-gen s≈t
  ...  | ⊢∷ ⊢Γ ⊢S , ⊢s , ⊢t , _ , ⊢T                = ⊢Γ , Λ-I ⊢s , Λ-I ⊢t , _ , Π-wf (lift-⊢-Se ⊢S (ℕₚ.m≤m⊔n _ _)) (lift-⊢-Se ⊢T (ℕₚ.m≤n⊔m _ _))
  ty-eq⇒env-ty-wf-gen ($-cong r≈r′ s≈s′)
    with ty-eq⇒env-ty-wf-gen r≈r′ | ty-eq⇒env-ty-wf-gen s≈s′
  ...  | ⊢Γ , ⊢r , ⊢r′ , _ , ⊢Π | _ , ⊢s , ⊢s′ , _ , ⊢S
       with inv-Π-wf ⊢Π
  ...     | _ , ⊢T                                  = ⊢Γ
                                                    , Λ-E ⊢r ⊢s
                                                    , conv (Λ-E ⊢r′ ⊢s′) (_ , []-cong-St ⊢Γ (⊢∷ ⊢Γ ⊢S) (Se _) I,s′ (≈-refl ⊢T) (,-cong ⊢S (I-≈ ⊢Γ) (≈-conv (≈-sym s≈s′) (_ , ≈-sym ([I] ⊢S)))))
                                                    , _ , ⊢T⇒⊢Tσ ⊢T I,s
    where I,s′ = S-, (S-I ⊢Γ) ⊢S (conv ⊢s′ (_ , ≈-sym ([I] ⊢S)))
          I,s  = S-, (S-I ⊢Γ) ⊢S (conv ⊢s (_ , ≈-sym ([I] ⊢S)))
  ty-eq⇒env-ty-wf-gen ([]-cong σ≈σ′ s≈t)
    with subst-eq⇒env-subst-wf-gen σ≈σ′ | ty-eq⇒env-ty-wf-gen s≈t
  ...  | ⊢Γ , ⊢σ , ⊢σ′ , _ | ⊢Δ , ⊢t , ⊢t′ , _ , ⊢T = ⊢Γ , t[σ] ⊢t ⊢σ , conv (t[σ] ⊢t′ ⊢σ′) (_ , ⊢≈⇒⊢≈σ′ (≈-refl ⊢T) (S-≈-sym σ≈σ′) ⊢σ′) , _ , ⊢T⇒⊢Tσ ⊢T ⊢σ
  ty-eq⇒env-ty-wf-gen (ze-[] ⊢σ)
    with tys⇒env-wf ⊢σ
  ...  | ⊢Γ , ⊢Δ                                    = ⊢Γ , t[σ]-St ⊢Γ ⊢Δ N (ze-I ⊢Δ) ⊢σ , ze-I ⊢Γ , _ , N-wf 0 ⊢Γ
  ty-eq⇒env-ty-wf-gen (su-[] ⊢σ ⊢t)
    with tys⇒env-wf ⊢σ | ty⇒env-ty-wf ⊢t
  ...  | ⊢Γ , _ | ⊢Δ , _                            = ⊢Γ , t[σ]-St ⊢Γ ⊢Δ N (su-I ⊢t) ⊢σ , su-I (t[σ]-St ⊢Γ ⊢Δ N ⊢t ⊢σ) , _ , N-wf 0 ⊢Γ
  ty-eq⇒env-ty-wf-gen (Λ-[] ⊢σ ⊢t)
    with tys⇒env-wf ⊢σ | ty⇒env-ty-wf ⊢t
  ... | ⊢Γ , _ | ⊢∷ ⊢Δ ⊢S , _ , ⊢T                  = ⊢Γ
                                                    , t[σ] (Λ-I ⊢t) ⊢σ
                                                    , conv (Λ-I (t[σ] ⊢t (⊢qσ ⊢Γ ⊢S ⊢σ))) (_ , ≈-sym (Π-[] ⊢σ (lift-⊢-Se ⊢S (ℕₚ.m≤m⊔n _ _)) (lift-⊢-Se ⊢T (ℕₚ.m≤n⊔m _ _))))
                                                    , _ , ⊢T⇒⊢Tσ (Π-wf (lift-⊢-Se ⊢S (ℕₚ.m≤m⊔n _ _)) (lift-⊢-Se ⊢T (ℕₚ.m≤n⊔m _ _))) ⊢σ
  ty-eq⇒env-ty-wf-gen ($-[] ⊢σ ⊢r ⊢s)
    with tys⇒env-wf ⊢σ | ty⇒env-ty-wf ⊢r | ty⇒env-ty-wf ⊢s
  ...  | ⊢Γ , _  | ⊢Δ , _ , ⊢Π | _ , _ , ⊢S
       with inv-Π-wf ⊢Π
  ...     | _ , ⊢T                                  = ⊢Γ
                                                    , conv (t[σ] (Λ-E ⊢r ⊢s) ⊢σ)
                                                           (_ , [|∘]-cong (⊢∷ ⊢Δ ⊢S) ⊢σ ⊢s ⊢T)
                                                    , conv (Λ-E (conv (t[σ] ⊢r ⊢σ) (_ , Π-[] ⊢σ (lift-⊢-Se ⊢S (ℕₚ.m≤m⊔n _ _)) (lift-⊢-Se ⊢T (ℕₚ.m≤n⊔m _ _)))) (t[σ] ⊢s ⊢σ))
                                                           (_ , [q∘]-cong ⊢Γ (⊢∷ ⊢Δ ⊢S) ⊢σ (t[σ] ⊢s ⊢σ) ⊢T)
                                                    , _ , ⊢T⇒⊢Tσ ⊢T (S-, ⊢σ ⊢S (t[σ] ⊢s ⊢σ))

  ty-eq⇒env-ty-wf-gen (rec-[] ⊢σ ⊢T ⊢s ⊢r ⊢t)
    with tys⇒env-wf ⊢σ
  ...  | ⊢Γ , ⊢Δ                                    = ⊢Γ
                                                    , t[σ] (N-E ⊢T ⊢s ⊢r ⊢t) ⊢σ
                                                    , conv (N-E (⊢T⇒⊢Tσ ⊢T qσ)
                                                                (conv (t[σ] ⊢s ⊢σ) (_ , ≈-trans ([∘]-cong ⊢NΔ (S-I ⊢Δ) ⊢σ (conv (ze-I ⊢Δ) (_ , ≈-sym ([I] (N-wf 0 ⊢Δ)))) ⊢T (≈-refl ⊢T))
                                                                                        (≈-trans ([]-cong-Se (S-, (S-∘ ⊢σ (S-I ⊢Δ)) (N-wf 0 ⊢Δ) (conv (t[σ] (ze-I ⊢Δ) ⊢σ) (_ , ≈-trans (St-[]≈ ⊢Γ ⊢Δ N ⊢σ) (≈-sym (St-[]≈ ⊢Γ ⊢Δ N (S-∘ ⊢σ (S-I ⊢Δ)))))))
                                                                                                             (≈-refl ⊢T)
                                                                                                             (,-cong (N-wf 0 ⊢Δ) (I-∘ ⊢σ) (≈-conv (ze-[] ⊢σ) (_ , ≈-sym (St-[]≈ ⊢Γ ⊢Δ N (S-∘ ⊢σ (S-I ⊢Δ)))))))
                                                                                                 (≈-sym ([q∘]-cong ⊢Γ ⊢NΔ ⊢σ (conv (ze-I ⊢Γ) (_ , ≈-sym (N-[] 0 ⊢σ))) ⊢T)))))
                                                                (conv (t[σ] ⊢r (⊢qσ ⊢NΓ ⊢T qσ))
                                                                      (_ , rec-su-T[σ] ⊢Δ ⊢T ⊢Γ ⊢σ))
                                                                (t∶N⇒tσ∶N ⊢t ⊢σ))
                                                           (_ , ≈-trans ([q∘]-cong ⊢Γ ⊢NΔ ⊢σ (t[σ] ⊢t ⊢σ) ⊢T)
                                                                        (≈-sym ([|∘]-cong ⊢NΔ ⊢σ ⊢t ⊢T)))
                                                    , _ , ⊢T⇒⊢Tσ (⊢T⇒⊢Tσ ⊢T (I-, ⊢Δ (N-wf 0 ⊢Δ) ⊢t)) ⊢σ
    where ⊢NΓ   = ⊢∷ ⊢Γ (N-wf 0 ⊢Γ)
          ⊢NΔ   = ⊢∷ ⊢Δ (N-wf 0 ⊢Δ)
          qσ    = S-, (S-∘ (S-↑ ⊢NΓ) ⊢σ) (N-wf 0 ⊢Δ) (conv (vlookup ⊢NΓ here) (_ , ≈-trans (St-[]≈ ⊢NΓ ⊢Γ N (S-↑ ⊢NΓ)) (≈-sym (St-[]≈ ⊢NΓ ⊢Δ N (S-∘ (S-↑ ⊢NΓ) ⊢σ)))))
          I,ze  = S-, (S-I ⊢Δ) (N-wf 0 ⊢Δ) (conv (ze-I ⊢Δ) (_ , ≈-sym ([I] (N-wf 0 ⊢Δ))))
          I,ze′ = S-, (S-I ⊢Γ) (N-wf 0 ⊢Γ) (conv (ze-I ⊢Γ) (_ , ≈-sym ([I] (N-wf 0 ⊢Γ))))
  ty-eq⇒env-ty-wf-gen (rec-β-ze ⊢T ⊢t ⊢r)
    with ty⇒env-ty-wf ⊢t
  ...  | ⊢Γ , _                                     = ⊢Γ , N-E ⊢T ⊢t ⊢r (ze-I ⊢Γ) , ⊢t , _ , ⊢T⇒⊢Tσ ⊢T (S-, (S-I ⊢Γ) (N-wf 0 ⊢Γ) (conv (ze-I ⊢Γ) (_ , ≈-sym ([I] (N-wf 0 ⊢Γ)))))
  ty-eq⇒env-ty-wf-gen (rec-β-su ⊢T ⊢s ⊢r ⊢t)
    with ty⇒env-ty-wf ⊢t | ty⇒env-ty-wf ⊢r
  ...  | ⊢Γ , _ | ⊢TNΓ , _                          = ⊢Γ , N-E ⊢T ⊢s ⊢r (su-I ⊢t)
                                                    , conv (t[σ] ⊢r (S-, (I-, ⊢Γ (N-wf 0 ⊢Γ) ⊢t) ⊢T ⊢rec))
                                                           (_ , ≈-sym (≈-trans ([]-cong-Se (S-, (S-I ⊢Γ) (N-wf 0 ⊢Γ) (conv (su-I ⊢t) (_ , ≈-sym (N-[] 0 (S-I ⊢Γ))))) (≈-refl ⊢T)
                                                                                           (S-≈-sym helper))
                                                                               (T-[∘] (S-, (I-, ⊢Γ (N-wf 0 ⊢Γ) ⊢t) ⊢T ⊢rec) (S-, (S-∘ (S-↑ ⊢TNΓ) (S-↑ ⊢NΓ)) (N-wf 0 ⊢Γ) ⊢suv1) ⊢T)))
                                                    , _ , ⊢T⇒⊢Tσ ⊢T (S-, (S-I ⊢Γ) (N-wf 0 ⊢Γ) (conv (su-I ⊢t) N[I]))
    where ⊢NΓ    = ⊢∷ ⊢Γ (N-wf 0 ⊢Γ)
          ⊢suv1  = conv (su-I (v1-St ⊢TNΓ N)) (_ , ≈-sym (N-[] 0 (S-∘ (S-↑ ⊢TNΓ) (S-↑ ⊢NΓ))))
          N[I]   = _ , ≈-sym ([I] (N-wf 0 ⊢Γ))
          ⊢rec   = N-E ⊢T ⊢s ⊢r ⊢t
          ⊢It    = S-, (S-I ⊢Γ) (N-wf 0 ⊢Γ) (conv ⊢t N[I])
          ⊢Itr   = S-, ⊢It ⊢T ⊢rec
          helper = begin
            ((↑ ∘ ↑) , su (v 1)) ∘ ((I , _) , rec _ _ _ _)
              ≈⟨ ,-ext′ ⊢NΓ (S-∘ (S-↑ ⊢TNΓ) (S-↑ ⊢NΓ)) ⊢Itr ⊢suv1 ⟩
            (↑ ∘ ↑ ∘ ((I , _) , rec _ _ _ _)) , (su (v 1) [ (I , _) , rec _ _ _ _ ])
              ≈⟨ ,-cong (N-wf 0 ⊢Γ) (∘-assoc (S-↑ ⊢NΓ) (S-↑ ⊢TNΓ) ⊢Itr) (≈-conv (su-[] ⊢Itr (v1-St ⊢TNΓ N)) (_ , ≈-sym (N-[] 0 (S-∘ ⊢Itr (S-∘ (S-↑ ⊢TNΓ) (S-↑ ⊢NΓ)))))) ⟩
            (↑ ∘ (↑ ∘ ((I , _) , rec _ _ _ _))) , su (v 1 [ (I , _) , rec _ _ _ _ ])
              ≈⟨ ,-cong (N-wf 0 ⊢Γ) (∘-cong (↑-∘-, ⊢It ⊢T ⊢rec) (↑-≈ ⊢NΓ))
                                    (≈-conv (su-cong (≈-conv ([,]-v-su ⊢It ⊢T ⊢rec here) (_ , ≈-trans (≈-sym (T-[∘] ⊢It (S-↑ ⊢NΓ) (N-wf 0 ⊢Γ))) (N-[] 0 (S-∘ ⊢It (S-↑ ⊢NΓ))))))
                                                     (_ , ≈-sym (N-[] 0 (S-∘ (S-∘ ⊢Itr (S-↑ ⊢TNΓ)) (S-↑ ⊢NΓ))))) ⟩
            (↑ ∘ (I , _)) , su (v 0 [ I , _ ])
              ≈⟨ ,-cong (N-wf 0 ⊢Γ)
                        (↑-∘-, (S-I ⊢Γ) (N-wf 0 ⊢Γ) (conv ⊢t N[I]))
                        (≈-conv (su-cong (≈-conv ([,]-v-ze (S-I ⊢Γ) (N-wf 0 ⊢Γ) (conv ⊢t N[I])) (_ , N-[] 0 (S-I ⊢Γ))))
                                (_ , ≈-sym (N-[] 0 (S-∘ ⊢It (S-↑ ⊢NΓ))))) ⟩
            I , su _
              ∎
            where open TRS
  ty-eq⇒env-ty-wf-gen (Λ-β ⊢t ⊢s)
    with ty⇒env-ty-wf ⊢t | ty⇒env-ty-wf ⊢s
  ...  | _ , _ , ⊢T | ⊢Γ , _ , ⊢S                   = ⊢Γ , Λ-E (Λ-I ⊢t) ⊢s , t[σ] ⊢t (I-, ⊢Γ ⊢S ⊢s) , _ , ⊢T⇒⊢Tσ ⊢T (I-, ⊢Γ ⊢S ⊢s)
  ty-eq⇒env-ty-wf-gen (Λ-η ⊢s)
    with ty⇒env-ty-wf ⊢s
  ...  | ⊢Γ , _ , ⊢Π
       with inv-Π-wf ⊢Π | inv-Π-wf′ ⊢Π
  ...     | _ , ⊢T      | _ , ⊢S                    = ⊢Γ
                                                    , ⊢s
                                                    , Λ-I (conv (Λ-E ([]-Π ⊢s (S-↑ ⊢SΓ) ⊢Π) ⊢v0)
                                                                (_ , ≈-trans ([q∘]-cong ⊢SΓ ⊢SΓ (S-↑ ⊢SΓ) ⊢v0 ⊢T)
                                                                     (≈-trans (≈-sym ([]-cong-Se (S-I (⊢∷ ⊢Γ ⊢S)) (≈-refl ⊢T) (I-ext (⊢∷ ⊢Γ ⊢S))))
                                                                              ([I] ⊢T))))
                                                    , _ , ⊢Π
    where ⊢SΓ = ⊢∷ ⊢Γ ⊢S
          ⊢v0 = vlookup ⊢SΓ here
  ty-eq⇒env-ty-wf-gen ([I] ⊢t)
    with ty⇒env-ty-wf ⊢t
  ...  | ⊢Γ , _ , ⊢T                                = ⊢Γ , conv (t[σ] ⊢t (S-I ⊢Γ)) (_ , [I] ⊢T) , ⊢t , _ , ⊢T
  ty-eq⇒env-ty-wf-gen (↑-lookup (⊢∷ ⊢Γ ⊢S) T∈Γ)     = ⊢∷ ⊢Γ ⊢S , t[σ] (vlookup ⊢Γ T∈Γ) (S-↑ (⊢∷ ⊢Γ ⊢S)) , vlookup (⊢∷ ⊢Γ ⊢S) (there T∈Γ) , _ , ⊢T⇒⊢Tσ ⊢T (S-↑ (⊢∷ ⊢Γ ⊢S))
    where ⊢T = proj₂ (⊢∈⇒ty-wf ⊢Γ T∈Γ)
  ty-eq⇒env-ty-wf-gen ([∘] ⊢τ ⊢σ ⊢t)
    with tys⇒env-wf ⊢τ | ty⇒env-ty-wf ⊢t
  ...  | ⊢Γ , ⊢Γ′ | _ , _ , ⊢T                      = ⊢Γ
                                                    , t[σ] ⊢t (S-∘ ⊢τ ⊢σ)
                                                    , conv (t[σ] (t[σ] ⊢t ⊢σ) ⊢τ) (_ , ≈-sym (T-[∘] ⊢τ ⊢σ ⊢T))
                                                    , _ , ⊢T⇒⊢Tσ ⊢T (S-∘ ⊢τ ⊢σ)
  ty-eq⇒env-ty-wf-gen ([,]-v-ze ⊢σ ⊢S ⊢t)
    with tys⇒env-wf ⊢σ
  ...  | ⊢Γ , ⊢Δ                                    = ⊢Γ
                                                    , conv (t[σ] (vlookup (⊢∷ ⊢Δ ⊢S) here) (S-, ⊢σ ⊢S ⊢t))
                                                           (_ , ≈-trans (≈-sym (T-[∘] (S-, ⊢σ ⊢S ⊢t) (S-↑ (⊢∷ ⊢Δ ⊢S)) ⊢S))
                                                                        (≈-sym ([]-cong-Se ⊢σ (≈-refl ⊢S) (S-≈-sym (↑-∘-, ⊢σ ⊢S ⊢t)))))
                                                    , ⊢t
                                                    , _ , ⊢T⇒⊢Tσ ⊢S ⊢σ
  ty-eq⇒env-ty-wf-gen ([,]-v-su ⊢σ ⊢S ⊢s T∈Δ)
    with tys⇒env-wf ⊢σ
  ...  | ⊢Γ , ⊢Δ                                    = ⊢Γ
                                                    , conv (t[σ] (vlookup (⊢∷ ⊢Δ ⊢S) (there T∈Δ)) (S-, ⊢σ ⊢S ⊢s))
                                                           (_ , ≈-trans (≈-sym (T-[∘] (S-, ⊢σ ⊢S ⊢s) (S-↑ (⊢∷ ⊢Δ ⊢S)) ⊢T)) (⊢≈⇒⊢≈σ′ (≈-refl ⊢T) (↑-∘-, ⊢σ ⊢S ⊢s) (S-∘ (S-, ⊢σ ⊢S ⊢s) (S-↑ (⊢∷ ⊢Δ ⊢S)))))
                                                    , t[σ] (vlookup ⊢Δ T∈Δ) ⊢σ
                                                    , _ , ⊢T⇒⊢Tσ ⊢T ⊢σ
    where ⊢T = proj₂ (⊢∈⇒ty-wf ⊢Δ T∈Δ)
  ty-eq⇒env-ty-wf-gen (≈-cumu s≈t)
    with ty-eq⇒env-ty-wf-gen s≈t
  ...  | ⊢Γ , ⊢s , ⊢t , _                           = ⊢Γ , cumu ⊢s , cumu ⊢t , _ , Se-wf _ ⊢Γ
  ty-eq⇒env-ty-wf-gen (≈-conv s≈t eq@(_ , S≈T))
    with ty-eq⇒env-ty-wf-gen s≈t | ty-eq⇒env-ty-wf-gen S≈T
  ...  | ⊢Γ , ⊢s , ⊢t , _ | _ , _ ,  ⊢T , _         = ⊢Γ , conv ⊢s eq , conv ⊢t eq , _ , ⊢T
  ty-eq⇒env-ty-wf-gen (≈-sym s≈t)
    with ty-eq⇒env-ty-wf-gen s≈t
  ...  | ⊢Γ , ⊢s , ⊢t , ⊢T                          = ⊢Γ , ⊢t , ⊢s , ⊢T
  ty-eq⇒env-ty-wf-gen (≈-trans s≈t′ t′≈t)
    with ty-eq⇒env-ty-wf-gen s≈t′ | ty-eq⇒env-ty-wf-gen t′≈t
  ...  | _ , ⊢s , _ , _ | ⊢Γ , _ , ⊢t , ⊢T          = ⊢Γ , ⊢s , ⊢t , ⊢T

  subst-eq⇒env-subst-wf-gen : Γ ⊢s σ ≈ τ ∶ Δ →
                              -----------------------------------
                              ⊢ Γ × Γ ⊢s σ ∶ Δ × Γ ⊢s τ ∶ Δ × ⊢ Δ
  subst-eq⇒env-subst-wf-gen (↑-≈ ⊢SΔ@(⊢∷ ⊢Δ _))  = ⊢SΔ , S-↑ ⊢SΔ , S-↑ ⊢SΔ , ⊢Δ
  subst-eq⇒env-subst-wf-gen (I-≈ ⊢Γ)             = ⊢Γ , S-I ⊢Γ , S-I ⊢Γ , ⊢Γ
  subst-eq⇒env-subst-wf-gen (∘-cong τ≈τ′ σ≈σ′)
    with subst-eq⇒env-subst-wf-gen τ≈τ′ | subst-eq⇒env-subst-wf-gen σ≈σ′
  ...  | ⊢Γ , ⊢τ , ⊢τ′ , _ | ⊢Γ′ , ⊢σ , ⊢σ′ , ⊢Δ = ⊢Γ , S-∘ ⊢τ ⊢σ , S-∘ ⊢τ′ ⊢σ′ , ⊢Δ
  subst-eq⇒env-subst-wf-gen (,-cong ⊢S σ≈τ s≈s′)
    with subst-eq⇒env-subst-wf-gen σ≈τ | ty-eq⇒env-ty-wf-gen s≈s′
  ...  | ⊢Γ , ⊢σ , ⊢σ′ , ⊢Δ | _ , ⊢s , ⊢s′ , ⊢Sσ = ⊢Γ , S-, ⊢σ ⊢S ⊢s , S-, ⊢σ′ ⊢S (conv ⊢s′ (_ , ⊢≈⇒⊢≈σ′ (≈-refl ⊢S) σ≈τ ⊢σ)) , ⊢∷ ⊢Δ ⊢S
  subst-eq⇒env-subst-wf-gen (↑-∘-, ⊢τ ⊢S ⊢s)
    with tys⇒env-wf ⊢τ
  ...  | ⊢Γ , ⊢Δ                                 = ⊢Γ , S-∘ (S-, ⊢τ ⊢S ⊢s) (S-↑ (⊢∷ ⊢Δ ⊢S)) , ⊢τ , ⊢Δ
  subst-eq⇒env-subst-wf-gen (I-∘ ⊢τ)
    with tys⇒env-wf ⊢τ
  ...  | ⊢Γ , ⊢Δ                                 = ⊢Γ , S-∘ ⊢τ (S-I ⊢Δ) , ⊢τ , ⊢Δ
  subst-eq⇒env-subst-wf-gen (∘-I ⊢τ)
    with tys⇒env-wf ⊢τ
  ...  | ⊢Γ , ⊢Δ                                 = ⊢Γ , S-∘ (S-I ⊢Γ) ⊢τ , ⊢τ , ⊢Δ
  subst-eq⇒env-subst-wf-gen (∘-assoc ⊢σ ⊢σ′ ⊢σ″)
   with tys⇒env-wf ⊢σ | tys⇒env-wf ⊢σ″
  ...  | ⊢Γ′ , ⊢Δ | ⊢Γ , ⊢Γ″                     = ⊢Γ , S-∘ ⊢σ″ (S-∘ ⊢σ′ ⊢σ) , S-∘ (S-∘ ⊢σ″ ⊢σ′) ⊢σ , ⊢Δ
  subst-eq⇒env-subst-wf-gen (,-ext ⊢σ)
    with tys⇒env-wf ⊢σ
  ...  | ⊢Γ , ⊢∷ ⊢Δ ⊢S                           = ⊢Γ , ⊢σ , S-, (S-∘ ⊢σ (S-↑ (⊢∷ ⊢Δ ⊢S))) ⊢S (conv (t[σ] (vlookup (⊢∷ ⊢Δ ⊢S) here) ⊢σ) (_ , ≈-sym (T-[∘] ⊢σ (S-↑ (⊢∷ ⊢Δ ⊢S)) ⊢S))) , ⊢∷ ⊢Δ ⊢S
  subst-eq⇒env-subst-wf-gen (S-≈-sym σ≈τ)
    with subst-eq⇒env-subst-wf-gen σ≈τ
  ...  | ⊢Γ , ⊢τ , ⊢σ , ⊢Δ                       = ⊢Γ , ⊢σ , ⊢τ , ⊢Δ
  subst-eq⇒env-subst-wf-gen (S-≈-trans σ≈σ′ σ′≈τ)
    with subst-eq⇒env-subst-wf-gen σ≈σ′ | subst-eq⇒env-subst-wf-gen σ′≈τ
  ...  | _ , ⊢σ , _ , _ | ⊢Γ , _ , ⊢τ , ⊢Δ       = ⊢Γ , ⊢σ , ⊢τ , ⊢Δ
