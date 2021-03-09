{-# OPTIONS --without-K --safe #-}

module PTT.Statics.Inv where

open import Lib
open import PTT.Statics
open import PTT.Statics.Misc
open import PTT.Statics.Complement
open import PTT.Statics.Stable
open import PTT.Statics.EnvSubst
open import PTT.Statics.RecHelper

import Data.Nat.Properties as ℕₚ
open import Relation.Binary.Construct.Closure.ReflexiveTransitive

mutual
  ty⇒env-ty-wf : Γ ⊢ t ∶ T →
                 ------------
                 ⊢ Γ × Γ ⊢ T
  ty⇒env-ty-wf (N-wf i ⊢Γ)       = ⊢Γ , suc i , Se-wf ⊢Γ ℕₚ.≤-refl
  ty⇒env-ty-wf (Se-wf ⊢Γ _)      = ⊢Γ , _ , Se-wf ⊢Γ ℕₚ.≤-refl
  ty⇒env-ty-wf (Π-wf ⊢S ⊢T _ _)
    with ty⇒env-ty-wf ⊢S
  ...  | ⊢Γ , _ , _              = ⊢Γ , _ , Se-wf ⊢Γ ℕₚ.≤-refl
  ty⇒env-ty-wf (vlookup ⊢Γ T∈Γ)  = ⊢Γ , ∈!⇒ty-wf ⊢Γ T∈Γ
  ty⇒env-ty-wf (ze-I ⊢Γ)         = ⊢Γ , 0 , N-wf 0 ⊢Γ
  ty⇒env-ty-wf (su-I t)          = ty⇒env-ty-wf t
  ty⇒env-ty-wf (N-E ⊢Π ⊢s ⊢r ⊢t)
    with ty⇒env-ty-wf ⊢Π
  ...  | ⊢Γ , _                  = ⊢Γ , _ , conv (Λ-E ⊢Π ⊢t) (≈-≲ (Se-[] (S-, ⊢I (N-wf 0 ⊢Γ) (conv ⊢t (≈-≲ (≈-sym (N-[] 0 ⊢I))))) ℕₚ.≤-refl))
    where ⊢I = S-I ⊢Γ
  ty⇒env-ty-wf (Λ-I ⊢t) with ty⇒env-ty-wf ⊢t
  ... | ⊢∷ ⊢Γ ⊢S , _ , ⊢T       = ⊢Γ , _ , Π-wf ⊢S ⊢T (ℕₚ.m≤m⊔n _ _) (ℕₚ.n≤m⊔n _ _)
  ty⇒env-ty-wf (Λ-E ⊢r ⊢s)
    with ty⇒env-ty-wf ⊢r | ty⇒env-ty-wf ⊢s
  ...  | ⊢Γ , _ , ⊢Π | _ , _ , ⊢S
       with inv-Π-wf ⊢Π
  ...     | _ , ⊢T               = ⊢Γ , _ , conv (t[σ] ⊢T I,s) (≈-≲ (Se-[] I,s ℕₚ.≤-refl))
    where S[I] = ≈-≲ (≈-sym ([I] ⊢S))
          I,s  = S-, (S-I ⊢Γ) ⊢S (conv ⊢s (≈-≲ (≈-sym ([I] ⊢S))))
  ty⇒env-ty-wf (t[σ] ⊢t ⊢σ)
    with ty⇒env-ty-wf ⊢t | tys⇒env-wf ⊢σ
  ...  | ⊢Δ , _ , ⊢T | ⊢Γ , _    = ⊢Γ , _ , conv (t[σ] ⊢T ⊢σ) (≈-≲ (Se-[] ⊢σ ℕₚ.≤-refl))
  ty⇒env-ty-wf (conv ⊢t S≲T)
    with ty⇒env-ty-wf ⊢t | ≲⇒env-ty-wf S≲T
  ...  | ⊢Γ , _ | _ , i , _ , ⊢T = ⊢Γ , _ , ⊢T

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
  tys⇒env-wf (S-conv Δ′≲Δ ⊢σ)
    with tys⇒env-wf ⊢σ | ≲env⇒env-wf Δ′≲Δ
  ...  | ⊢Γ , _        | _ , ⊢Δ  = ⊢Γ , ⊢Δ

  ≲env⇒env-wf : ⊢ Γ ≲ Δ →
               ------------
               ⊢ Γ × ⊢ Δ
  ≲env⇒env-wf ≈[]                          = ⊢[] , ⊢[]
  ≲env⇒env-wf (≈∷ Γ≲Δ S≲T _)
    with ≲env⇒env-wf Γ≲Δ | ≲⇒env-ty-wf S≲T
  ...  | ⊢Γ , ⊢Δ         | _ , _ , ⊢S , ⊢T = ⊢∷ ⊢Γ (ty-env-substs Γ≲Δ ⊢S) , ⊢∷ ⊢Δ ⊢T

  ≲⇒env-ty-wf : Γ ⊢ S ≲ T →
                ------------------------------------------
                ⊢ Γ × ∃ λ i → Γ ⊢ S ∶ Se i × Γ ⊢ T ∶ Se i
  ≲⇒env-ty-wf (Se-≲ ⊢Γ i≤j) = ⊢Γ , _ , Se-wf ⊢Γ (s≤s i≤j) , Se-wf ⊢Γ ℕₚ.≤-refl
  ≲⇒env-ty-wf (≈-≲ S≈T)
    with ty-eq⇒env-ty-wf-gen S≈T
  ...  | ⊢Γ , ⊢S , ⊢T , _   = ⊢Γ , _ , ⊢S , ⊢T


  ty-eq⇒env-ty-wf-gen : Γ ⊢ s ≈ t ∶ T →
                        -----------------------------------
                        ⊢ Γ × Γ ⊢ s ∶ T × Γ ⊢ t ∶ T × Γ ⊢ T
  ty-eq⇒env-ty-wf-gen (N-[] i ⊢σ)
    with tys⇒env-wf ⊢σ
  ...  | ⊢Γ , ⊢Δ                              = ⊢Γ
                                              , conv (t[σ] (N-wf i ⊢Δ) ⊢σ) (≈-≲ (Se-[] ⊢σ ℕₚ.≤-refl))
                                              , N-wf i ⊢Γ
                                              , suc i , Se-wf ⊢Γ ℕₚ.≤-refl
  ty-eq⇒env-ty-wf-gen (Se-[] ⊢σ i<j)
    with tys⇒env-wf ⊢σ
  ...  | ⊢Γ , ⊢Δ                              = ⊢Γ
                                              , conv (t[σ] (Se-wf ⊢Δ i<j) ⊢σ) (≈-≲ (Se-[] ⊢σ ℕₚ.≤-refl))
                                              , Se-wf ⊢Γ i<j
                                              , _ , Se-wf ⊢Γ ℕₚ.≤-refl
  ty-eq⇒env-ty-wf-gen (Π-[] ⊢σ ⊢S ⊢T i≤k j≤k)
    with tys⇒env-wf ⊢σ
  ...  | ⊢Γ , ⊢Δ                              = ⊢Γ
                                              , conv (t[σ] (Π-wf ⊢S ⊢T i≤k j≤k) ⊢σ) Sek[]
                                              , Π-wf ⊢S[σ] (conv (t[σ] ⊢T qσ) Sej[]) i≤k j≤k
                                              , _ , Se-wf ⊢Γ ℕₚ.≤-refl
    where Sek[] = ≈-≲ (Se-[] ⊢σ ℕₚ.≤-refl)
          Sei[] = ≈-≲ (Se-[] ⊢σ ℕₚ.≤-refl)
          ⊢S[σ] = conv (t[σ] ⊢S ⊢σ) Sei[]
          ⊢SΓ   = ⊢∷ ⊢Γ ⊢S[σ]
          qσ    = ⊢qσ ⊢Γ ⊢S ⊢σ
          Sej[] = ≈-≲ (Se-[] qσ ℕₚ.≤-refl)
  ty-eq⇒env-ty-wf-gen (Π-cong _ S≈S′ T≈T′ i≤k j≤k)
    with ty-eq⇒env-ty-wf-gen S≈S′ | ty-eq⇒env-ty-wf-gen T≈T′
  ...  | ⊢Γ , ⊢S , ⊢S′ , _ | _ , ⊢T , ⊢T′ , _ = ⊢Γ
                                              , Π-wf ⊢S ⊢T i≤k j≤k
                                              , Π-wf ⊢S′ (ty-env-subst {Δ = []} (≈-≲ (≈-sym S≈S′)) ⊢S′ ⊢T′ refl) i≤k j≤k
                                              , _ , Se-wf ⊢Γ ℕₚ.≤-refl
  ty-eq⇒env-ty-wf-gen (v-≈ ⊢Γ T∈Γ)            = ⊢Γ , vlookup ⊢Γ T∈Γ , vlookup ⊢Γ T∈Γ , ⊢∈⇒ty-wf ⊢Γ T∈Γ
  ty-eq⇒env-ty-wf-gen (ze-≈ ⊢Γ)               = ⊢Γ , ze-I ⊢Γ , ze-I ⊢Γ , _ , N-wf 0 ⊢Γ
  ty-eq⇒env-ty-wf-gen (su-cong s≈t)
    with ty-eq⇒env-ty-wf-gen s≈t
  ...  | ⊢Γ , ⊢t , ⊢t′ , _                    = ⊢Γ , su-I ⊢t , su-I ⊢t′ , 0 , N-wf 0 ⊢Γ
  ty-eq⇒env-ty-wf-gen (rec-cong T≈T″ s≈s′ r≈r′ t≈t′)
    with ty-eq⇒env-ty-wf-gen T≈T″
       | ty-eq⇒env-ty-wf-gen s≈s′
       | ty-eq⇒env-ty-wf-gen r≈r′
       | ty-eq⇒env-ty-wf-gen t≈t′
  ...  | ⊢Γ , ⊢T , ⊢T″ , _
       | _ , ⊢s , ⊢s′ , _
       | _ , ⊢r , ⊢r′ , _
       | _ , ⊢t , ⊢t′ , _                    = ⊢Γ
                                             , N-E ⊢T ⊢s ⊢r ⊢t
                                             , conv (N-E ⊢T″
                                                         (conv ⊢s′ (≈-≲ (≈-conv ($-cong T≈T″ (ze-≈ ⊢Γ))
                                                                                (≈-≲ (Se-[] (S-, (S-I ⊢Γ) ⊢N (conv (ze-I ⊢Γ) (⊢N≲N[I] ⊢Γ)))
                                                                                            ℕₚ.≤-refl)))))
                                                         (conv ⊢r′ (≈-≲ (Π-cong ⊢N
                                                                                (≈-refl ⊢N)
                                                                        (Π-cong ⊢T0
                                                                                (≈-conv ($-cong (≈-conv ([]-cong (↑-≈ ⊢NΓ) T≈T″) (≈-≲ ⊢ΠNS≈))
                                                                                                (v-≈ ⊢NΓ here))
                                                                                        (≈-≲ (iter-[]-Se ⊢NΓ (((I , v 0) , S-, (S-I ⊢NΓ) ⊢N↑
                                                                                                                           (conv (vlookup ⊢NΓ here) (≈-≲ (≈-sym ([I] ⊢N↑))))
                                                                                                                         , ⊢∷ ⊢NΓ ⊢N↑)
                                                                                                             ◅ (q ↑ , ⊢qσ ⊢NΓ (N-wf 0 ⊢Γ) (S-↑ ⊢NΓ) , ⊢NΓ)
                                                                                                             ◅ ε) ℕₚ.≤-refl)))
                                                                                (≈-conv ($-cong (≈-conv ([]-cong (S-≈-refl ⊢↑↑)
                                                                                                                 T≈T″)
                                                                                                        (≈-≲ (≈-conv (≈-trans (Π-[] ⊢↑↑
                                                                                                                                    ⊢N
                                                                                                                                    (Se-wf ⊢NΓ ℕₚ.≤-refl)
                                                                                                                                    _≤_.z≤n
                                                                                                                                    ℕₚ.≤-refl)
                                                                                                                              (Π-cong (⊢T⇒⊢Tσ ⊢N ⊢↑↑)
                                                                                                                                      (N-[] 0 ⊢↑↑)
                                                                                                                                      (Se-[] (⊢qσ ⊢T0NΓ ⊢N ⊢↑↑)
                                                                                                                                             ℕₚ.≤-refl)
                                                                                                                                      _≤_.z≤n
                                                                                                                                      ℕₚ.≤-refl))
                                                                                                                     (Se-≲ ⊢T0NΓ ℕₚ.≤-refl))))
                                                                                                (≈-refl ⊢suv1))
                                                                                        (≈-≲ (Se-[] (S-, (S-I ⊢T0NΓ) (N-wf 0 ⊢T0NΓ) (conv ⊢suv1
                                                                                                                                          (≈-≲ (≈-sym (N-[] 0 (S-I ⊢T0NΓ))))))
                                                                                                    ℕₚ.≤-refl)))
                                                                                ℕₚ.≤-refl ℕₚ.≤-refl)
                                                                                _≤_.z≤n ℕₚ.≤-refl)))
                                                         ⊢t′)
                                                    (≈-≲ (≈-conv ($-cong (≈-sym T≈T″) (≈-sym t≈t′))
                                                                 (≈-≲ (Se-[] (S-, (S-I ⊢Γ) ⊢N
                                                                                  (conv ⊢t′ (≈-≲ (≈-sym (N-[] 0 (S-I ⊢Γ))))))
                                                                             ℕₚ.≤-refl))))
                                             , _ , conv (Λ-E ⊢T ⊢t)
                                                        (≈-≲ (Se-[] (S-, (S-I ⊢Γ) (N-wf 0 ⊢Γ) (conv ⊢t (≈-≲ (≈-sym (N-[] 0 (S-I ⊢Γ)))))) ℕₚ.≤-refl))
    where open TR
          ⊢N≲N[I] : ⊢ Γ → Γ ⊢ N ≲ N [ I ]
          ⊢N≲N[I] ⊢Γ = (≈-≲ (≈-sym (N-[] 0 (S-I ⊢Γ))))
          ⊢N    = N-wf 0 ⊢Γ
          ⊢NΓ   = ⊢∷ ⊢Γ ⊢N
          ⊢ΠNS≈ = Π-[] (S-↑ ⊢NΓ) (N-wf 0 ⊢Γ) (Se-wf ⊢NΓ ℕₚ.≤-refl) _≤_.z≤n ℕₚ.≤-refl
          ⊢N↑   = ⊢T⇒⊢Tσ ⊢N (S-↑ ⊢NΓ)
          ⊢T0   = conv (Λ-E (conv (t[σ] ⊢T (S-↑ ⊢NΓ))
                            (≈-≲ (begin
                              Π N (Se _) [ ↑ ]           ≈⟨ ⊢ΠNS≈ ⟩
                              Π (N [ ↑ ]) (Se _ [ q ↑ ]) ≈!⟨ Π-cong ⊢N↑ (≈-refl ⊢N↑) (Se-[] (⊢qσ ⊢NΓ ⊢N (S-↑ ⊢NΓ)) ℕₚ.≤-refl) _≤_.z≤n ℕₚ.≤-refl ⟩
                              Π (N [ ↑ ]) (Se _)         ∎)))
                            (vlookup ⊢NΓ here))
                       (≈-≲ (Se-[] (S-, (S-I ⊢NΓ)
                                        (N-wf 0 ⊢NΓ)
                                        (conv (vlookup ⊢NΓ here)
                                              (≈-≲ (≈-trans (N-[] 0 (S-↑ ⊢NΓ))
                                                            (≈-sym ([I] (N-wf 0 ⊢NΓ)))))))
                                   ℕₚ.≤-refl))
          ⊢T0NΓ = ⊢∷ (⊢∷ ⊢Γ ⊢N) ⊢T0
          ⊢↑↑   = S-∘ (S-↑ ⊢T0NΓ) (S-↑ ⊢NΓ)
          ⊢suv1 = su-I (conv (vlookup ⊢T0NΓ (there here))
                             (≈-≲ (≈-trans (≈-Se-inter-[] ⊢T0NΓ ((↑ , S-↑ ⊢T0NΓ , ⊢NΓ) ◅ ε) ([]-cong (↑-≈ ⊢T0NΓ) (N-[] 0 (S-↑ ⊢NΓ))))
                                           (N-[] 0 (S-↑ ⊢T0NΓ)))))
  ty-eq⇒env-ty-wf-gen (Λ-cong s≈t)
    with ty-eq⇒env-ty-wf-gen s≈t
  ... | ⊢∷ ⊢Γ ⊢S , ⊢t , ⊢t′ , _ , ⊢T          = ⊢Γ , Λ-I ⊢t , Λ-I ⊢t′ , _ , Π-wf ⊢S ⊢T (ℕₚ.m≤m⊔n _ _) (ℕₚ.n≤m⊔n _ _)
  ty-eq⇒env-ty-wf-gen ($-cong r≈r′ s≈s′)
    with ty-eq⇒env-ty-wf-gen r≈r′ | ty-eq⇒env-ty-wf-gen s≈s′
  ...  | ⊢Γ , ⊢r , ⊢r′ , _ , ⊢Π
       | _ , ⊢s , ⊢s′ , _ , ⊢S
       with inv-Π-wf ⊢Π
  ...     | _ , ⊢T                            = ⊢Γ
                                              , Λ-E ⊢r ⊢s
                                              , conv (Λ-E ⊢r′ ⊢s′)
                                                     (≈-≲ (≈-conv ([]-cong (,-cong ⊢S (I-≈ ⊢Γ) (≈-conv (≈-sym s≈s′) (≈-≲ (≈-sym ([I] ⊢S))))) (≈-refl ⊢T))
                                                                  (≈-≲ (Se-[] I,s′ ℕₚ.≤-refl))))
                                              , _ , ⊢T⇒⊢Tσ ⊢T (S-, (S-I ⊢Γ) ⊢S (conv ⊢s (≈-≲ (≈-sym ([I] ⊢S)))))
    where I,s′ = S-, (S-I ⊢Γ) ⊢S (conv ⊢s′ (≈-≲ (≈-sym ([I] ⊢S))))
  ty-eq⇒env-ty-wf-gen ([]-cong σ≈σ′ t≈t′)
    with ty-eq⇒env-ty-wf-gen t≈t′
  ...  | ⊢Δ , ⊢t , ⊢t′ , _ , ⊢T               = {!!}
  ty-eq⇒env-ty-wf-gen (ze-[] ⊢σ)
    with tys⇒env-wf ⊢σ
  ...  | ⊢Γ , ⊢Δ                              = ⊢Γ , conv (t[σ] (ze-I ⊢Δ) ⊢σ) (≈-≲ (N-[] 0 ⊢σ)) , ze-I ⊢Γ , _ , N-wf 0 ⊢Γ
  ty-eq⇒env-ty-wf-gen (su-[] ⊢σ ⊢t)
    with tys⇒env-wf ⊢σ
  ...  | ⊢Γ , ⊢Δ                              = ⊢Γ
                                              , conv (t[σ] (su-I ⊢t) ⊢σ) (≈-≲ (N-[] 0 ⊢σ))
                                              , su-I (conv (t[σ] ⊢t ⊢σ) (≈-≲ (N-[] 0 ⊢σ)))
                                              , _ , N-wf 0 ⊢Γ
  ty-eq⇒env-ty-wf-gen (Λ-[] ⊢σ ⊢t)
    with tys⇒env-wf ⊢σ | ty⇒env-ty-wf ⊢t
  ...  | ⊢Γ , _  | ⊢∷ ⊢Δ ⊢S , _ , ⊢T          = ⊢Γ
                                              , t[σ] (Λ-I ⊢t) ⊢σ
                                              , conv (Λ-I (t[σ] ⊢t (S-, σ∘↑ ⊢S
                                                                        (conv (vlookup ⊢SσΓ here)
                                                                              (≈-≲ (≈-sym (≈-conv ([∘] (S-↑ ⊢SσΓ) ⊢σ ⊢S)
                                                                                                  (≈-≲ (Se-[] σ∘↑ ℕₚ.≤-refl)))))))))
                                                     (≈-≲ (≈-sym (Π-[] ⊢σ ⊢S ⊢T (ℕₚ.m≤m⊔n _ _) (ℕₚ.n≤m⊔n _ _))))
                                              , _ , ⊢T⇒⊢Tσ (Π-wf ⊢S ⊢T (ℕₚ.m≤m⊔n _ _) (ℕₚ.n≤m⊔n _ _)) ⊢σ
    where ⊢Sσ  = ⊢T⇒⊢Tσ ⊢S ⊢σ
          ⊢SσΓ = ⊢∷ ⊢Γ ⊢Sσ
          σ∘↑  = S-∘ (S-↑ ⊢SσΓ) ⊢σ
  ty-eq⇒env-ty-wf-gen ($-[] ⊢σ ⊢r ⊢s)
    with tys⇒env-wf ⊢σ | ty⇒env-ty-wf ⊢r | ty⇒env-ty-wf ⊢s
  ...  | ⊢Γ , _  | ⊢Δ , _ , ⊢Π | _ , _ , ⊢S
       with inv-Π-wf ⊢Π
  ...     | _ , ⊢T                              = ⊢Γ
                                                , conv (t[σ] (Λ-E ⊢r ⊢s) ⊢σ)
                                                       (≈-≲ ([|∘]-cong (⊢∷ ⊢Δ ⊢S) ⊢σ ⊢s ⊢T))
                                                , conv (Λ-E (conv (t[σ] ⊢r ⊢σ) (≈-≲ (Π-[] ⊢σ ⊢S ⊢T (ℕₚ.m≤m⊔n _ _) (ℕₚ.n≤m⊔n _ _)))) (t[σ] ⊢s ⊢σ))
                                                       (≈-≲ ([q∘]-cong ⊢Γ (⊢∷ ⊢Δ ⊢S) ⊢σ (t[σ] ⊢s ⊢σ) ⊢T))
                                                , _ , ⊢T⇒⊢Tσ ⊢T (S-, ⊢σ ⊢S (t[σ] ⊢s ⊢σ))
  ty-eq⇒env-ty-wf-gen (rec-[] ⊢σ ⊢T ⊢s ⊢r ⊢t)
    with tys⇒env-wf ⊢σ
  ...  | ⊢Γ , ⊢Δ                                = ⊢Γ
                                                , t[σ] (N-E ⊢T ⊢s ⊢r ⊢t) ⊢σ
                                                , conv (N-E (ΠNSe[σ] ⊢Δ ⊢Γ ⊢T ⊢σ)
                                                            (⊢Tze⇒T[σ]ze ⊢Γ ⊢Δ ⊢T ⊢s ⊢σ)
                                                            (conv (t[σ] ⊢r ⊢σ) (≈-≲ (T-rec-su[σ] ⊢Δ ⊢T ⊢Γ ⊢σ)))
                                                            (t∶N⇒tσ∶N ⊢t ⊢σ))
                                                       (≈-≲ (≈-conv (≈-sym ($-[] ⊢σ ⊢T ⊢t)) (≈-≲ (Se-[] (S-, ⊢σ (N-wf 0 ⊢Δ) (t[σ] ⊢t ⊢σ)) ℕₚ.≤-refl))))
                                                , _ , ⊢T⇒⊢Tσ (ΠSe-$ ⊢Δ (N-wf 0 ⊢Δ) ⊢T ⊢t) ⊢σ
  ty-eq⇒env-ty-wf-gen (rec-β-ze ⊢T ⊢t ⊢r)
    with ty⇒env-ty-wf ⊢t
  ...  | ⊢Γ , _                                 = ⊢Γ , N-E ⊢T ⊢t ⊢r (ze-I ⊢Γ) , ⊢t , _ , ΠSe-$ ⊢Γ (N-wf 0 ⊢Γ) ⊢T (ze-I ⊢Γ)
  ty-eq⇒env-ty-wf-gen (rec-β-su ⊢T ⊢s ⊢r ⊢t)
    with ty⇒env-ty-wf ⊢t
  ...  | ⊢Γ , _                                 = ⊢Γ
                                                , N-E ⊢T ⊢s ⊢r (su-I ⊢t)
                                                , conv (Λ-E (conv (Λ-E ⊢r ⊢t) (≈-≲ helper))
                                                            (N-E ⊢T ⊢s ⊢r ⊢t))
                                                       (≈-≲ helper′)
                                                , _ , ΠSe-$ ⊢Γ (N-wf 0 ⊢Γ) ⊢T (su-I ⊢t)
    where ⊢NΓ    = ⊢∷ ⊢Γ (N-wf 0 ⊢Γ)
          ⊢tI    = conv ⊢t (≈-≲ (≈-sym (N-[] 0 (S-I ⊢Γ))))
          I,t    = S-, (S-I ⊢Γ) (N-wf 0 ⊢Γ) ⊢tI
          ⊢T↑    = ΠNSe[σ] ⊢Γ ⊢NΓ ⊢T (S-↑ ⊢NΓ)
          v0∶N   = ⊢v0∶N ⊢NΓ
          ⊢Tv0   = ΠSe-$ ⊢NΓ (N-wf 0 ⊢NΓ) ⊢T↑ v0∶N
          ⊢T0NΓ  = ⊢∷ ⊢NΓ ⊢Tv0
          ⊢↑↑    = S-∘ (S-↑ ⊢T0NΓ) (S-↑ ⊢NΓ)
          ⊢T↑↑   = ΠNSe[σ] ⊢Γ ⊢T0NΓ ⊢T ⊢↑↑
          ⊢v1    = v1-St ⊢T0NΓ N
          ⊢suv1  = su-I ⊢v1
          ⊢Tsuv1 = ΠSe-$ ⊢T0NΓ (N-wf 0 ⊢T0NΓ) ⊢T↑↑ ⊢suv1
          ⊢T0I,t = ⊢T⇒⊢Tσ ⊢Tv0 I,t
          qI,t   = ⊢qσ ⊢Γ ⊢Tv0 I,t
          ⊢T0ItΓ = ⊢∷ ⊢Γ ⊢T0I,t
          ⊢v0′   = conv (vlookup ⊢T0ItΓ here) (≈-≲ (≈-sym ([∘]-St ⊢T0ItΓ ⊢NΓ (Se _) (S-↑ ⊢T0ItΓ) I,t ⊢Tv0)))
          v0It≈  = [,]-v-ze-St ⊢Γ ⊢Γ N (S-I ⊢Γ) ⊢t
          I,t↑   = S-∘ I,t (S-↑ ⊢NΓ)
          ⊢T↑′   = ΠNSe[σ] ⊢Γ ⊢T0ItΓ ⊢T (S-↑ ⊢T0ItΓ)
          ⊢rec   = N-E ⊢T ⊢s ⊢r ⊢t
          ⊢Tt    = ΠSe-$ ⊢Γ (N-wf 0 ⊢Γ) ⊢T ⊢t
          ⊢TtΓ   = ⊢∷ ⊢Γ ⊢Tt
          I,rec  = S-, (S-I ⊢Γ) ⊢Tt (conv ⊢rec (≈-≲ (≈-sym ([I] ⊢Tt))))
          ↑Irec  = S-∘ I,rec (S-↑ ⊢TtΓ)
          aux = begin
            ↑ ∘ ↑ ∘ q (I , _)   ≈⟨ ∘-assoc (S-↑ ⊢NΓ) (S-↑ ⊢T0NΓ) qI,t ⟩
            ↑ ∘ (↑ ∘ q (I , _)) ≈⟨ ∘-cong (↑-∘-, (S-∘ (S-↑ ⊢T0ItΓ) I,t) ⊢Tv0 ⊢v0′)
                                          (↑-≈ ⊢NΓ) ⟩
            ↑ ∘ ((I , _) ∘ ↑)   ≈˘⟨ ∘-assoc (S-↑ ⊢NΓ) I,t (S-↑ ⊢T0ItΓ) ⟩
            ↑ ∘ (I , _) ∘ ↑     ≈⟨ ∘-cong (↑-≈ ⊢T0ItΓ) (↑-∘-, (S-I ⊢Γ) (N-wf 0 ⊢Γ) ⊢tI) ⟩
            (I ∘ ↑)             ≈!⟨ I-∘ (S-↑ ⊢T0ItΓ) ⟩
            ↑                   ∎
            where open TRS
          aux′    = ↑-∘-, (S-I ⊢Γ) ⊢Tt (conv ⊢rec (≈-≲ (≈-sym ([I] ⊢Tt))))
          open TR
          eq = begin
            _ [ ↑ ] [ I , _ ] ≈˘⟨ [∘]-St ⊢Γ ⊢Γ (Π N (Se _)) I,t (S-↑ ⊢NΓ) ⊢T ⟩
            _ [ ↑ ∘ (I , _) ] ≈⟨ []-cong-St ⊢Γ ⊢Γ (Π N (Se _)) I,t↑ (≈-refl ⊢T) (↑-∘-, (S-I ⊢Γ) (N-wf 0 ⊢Γ) ⊢tI) ⟩
            _ [ I ]           ≈!⟨ [I] ⊢T ⟩
            _                 ∎
          eq′     = begin
            (_ [ ↑ ] $ v 0) [ I , _ ]         ≈⟨ $-[]-St ⊢Γ ⊢NΓ (Se _) (N-wf 0 ⊢NΓ) I,t ⊢T↑ v0∶N ⟩
            _ [ ↑ ] [ I , _ ] $ v 0 [ I , _ ] ≈!⟨ $-cong-St ⊢Γ (Se _) (N-wf 0 ⊢Γ) eq v0It≈ (t[σ]-St ⊢Γ ⊢NΓ N v0∶N I,t) ⟩
            _ $ _                              ∎
          eq″ = begin
            _ [ ↑ ∘ ↑ ] [ q (I , _) ] ≈˘⟨ [∘]-St ⊢T0ItΓ ⊢Γ (Π N (Se _)) qI,t ⊢↑↑ ⊢T ⟩
            _ [ ↑ ∘ ↑ ∘ q (I , _) ]   ≈!⟨ []-cong-St ⊢T0ItΓ ⊢Γ (Π N (Se _)) (S-∘ qI,t ⊢↑↑) (≈-refl ⊢T) aux ⟩
            _ [ ↑ ]                   ∎
          eq‴ = begin
            su (v 1) [ q (I , _) ]   ≈⟨ su-[] qI,t ⊢v1 ⟩
            su (v 1 [ q (I , _) ])   ≈⟨ su-cong (≈-conv ([,]-v-su (S-∘ (S-↑ ⊢T0ItΓ) I,t) ⊢Tv0 ⊢v0′ here)
                                                        (≈-≲ (≈-trans (≈-sym ([∘]-St ⊢T0ItΓ ⊢Γ (Se _) (S-∘ (S-↑ ⊢T0ItΓ) I,t) (S-↑ ⊢NΓ) (N-wf 0 ⊢Γ)))
                                                                      (N-[] 0 (S-∘ (S-∘ (S-↑ ⊢T0ItΓ) I,t) (S-↑ ⊢NΓ)))))) ⟩
            su (v 0 [ (I , _) ∘ ↑ ]) ≈⟨ su-cong ([∘]-St ⊢T0ItΓ ⊢NΓ N (S-↑ ⊢T0ItΓ) I,t v0∶N) ⟩
            su (v 0 [ I , _ ] [ ↑ ]) ≈⟨ su-cong ([]-cong-St ⊢T0ItΓ ⊢Γ N (S-↑ ⊢T0ItΓ) v0It≈ (↑-≈ ⊢T0ItΓ)) ⟩
            su (_ [ ↑ ])             ≈!⟨ ≈-sym (su-[] (S-↑ ⊢T0ItΓ) ⊢t) ⟩
            su _ [ ↑ ]               ∎
          eq⁗ = begin
            (_ [ ↑ ∘ ↑ ] $ su (v 1)) [ q (I , _) ]
              ≈⟨ $-[]-St ⊢T0ItΓ ⊢T0NΓ (Se _) (N-wf 0 ⊢T0NΓ) qI,t ⊢T↑↑ ⊢suv1 ⟩
            _ [ ↑ ∘ ↑ ] [ q (I , _) ] $ su (v 1) [ q (I , _) ]
              ≈!⟨ $-cong-St ⊢T0ItΓ (Se _) (N-wf 0 ⊢T0ItΓ) eq″ eq‴ (t[σ]-St ⊢T0ItΓ ⊢T0NΓ N ⊢suv1 qI,t) ⟩
            _ [ ↑ ] $ su _ [ ↑ ]
              ∎
          helper = begin
            Π (_ [ ↑ ] $ v 0) (_ [ ↑ ∘ ↑ ] $ su (v 1)) [| _ ] ≈⟨ Π-[] I,t ⊢Tv0 ⊢Tsuv1 ℕₚ.≤-refl ℕₚ.≤-refl ⟩
            Π ((_ [ ↑ ] $ v 0) [ I , _ ])
              ((_ [ ↑ ∘ ↑ ] $ su (v 1)) [ q (I , _) ])        ≈!⟨ Π-cong ⊢T0I,t eq′ eq⁗ ℕₚ.≤-refl ℕₚ.≤-refl ⟩
            Π (_ $ _) (_ [ ↑ ] $ _)                           ∎
          heq     = begin
            _ [ ↑ ] [| rec _ _ _ _ ]       ≈˘⟨ [∘]-St ⊢Γ ⊢Γ (Π N (Se _)) I,rec (S-↑ ⊢TtΓ) ⊢T ⟩
            _ [ ↑ ∘ (I , rec _ _ _ _) ]    ≈⟨ []-cong-St ⊢Γ ⊢Γ (Π N (Se _)) ↑Irec (≈-refl ⊢T) aux′ ⟩
            _ [ I ]                        ≈!⟨ [I] ⊢T ⟩
            _                              ∎
          heq′    = begin
            su _ [ ↑ ] [| rec _ _ _ _ ]    ≈˘⟨ [∘]-St ⊢Γ ⊢Γ N I,rec (S-↑ ⊢TtΓ) (su-I ⊢t) ⟩
            su _ [ ↑ ∘ (I , rec _ _ _ _) ] ≈⟨ []-cong-St ⊢Γ ⊢Γ N ↑Irec (su-cong (≈-refl ⊢t)) aux′ ⟩
            su _ [ I ]                     ≈!⟨ [I] (su-I ⊢t) ⟩
            su _                           ∎
          helper′ = begin
            (_ [ ↑ ] $ su _ [ ↑ ]) [| rec _ _ _ _ ]
              ≈⟨ $-[]-St ⊢Γ ⊢T0ItΓ (Se _) (N-wf 0 ⊢T0ItΓ)
                         (S-conv (≈∷ (env≲-refl ⊢Γ) (≈-≲ (≈-sym eq′)) ⊢Tt) (S-, (S-I ⊢Γ) ⊢Tt (conv ⊢rec (≈-≲ (≈-sym ([I] ⊢Tt))))))
                         ⊢T↑′ (t[σ]-St ⊢T0ItΓ ⊢Γ N (su-I ⊢t) (S-↑ ⊢T0ItΓ)) ⟩
            _ [ ↑ ] [| rec _ _ _ _ ] $ su _ [ ↑ ] [| rec _ _ _ _ ]
              ≈!⟨ $-cong-St ⊢Γ (Se _) (N-wf zero ⊢Γ) heq heq′ (t[σ]-St ⊢Γ ⊢TtΓ N (t[σ]-St ⊢TtΓ ⊢Γ N (su-I ⊢t) (S-↑ ⊢TtΓ)) I,rec) ⟩
            _ $ su _ ∎

  ty-eq⇒env-ty-wf-gen (Λ-β ⊢t ⊢s)
    with ty⇒env-ty-wf ⊢t | ty⇒env-ty-wf ⊢s
  ...  | _ , _ , ⊢T | ⊢Γ , _ , ⊢S               = ⊢Γ , Λ-E (Λ-I ⊢t) ⊢s , t[σ] ⊢t (I-, ⊢Γ ⊢S ⊢s) , _ , ⊢T⇒⊢Tσ ⊢T (I-, ⊢Γ ⊢S ⊢s)
  ty-eq⇒env-ty-wf-gen (Λ-η ⊢s)
    with ty⇒env-ty-wf ⊢s
  ...  | ⊢Γ , _ , ⊢Π
       with inv-Π-wf ⊢Π | inv-Π-wf′ ⊢Π
  ...     | _ , ⊢T      | _ , ⊢S                = ⊢Γ
                                                , ⊢s
                                                , Λ-I (conv (Λ-E ([]-Π ⊢s (S-↑ ⊢SΓ) ⊢Π) ⊢v0)
                                                            (≈-≲ (≈-trans ([q∘]-cong ⊢SΓ ⊢SΓ (S-↑ ⊢SΓ) ⊢v0 ⊢T)
                                                                 (≈-trans (≈-sym ([]-cong-Se (S-I (⊢∷ ⊢Γ ⊢S)) (≈-refl ⊢T) (I-ext (⊢∷ ⊢Γ ⊢S))))
                                                                          ([I] ⊢T)))))
                                                , _ , ⊢Π
    where ⊢SΓ = ⊢∷ ⊢Γ ⊢S
          ⊢v0 = vlookup ⊢SΓ here
  ty-eq⇒env-ty-wf-gen ([I] ⊢t)
    with ty⇒env-ty-wf ⊢t
  ...  | ⊢Γ , _ , ⊢T                            = ⊢Γ , ⊢[I] ⊢Γ ⊢T ⊢t , ⊢t , _ , ⊢T
  ty-eq⇒env-ty-wf-gen (↑-lookup (⊢∷ ⊢Γ ⊢S) T∈Γ)
    with ∈!⇒ty-wf ⊢Γ T∈Γ
  ...  | _ , ⊢T                                 = ⊢∷ ⊢Γ ⊢S
                                                , t[σ] (vlookup ⊢Γ T∈Γ) (S-↑ (⊢∷ ⊢Γ ⊢S))
                                                , vlookup (⊢∷ ⊢Γ ⊢S) (there T∈Γ)
                                                , _ , ⊢T⇒⊢Tσ ⊢T (S-↑ (⊢∷ ⊢Γ ⊢S))
  ty-eq⇒env-ty-wf-gen ([∘] ⊢τ ⊢σ ⊢t)
    with ty⇒env-ty-wf ⊢t | tys⇒env-wf ⊢τ
  ...  | _ , _ , ⊢T      | ⊢Γ , _               = ⊢Γ
                                                , t[σ] ⊢t (S-∘ ⊢τ ⊢σ)
                                                , conv (t[σ] (t[σ] ⊢t ⊢σ) ⊢τ) (≈-≲ (≈-sym (T-[∘] ⊢τ ⊢σ ⊢T)))
                                                , _ , ⊢T⇒⊢Tσ ⊢T (S-∘ ⊢τ ⊢σ)
  ty-eq⇒env-ty-wf-gen ([,]-v-ze ⊢σ ⊢S ⊢t)
    with ty⇒env-ty-wf ⊢t | tys⇒env-wf ⊢σ
  ...  | _ , _ , ⊢T      | ⊢Γ , ⊢Δ              = ⊢Γ
                                                  , conv (t[σ] (vlookup (⊢∷ ⊢Δ ⊢S) here) (S-, ⊢σ ⊢S ⊢t))
                                                         (≈-≲ (≈-trans (≈-sym (T-[∘] (S-, ⊢σ ⊢S ⊢t) (S-↑ (⊢∷ ⊢Δ ⊢S)) ⊢S))
                                                                       (≈-sym ([]-cong-Se ⊢σ (≈-refl ⊢S) (S-≈-sym (↑-∘-, ⊢σ ⊢S ⊢t))))))
                                                  , ⊢t
                                                  , _ , ⊢T
  ty-eq⇒env-ty-wf-gen ([,]-v-su ⊢σ ⊢S ⊢s T∈Δ)
    with tys⇒env-wf ⊢σ
  ...  | ⊢Γ , ⊢Δ
       with ∈!⇒ty-wf ⊢Δ T∈Δ
  ...     | _ , ⊢T                              = ⊢Γ
                                                , conv (t[σ] (vlookup (⊢∷ ⊢Δ ⊢S) (there T∈Δ)) (S-, ⊢σ ⊢S ⊢s))
                                                       (≈-≲ (≈-trans (≈-sym (T-[∘] (S-, ⊢σ ⊢S ⊢s) (S-↑ (⊢∷ ⊢Δ ⊢S)) ⊢T))
                                                                     (≈-sym ([]-cong-Se ⊢σ (≈-refl ⊢T) (S-≈-sym (↑-∘-, ⊢σ ⊢S ⊢s))))))
                                                , t[σ] (vlookup ⊢Δ T∈Δ) ⊢σ
                                                , _ , ⊢T⇒⊢Tσ ⊢T ⊢σ
  ty-eq⇒env-ty-wf-gen (≈-conv s≈t S≲T)
    with ty-eq⇒env-ty-wf-gen s≈t | ≲⇒env-ty-wf S≲T
  ...  | ⊢Γ , ⊢s , ⊢t , _ , ⊢S | _ , _ , _ , ⊢T = ⊢Γ
                                                , conv ⊢s S≲T
                                                , conv ⊢t S≲T
                                                , _ , ⊢T
  ty-eq⇒env-ty-wf-gen (≈-sym s≈t)
    with ty-eq⇒env-ty-wf-gen s≈t
  ...  | ⊢Γ , ⊢s , ⊢t , ⊢T                      = ⊢Γ , ⊢t , ⊢s , ⊢T
  ty-eq⇒env-ty-wf-gen (≈-trans s≈t′ t′≈t″)
    with ty-eq⇒env-ty-wf-gen s≈t′ | ty-eq⇒env-ty-wf-gen t′≈t″
  ...  | ⊢Γ , ⊢s , _ , ⊢T | _ , _ , ⊢t″ , _     = ⊢Γ , ⊢s , ⊢t″ , ⊢T


  -- ty-eq⇒env-ty-wf-gen : Γ ⊢ s ≈ t ∶ T →
  --                       ----------------------------
  --                       ⊢ Γ × Γ ⊢ s ∶ T × Γ ⊢ t ∶ T
  -- ty-eq⇒env-ty-wf-gen (N-[] i ⊢σ)
  --   with tys⇒env-wf ⊢σ
  -- ...  | ⊢Γ , ⊢Δ                             = ⊢Γ , conv (t[σ] (N-wf i ⊢Δ) ⊢σ) (≈-≲ (Se-[] ⊢σ ℕₚ.≤-refl)) , N-wf i ⊢Γ
  -- ty-eq⇒env-ty-wf-gen (Se-[] ⊢σ i<j)
  --   with tys⇒env-wf ⊢σ
  -- ...  | ⊢Γ , ⊢Δ                             = ⊢Γ , conv (t[σ] (Se-wf ⊢Δ i<j) ⊢σ) (≈-≲ (Se-[] ⊢σ ℕₚ.≤-refl)) , Se-wf ⊢Γ i<j
  -- ty-eq⇒env-ty-wf-gen (Π-[] ⊢σ ⊢S ⊢T i≤k j≤k)
  --   with tys⇒env-wf ⊢σ
  -- ...  | ⊢Γ , ⊢Δ                             = ⊢Γ , conv (t[σ] (Π-wf ⊢S ⊢T i≤k j≤k) ⊢σ) Sek[] , Π-wf ⊢S[σ] (conv (t[σ] ⊢T qσ) Sej[]) i≤k j≤k
  --   where Sek[] = ≈-≲ (Se-[] ⊢σ ℕₚ.≤-refl)
  --         Sei[] = ≈-≲ (Se-[] ⊢σ ℕₚ.≤-refl)
  --         ⊢S[σ] = conv (t[σ] ⊢S ⊢σ) Sei[]
  --         ⊢SΓ   = ⊢∷ ⊢Γ ⊢S[σ]
  --         qσ    = S-, (S-∘ (S-↑ ⊢SΓ) ⊢σ) ⊢S
  --                     (conv (vlookup ⊢SΓ here) (≈-≲ (≈-sym (≈-conv ([∘] (S-↑ ⊢SΓ) ⊢σ ⊢S)
  --                                              (≈-≲ (Se-[] (S-∘ (S-↑ ⊢SΓ) ⊢σ) ℕₚ.≤-refl))))))
  --         Sej[] = ≈-≲ (Se-[] qσ ℕₚ.≤-refl)
  -- ty-eq⇒env-ty-wf-gen (Π-cong _ S≈S′ T≈T′ i≤k j≤k)
  --   with ty-eq⇒env-ty-wf-gen S≈S′ | ty-eq⇒env-ty-wf-gen T≈T′
  -- ...  | ⊢Γ , ⊢S , ⊢S′ | _ , ⊢T , ⊢T′        = ⊢Γ
  --                                            , Π-wf ⊢S ⊢T i≤k j≤k
  --                                            , Π-wf ⊢S′ (EnvSubst.ty-env-subst {Δ = []} (≈-≲ (≈-sym S≈S′)) ⊢S′ ⊢T′ refl) i≤k j≤k
  -- ty-eq⇒env-ty-wf-gen (v-≈ ⊢Γ T∈Γ)           = ⊢Γ , vlookup ⊢Γ T∈Γ , vlookup ⊢Γ T∈Γ
  -- ty-eq⇒env-ty-wf-gen (ze-≈ ⊢Γ)              = ⊢Γ , ze-I ⊢Γ , ze-I ⊢Γ
  -- ty-eq⇒env-ty-wf-gen (su-cong s≈t)
  --   with ty-eq⇒env-ty-wf-gen s≈t
  -- ...  | ⊢Γ , ⊢t , ⊢t′                       = ⊢Γ , su-I ⊢t , su-I ⊢t′
  -- ty-eq⇒env-ty-wf-gen (rec-cong T≈T″ s≈s′ r≈r′ t≈t′)
  --   with ty-eq⇒env-ty-wf-gen T≈T″
  --      | ty-eq⇒env-ty-wf-gen s≈s′
  --      | ty-eq⇒env-ty-wf-gen r≈r′
  --      | ty-eq⇒env-ty-wf-gen t≈t′
  -- ...  | ⊢Γ , ⊢T , ⊢T″
  --      | _ , ⊢s , ⊢s′
  --      | _ , ⊢r , ⊢r′
  --      | _ , ⊢t , ⊢t′                        = ⊢Γ
  --                                            , N-E ⊢T ⊢s ⊢r ⊢t
  --                                            , conv (N-E ⊢T″
  --                                                        (conv ⊢s′ (≈-≲ (≈-conv ($-cong T≈T″ (ze-≈ ⊢Γ))
  --                                                                               (≈-≲ (Se-[] (S-, (S-I ⊢Γ) ⊢N (conv (ze-I ⊢Γ) (⊢N≲N[I] ⊢Γ)))
  --                                                                                           ℕₚ.≤-refl)))))
  --                                                        (conv ⊢r′ (≈-≲ (Π-cong ⊢N
  --                                                                               (≈-refl ⊢N)
  --                                                                       (Π-cong ⊢T0
  --                                                                               (≈-conv ($-cong (≈-conv ([]-cong (↑-≈ ⊢NΓ) T≈T″) (≈-≲ ⊢ΠNS≈))
  --                                                                                               (v-≈ ⊢NΓ here))
  --                                                                                       (≈-≲ (iter-[]-Se ⊢NΓ (((I , v 0) , S-, (S-I ⊢NΓ) ⊢N↑
  --                                                                                                                          (conv (vlookup ⊢NΓ here) (≈-≲ (≈-sym ([I] ⊢N↑))))
  --                                                                                                                        , ⊢∷ ⊢NΓ ⊢N↑)
  --                                                                                                            ◅ (q ↑ , ⊢qσ ⊢NΓ (N-wf 0 ⊢Γ) (S-↑ ⊢NΓ) , ⊢NΓ)
  --                                                                                                            ◅ ε) ℕₚ.≤-refl)))
  --                                                                               (≈-conv ($-cong (≈-conv ([]-cong (S-≈-refl ⊢↑↑)
  --                                                                                                                T≈T″)
  --                                                                                                       (≈-≲ (≈-conv (≈-trans (Π-[] ⊢↑↑
  --                                                                                                                                   ⊢N
  --                                                                                                                                   (Se-wf ⊢NΓ ℕₚ.≤-refl)
  --                                                                                                                                   _≤_.z≤n
  --                                                                                                                                   ℕₚ.≤-refl)
  --                                                                                                                             (Π-cong (⊢T⇒⊢Tσ ⊢N ⊢↑↑)
  --                                                                                                                                     (N-[] 0 ⊢↑↑)
  --                                                                                                                                     (Se-[] (⊢qσ ⊢T0NΓ ⊢N ⊢↑↑)
  --                                                                                                                                            ℕₚ.≤-refl)
  --                                                                                                                                     _≤_.z≤n
  --                                                                                                                                     ℕₚ.≤-refl))
  --                                                                                                                    (Se-≲ ⊢T0NΓ ℕₚ.≤-refl))))
  --                                                                                               (≈-refl ⊢suv1))
  --                                                                                       (≈-≲ (Se-[] (S-, (S-I ⊢T0NΓ) (N-wf 0 ⊢T0NΓ) (conv ⊢suv1
  --                                                                                                                                         (≈-≲ (≈-sym (N-[] 0 (S-I ⊢T0NΓ))))))
  --                                                                                                   ℕₚ.≤-refl)))
  --                                                                               ℕₚ.≤-refl ℕₚ.≤-refl)
  --                                                                               _≤_.z≤n ℕₚ.≤-refl)))
  --                                                        ⊢t′)
  --                                                   (≈-≲ (≈-conv ($-cong (≈-sym T≈T″) (≈-sym t≈t′))
  --                                                                (≈-≲ (Se-[] (S-, (S-I ⊢Γ) ⊢N
  --                                                                                 (conv ⊢t′ (≈-≲ (≈-sym (N-[] 0 (S-I ⊢Γ))))))
  --                                                                            ℕₚ.≤-refl))))
  --   where open TR
  --         ⊢N≲N[I] : ⊢ Γ → Γ ⊢ N ≲ N [ I ]
  --         ⊢N≲N[I] ⊢Γ = (≈-≲ (≈-sym (N-[] 0 (S-I ⊢Γ))))
  --         ⊢N    = N-wf 0 ⊢Γ
  --         ⊢NΓ   = ⊢∷ ⊢Γ ⊢N
  --         ⊢ΠNS≈ = Π-[] (S-↑ ⊢NΓ) (N-wf 0 ⊢Γ) (Se-wf ⊢NΓ ℕₚ.≤-refl) _≤_.z≤n ℕₚ.≤-refl
  --         ⊢N↑   = ⊢T⇒⊢Tσ ⊢N (S-↑ ⊢NΓ)
  --         ⊢T0   = conv (Λ-E (conv (t[σ] ⊢T (S-↑ ⊢NΓ))
  --                           (≈-≲ (begin
  --                             Π N (Se _) [ ↑ ]           ≈⟨ ⊢ΠNS≈ ⟩
  --                             Π (N [ ↑ ]) (Se _ [ q ↑ ]) ≈!⟨ Π-cong ⊢N↑ (≈-refl ⊢N↑) (Se-[] (⊢qσ ⊢NΓ ⊢N (S-↑ ⊢NΓ)) ℕₚ.≤-refl) _≤_.z≤n ℕₚ.≤-refl ⟩
  --                             Π (N [ ↑ ]) (Se _)         ∎)))
  --                           (vlookup ⊢NΓ here))
  --                      (≈-≲ (Se-[] (S-, (S-I ⊢NΓ)
  --                                       (N-wf 0 ⊢NΓ)
  --                                       (conv (vlookup ⊢NΓ here)
  --                                             (≈-≲ (≈-trans (N-[] 0 (S-↑ ⊢NΓ))
  --                                                           (≈-sym ([I] (N-wf 0 ⊢NΓ)))))))
  --                                  ℕₚ.≤-refl))
  --         ⊢T0NΓ = ⊢∷ (⊢∷ ⊢Γ ⊢N) ⊢T0
  --         ⊢↑↑   = S-∘ (S-↑ ⊢T0NΓ) (S-↑ ⊢NΓ)
  --         ⊢suv1 = su-I (conv (vlookup ⊢T0NΓ (there here))
  --                            (≈-≲ (≈-trans (≈-Se-inter-[] ⊢T0NΓ ((↑ , S-↑ ⊢T0NΓ , ⊢NΓ) ◅ ε) ([]-cong (↑-≈ ⊢T0NΓ) (N-[] 0 (S-↑ ⊢NΓ))))
  --                                          (N-[] 0 (S-↑ ⊢T0NΓ)))))
  -- ty-eq⇒env-ty-wf-gen (Λ-cong s≈t)
  --   with ty-eq⇒env-ty-wf-gen s≈t
  -- ... | ⊢∷ ⊢Γ ⊢S , ⊢t , ⊢t′                  = ⊢Γ , Λ-I ⊢S ⊢t , Λ-I ⊢S ⊢t′
  -- ty-eq⇒env-ty-wf-gen ($-cong r≈r′ s≈s′)
  --   with ty-eq⇒env-ty-wf-gen r≈r′ | ty-eq⇒env-ty-wf-gen s≈s′
  -- ...  | ⊢Γ , ⊢r , ⊢r′ | _ , ⊢s , ⊢s′        = ⊢Γ
  --                                            , Λ-E ⊢r ⊢s
  --                                            , conv (Λ-E ⊢r′ ⊢s′)
  --                                                   (≈-≲ (≈-conv ([]-cong {!!} {!!}) {!!}))
  -- ty-eq⇒env-ty-wf-gen ([]-cong x s≈t)        = {!!}
  -- ty-eq⇒env-ty-wf-gen (ze-[] x)              = {!!}
  -- ty-eq⇒env-ty-wf-gen (su-[] x x₁)           = {!!}
  -- ty-eq⇒env-ty-wf-gen (Λ-[] x x₁)            = {!!}
  -- ty-eq⇒env-ty-wf-gen ($-[] x x₁ x₂)         = {!!}
  -- ty-eq⇒env-ty-wf-gen (rec-[] x x₁ x₂ x₃ x₄) = {!!}
  -- ty-eq⇒env-ty-wf-gen (rec-β-ze x x₁ x₂)     = {!!}
  -- ty-eq⇒env-ty-wf-gen (rec-β-su x x₁ x₂ x₃)  = {!!}
  -- ty-eq⇒env-ty-wf-gen (Λ-β x x₁)             = {!!}
  -- ty-eq⇒env-ty-wf-gen (Λ-η x)                = {!!}
  -- ty-eq⇒env-ty-wf-gen ([I] x)                = {!!}
  -- ty-eq⇒env-ty-wf-gen (↑-lookup ⊢Γ x)        = {!!}
  -- ty-eq⇒env-ty-wf-gen ([∘] x x₁ x₂)          = {!!}
  -- ty-eq⇒env-ty-wf-gen ([,]-v-ze x x₁ x₂)     = {!!}
  -- ty-eq⇒env-ty-wf-gen ([,]-v-su x x₁ x₂ x₃)  = {!!}
  -- ty-eq⇒env-ty-wf-gen (≈-conv s≈t x)         = {!!}
  -- ty-eq⇒env-ty-wf-gen (≈-sym s≈t)            = {!!}
  -- ty-eq⇒env-ty-wf-gen (≈-trans s≈t s≈t₁)     = {!!}
