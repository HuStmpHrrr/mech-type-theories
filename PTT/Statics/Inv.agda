{-# OPTIONS --without-K --safe #-}

module PTT.Statics.Inv where

open import Lib
open import PTT.Statics
open import PTT.Statics.Misc
open import PTT.Statics.Complement
open import PTT.Statics.EnvSubst

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
  ty⇒env-ty-wf (Λ-I ⊢S t) with ty⇒env-ty-wf t
  ... | ⊢∷ ⊢Γ _ , _ , ⊢T        = ⊢Γ , _ , Π-wf ⊢S ⊢T (ℕₚ.m≤m⊔n _ _) (ℕₚ.n≤m⊔n _ _)
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
    with tys⇒env-wf ⊢σ
  ...  | ⊢Γ , _                  = ⊢Γ , {!!}

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
  ... | ⊢∷ ⊢Γ ⊢S , ⊢t , ⊢t′ , _ , ⊢T          = ⊢Γ , Λ-I ⊢S ⊢t , Λ-I ⊢S ⊢t′ , _ , Π-wf ⊢S ⊢T (ℕₚ.m≤m⊔n _ _) (ℕₚ.n≤m⊔n _ _)
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
  ty-eq⇒env-ty-wf-gen ([]-cong σ≈σ′ t≈t′)     = {!!}
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
                                              , t[σ] (Λ-I ⊢S ⊢t) ⊢σ
                                              , conv (Λ-I ⊢Sσ (t[σ] ⊢t (S-, σ∘↑ ⊢S
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
  ty-eq⇒env-ty-wf-gen (rec-[] ⊢σ ⊢T ⊢s ⊢r ⊢t)   = {!!}
  ty-eq⇒env-ty-wf-gen (rec-β-ze x x₁ x₂)        = {!!}
  ty-eq⇒env-ty-wf-gen (rec-β-su x x₁ x₂ x₃)     = {!!}
  ty-eq⇒env-ty-wf-gen (Λ-β ⊢t ⊢s)
    with ty⇒env-ty-wf ⊢t | ty⇒env-ty-wf ⊢s
  ...  | _ , _ , ⊢T | ⊢Γ , _ , ⊢S               = ⊢Γ , Λ-E (Λ-I ⊢S ⊢t) ⊢s , t[σ] ⊢t (I-, ⊢Γ ⊢S ⊢s) , _ , ⊢T⇒⊢Tσ ⊢T (I-, ⊢Γ ⊢S ⊢s)
  ty-eq⇒env-ty-wf-gen (Λ-η ⊢s)
    with ty⇒env-ty-wf ⊢s
  ...  | ⊢Γ , _ , ⊢Π
       with inv-Π-wf ⊢Π | inv-Π-wf′ ⊢Π
  ...     | _ , ⊢T      | _ , ⊢S                = ⊢Γ
                                                , ⊢s
                                                , Λ-I ⊢S (conv (Λ-E ([]-Π ⊢s (S-↑ ⊢SΓ) ⊢Π) ⊢v0)
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
                                                         (≈-≲ {!!})
                                                  , ⊢t
                                                  , _ , ⊢T
  ty-eq⇒env-ty-wf-gen ([,]-v-su x x₁ x₂ x₃)     = {!!}
  ty-eq⇒env-ty-wf-gen (≈-conv s≈t x)            = {!!}
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
