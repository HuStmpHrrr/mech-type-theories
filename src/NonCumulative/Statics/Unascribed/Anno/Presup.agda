{-# OPTIONS --without-K --safe #-}

module NonCumulative.Statics.Unascribed.Anno.Presup where

open import Lib
open import NonCumulative.Statics.Unascribed.Anno
open import NonCumulative.Statics.Unascribed.Anno.PER
open import NonCumulative.Statics.Unascribed.Anno.Refl
open import NonCumulative.Statics.Unascribed.Anno.Misc
open import NonCumulative.Statics.Unascribed.Anno.CtxEquiv
open import NonCumulative.Statics.Unascribed.Anno.Properties.Contexts
open import NonCumulative.Statics.Unascribed.Anno.Properties.Subst

mutual
  presup-tm : ∀ {i} →
              Γ ⊢ t ∶[ i ] T →
              ----------------------
              ⊢ Γ × Γ ⊢ T ∶[ 1 + i ] Se i
  presup-tm (N-wf ⊢Γ)        = ⊢Γ , Se-wf zero ⊢Γ
  presup-tm (Se-wf i ⊢Γ)     = ⊢Γ , Se-wf (suc i) ⊢Γ
  presup-tm (Liftt-wf n ⊢T)
    with presup-tm ⊢T
  ...  | ⊢Γ , _              = ⊢Γ , Se-wf (n + _) ⊢Γ
  presup-tm (Π-wf ⊢S ⊢T eq)
    with presup-tm ⊢S
  ...  | ⊢Γ , _              = ⊢Γ , Se-wf _ ⊢Γ
  presup-tm (vlookup ⊢Γ T∈Γ) = ⊢Γ , ∈⇒ty-wf ⊢Γ T∈Γ
  presup-tm (ze-I ⊢Γ)        = ⊢Γ , N-wf ⊢Γ
  presup-tm (su-I ⊢t)        = presup-tm ⊢t
  presup-tm (N-E ⊢T ⊢s ⊢r ⊢t)
    with presup-tm ⊢T
  ... | ⊢∷ ⊢Γ _ , _          = ⊢Γ , t[σ]-Se ⊢T (⊢I,t ⊢Γ (N-wf ⊢Γ) ⊢t)
  presup-tm (Λ-I ⊢S ⊢t eq)
    with presup-tm ⊢t
  ...  | ⊢∷ ⊢Γ _ , ⊢T        = ⊢Γ , Π-wf ⊢S ⊢T eq
  presup-tm (Λ-E ⊢S ⊢T ⊢t ⊢s eq)
    with presup-tm ⊢S
  ...  | ⊢Γ , _              = ⊢Γ , t[σ]-Se ⊢T (⊢I,t ⊢Γ ⊢S ⊢s)
  presup-tm (L-I n ⊢t)
    with presup-tm ⊢t
  ...  | ⊢Γ , ⊢T             = ⊢Γ , Liftt-wf n ⊢T
  presup-tm (L-E n ⊢T ⊢t)    = proj₁ (presup-tm ⊢T) , ⊢T
  presup-tm (t[σ] ⊢t ⊢σ)
    with presup-tm ⊢t | presup-s ⊢σ
  ...  | _ , ⊢T | ⊢Γ , _     = ⊢Γ , t[σ]-Se ⊢T ⊢σ
  presup-tm (conv ⊢t S≈T)
    with presup-≈ S≈T
  ...  | ⊢Γ , _ , ⊢T , _     = ⊢Γ , ⊢T

  presup-s : Γ ⊢s σ ∶ Δ →
             ------------
             ⊢ Γ × ⊢ Δ
  presup-s (s-I ⊢Γ)             = ⊢Γ , ⊢Γ
  presup-s (s-wk ⊢TΓ@(⊢∷ ⊢Γ _)) = ⊢TΓ , ⊢Γ
  presup-s (s-∘ ⊢σ ⊢δ)          = proj₁ (presup-s ⊢σ) , proj₂ (presup-s ⊢δ)
  presup-s (s-, ⊢σ ⊢T ⊢t)
    with ⊢Γ , ⊢Δ ← presup-s ⊢σ  = ⊢Γ , ⊢∷ ⊢Δ ⊢T
  presup-s (s-conv ⊢σ Δ′≈Δ)     = proj₁ (presup-s ⊢σ) , proj₂ (presup-⊢≈ Δ′≈Δ)


  presup-≈ : ∀ {i} →
             Γ ⊢ s ≈ t ∶[ i ] T →
             -----------------------------------
             ⊢ Γ × Γ ⊢ s ∶[ i ] T × Γ ⊢ t ∶[ i ] T × Γ ⊢ T ∶[ 1 + i ] Se i
  presup-≈ (N-[] ⊢σ)
    with presup-s ⊢σ
  ...  | ⊢Γ , ⊢Δ                           = ⊢Γ , t[σ]-Se (N-wf ⊢Δ) ⊢σ , N-wf ⊢Γ , Se-wf zero ⊢Γ
  presup-≈ (Se-[] i ⊢σ)
    with presup-s ⊢σ
  ...  | ⊢Γ , ⊢Δ                           = ⊢Γ , t[σ]-Se (Se-wf i ⊢Δ) ⊢σ , Se-wf i ⊢Γ , Se-wf (suc i) ⊢Γ
  presup-≈ (Liftt-[] n ⊢σ ⊢T)
    with presup-s ⊢σ
  ...  | ⊢Γ , ⊢Δ                           = ⊢Γ , t[σ]-Se (Liftt-wf n ⊢T) ⊢σ , Liftt-wf n (t[σ]-Se ⊢T ⊢σ) , Se-wf (n + _) ⊢Γ
  presup-≈ (Π-[] ⊢σ ⊢S ⊢T eq)
    with presup-s ⊢σ
  ...  | ⊢Γ , ⊢Δ                           = ⊢Γ , t[σ]-Se (Π-wf ⊢S ⊢T eq) ⊢σ , Π-wf (t[σ]-Se ⊢S ⊢σ) (t[σ]-Se ⊢T (⊢q ⊢Γ ⊢σ ⊢S)) eq , Se-wf _ ⊢Γ
  presup-≈ (Π-cong ⊢S S≈S′ T≈T′ eq)
    with presup-≈ S≈S′ | presup-≈ T≈T′
  ...  | ⊢Γ , ⊢S , ⊢S′ , _
       | _ , ⊢T , ⊢T′ , _                  = ⊢Γ , Π-wf ⊢S ⊢T eq , Π-wf ⊢S′ (ctxeq-tm (∷-cong (≈-Ctx-refl ⊢Γ) ⊢S ⊢S′ S≈S′ S≈S′) ⊢T′) eq , Se-wf _ ⊢Γ
  presup-≈ (Liftt-cong n T≈T′)
    with presup-≈ T≈T′
  ...  | ⊢Γ , ⊢T , ⊢T′ , _                 = ⊢Γ , Liftt-wf n ⊢T , Liftt-wf n ⊢T′ , Se-wf (n + _) ⊢Γ
  presup-≈ (v-≈ ⊢Γ T∈Γ)                    = ⊢Γ , vlookup ⊢Γ T∈Γ , vlookup ⊢Γ T∈Γ , ∈⇒ty-wf ⊢Γ T∈Γ
  presup-≈ (ze-≈ ⊢Γ)                       = ⊢Γ , ze-I ⊢Γ , ze-I ⊢Γ , N-wf ⊢Γ
  presup-≈ (su-cong t≈t′)
    with presup-≈ t≈t′
  ...  | ⊢Γ , ⊢t , ⊢t′ , ⊢N                 = ⊢Γ , su-I ⊢t , su-I ⊢t′ , ⊢N
  presup-≈ (rec-cong ⊢T T≈T′ s≈s′ r≈r′ t≈t′)
    with ⊢NΓ , ⊢T , ⊢T′ , _ ← presup-≈ T≈T′
       | ⊢Γ , ⊢s , ⊢s′ , _ ← presup-≈ s≈s′
       | ⊢TNΓ , ⊢r , ⊢r′ , _ ← presup-≈ r≈r′
       | _ , ⊢t , ⊢t′ , _ ← presup-≈ t≈t′    = ⊢Γ
                                             , N-E ⊢T ⊢s ⊢r ⊢t
                                             , conv
                                               (N-E ⊢T′ (conv ⊢s′ ([]-cong-Se′ T≈T′ (⊢I,ze ⊢Γ))) (ctxeq-tm (∷-cong′ ⊢NΓ ⊢T ⊢T′ T≈T′) (conv ⊢r′ ([]-cong-Se′ T≈T′ (⊢[wk∘wk],su[v1] ⊢TNΓ)))) ⊢t′)
                                               (≈-sym ([]-cong-Se T≈T′ (⊢I,t ⊢Γ (N-wf ⊢Γ) ⊢t) (,-cong (I-≈ ⊢Γ) (N-wf ⊢Γ) (≈-conv-N-[]-sym t≈t′ (s-I ⊢Γ)))))
                                             , (t[σ]-Se ⊢T (⊢I,t ⊢Γ (N-wf ⊢Γ) ⊢t))
  presup-≈ (Λ-cong ⊢S t≈t′ eq)
    with ⊢∷ ⊢Γ _ , ⊢t , ⊢t′ , ⊢T ← presup-≈ t≈t′ = ⊢Γ , Λ-I ⊢S ⊢t eq , Λ-I ⊢S ⊢t′ eq , Π-wf ⊢S ⊢T eq
  presup-≈ ($-cong ⊢S ⊢T r≈r′ s≈s′ eq)
    with ⊢Γ , ⊢r , ⊢r′ , ⊢ΠST ← presup-≈ r≈r′
       | _ , ⊢s , ⊢s′ , _ ← presup-≈ s≈s′        = ⊢Γ
                                                 , Λ-E ⊢S ⊢T ⊢r ⊢s eq
                                                 , conv (Λ-E ⊢S ⊢T ⊢r′ ⊢s′ eq) ([]-cong-Se″ ⊢T (⊢I,t ⊢Γ ⊢S ⊢s′) (,-cong (I-≈ ⊢Γ) ⊢S (≈-conv (≈-sym s≈s′) (≈-sym ([I] ⊢S)))))
                                                 , t[σ]-Se ⊢T (⊢I,t ⊢Γ ⊢S ⊢s)
  presup-≈ ([]-cong t≈t′ σ≈σ′)
    with _ , ⊢t , ⊢t′ , ⊢T ← presup-≈ t≈t′
       | ⊢Γ , ⊢σ , ⊢σ′ , _ ← presup-s-≈ σ≈σ′     = ⊢Γ , t[σ] ⊢t ⊢σ , conv (t[σ] ⊢t′ ⊢σ′) ([]-cong-Se″ ⊢T ⊢σ′ (s-≈-sym σ≈σ′)) , t[σ]-Se ⊢T ⊢σ
  presup-≈ (liftt-cong n t≈t′)
    with ⊢Γ , ⊢t , ⊢t′ , ⊢T ← presup-≈ t≈t′      = ⊢Γ , L-I n ⊢t , L-I n ⊢t′ , Liftt-wf n ⊢T
  presup-≈ (unlift-cong n ⊢T t≈t′)
    with ⊢Γ , ⊢t , ⊢t′ , _ ← presup-≈ t≈t′       = ⊢Γ , L-E n ⊢T ⊢t , L-E n ⊢T ⊢t′ , ⊢T
  presup-≈ (ze-[] ⊢σ)
    with ⊢Γ , ⊢Δ ← presup-s ⊢σ    = ⊢Γ , t[σ]-N (ze-I ⊢Δ) ⊢σ , ze-I ⊢Γ , N-wf ⊢Γ
  presup-≈ (su-[] ⊢σ ⊢t)
    with ⊢Γ ← proj₁ (presup-s ⊢σ) = ⊢Γ , t[σ]-N (su-I ⊢t) ⊢σ , su-I (t[σ]-N ⊢t ⊢σ) , N-wf ⊢Γ
  presup-≈ (rec-[] {Γ = Γ} {σ = σ} {Δ = Δ} {T = T} {t = t} {i = i} ⊢σ ⊢T ⊢s ⊢r ⊢t)
    with ⊢Γ , ⊢Δ ← presup-s ⊢σ = ⊢Γ
                               , conv
                                   (t[σ] (N-E ⊢T ⊢s ⊢r ⊢t) ⊢σ)
                                   (ER.begin
                                      T [| t ] [ σ ]
                                    ER.≈⟨ [∘]-Se ⊢T (⊢I,t ⊢Δ (N-wf ⊢Δ) ⊢t) ⊢σ ⟩
                                      T [ (I , t) ∘ σ ]
                                    ER.≈⟨ []-cong-Se″ ⊢T (s-∘ ⊢σ (⊢I,t ⊢Δ (N-wf ⊢Δ) ⊢t)) ([I,t]∘σ≈σ,t[σ] ⊢NΔ ⊢σ ⊢t) ⟩
                                      T [ σ , sub t σ ]
                                    ER.∎)
                               , conv
                                   (N-E ⊢T[qσ]
                                     (conv
                                       (t[σ] ⊢s ⊢σ)
                                       (ER.begin
                                          T [| ze ] [ σ ]
                                        ER.≈⟨ [∘]-Se ⊢T (⊢I,ze ⊢Δ) ⊢σ ⟩
                                          T [ (I , ze) ∘ σ ]
                                        ER.≈⟨ []-cong-Se″ ⊢T (s-∘ ⊢σ (⊢I,ze ⊢Δ)) ([I,ze]∘σ≈σ,ze ⊢Δ ⊢σ) ⟩
                                          T [ σ , ze ]
                                        ER.≈˘⟨ []-cong-Se″ ⊢T (s-∘ (⊢I,ze ⊢Γ) ⊢qσ) (qσ∘[I,ze]≈σ,ze ⊢Γ ⊢Δ ⊢σ) ⟩
                                          T [ q σ ∘ (I , ze) ]
                                        ER.≈˘⟨ [∘]-Se ⊢T ⊢qσ (⊢I,t ⊢Γ (N-wf ⊢Γ) (ze-I ⊢Γ)) ⟩
                                          T [ q σ ] [| ze ]
                                        ER.∎))
                                     (conv (t[σ] ⊢r ⊢q[qσ]) (rec-β-su-T-swap ⊢Γ ⊢TNΔ ⊢σ))
                                     (t[σ]-N ⊢t ⊢σ))
                                   (≈-trans
                                     ([∘]-Se ⊢T ⊢qσ (⊢I,t ⊢Γ (N-wf ⊢Γ) (t[σ]-N ⊢t ⊢σ)))
                                     ([]-cong-Se″ ⊢T (s-∘ (⊢I,t ⊢Γ (N-wf ⊢Γ) (t[σ]-N ⊢t ⊢σ)) ⊢qσ) (qσ∘[I,t]≈σ,t ⊢Γ (N-wf ⊢Δ) ⊢σ (t[σ] ⊢t ⊢σ))))
                                , t[σ]-Se ⊢T (s-, ⊢σ (N-wf ⊢Δ) (t[σ] ⊢t ⊢σ))
    where
      ⊢qσ = ⊢q-N ⊢Γ ⊢Δ ⊢σ
      ⊢T[qσ] = t[σ]-Se ⊢T ⊢qσ
      ⊢NΓ = ⊢∷ ⊢Γ (N-wf ⊢Γ)
      ⊢q[qσ] = ⊢q ⊢NΓ ⊢qσ ⊢T
      ⊢T[qσ]NΓ = ⊢∷ ⊢NΓ ⊢T[qσ]
      ⊢NΔ = ⊢∷ ⊢Δ (N-wf ⊢Δ)
      ⊢TNΔ = ⊢∷ ⊢NΔ ⊢T
  presup-≈ (Λ-[] ⊢σ ⊢S ⊢t eq)
    with ⊢Γ ← proj₁ (presup-s ⊢σ)
       | ⊢∷ _ ⊢S , ⊢T ← presup-tm ⊢t = ⊢Γ
                                     , t[σ] (Λ-I ⊢S ⊢t eq) ⊢σ
                                     , conv
                                       (Λ-I (t[σ]-Se ⊢S ⊢σ) (t[σ] ⊢t (⊢q ⊢Γ ⊢σ ⊢S)) eq)
                                       (≈-sym (Π-[] ⊢σ ⊢S ⊢T eq))
                                     , t[σ]-Se (Π-wf ⊢S ⊢T eq) ⊢σ
  presup-≈ ($-[] ⊢S ⊢T ⊢σ ⊢r ⊢s eq)
    with ⊢Γ , ⊢Δ ← presup-s ⊢σ       = ⊢Γ
                                     , conv (t[σ] (Λ-E ⊢S ⊢T ⊢r ⊢s eq) ⊢σ) (≈-trans ([∘]-Se ⊢T (⊢I,t ⊢Δ ⊢S ⊢s) ⊢σ) ([]-cong-Se″ ⊢T (s-∘ ⊢σ (⊢I,t ⊢Δ ⊢S ⊢s)) ([I,t]∘σ≈σ,t[σ] (⊢∷ ⊢Δ ⊢S) ⊢σ ⊢s)))
                                     , conv (Λ-E (t[σ]-Se ⊢S ⊢σ) (t[σ]-Se ⊢T (⊢q ⊢Γ ⊢σ ⊢S)) (conv (t[σ] ⊢r ⊢σ) (Π-[] ⊢σ ⊢S ⊢T eq)) (t[σ] ⊢s ⊢σ) eq)
                                            (≈-trans ([∘]-Se ⊢T (⊢q ⊢Γ ⊢σ ⊢S) (⊢I,t ⊢Γ (t[σ]-Se ⊢S ⊢σ) (t[σ] ⊢s ⊢σ)))
                                                     ([]-cong-Se″ ⊢T (s-∘ (⊢I,t ⊢Γ (t[σ]-Se ⊢S ⊢σ) (t[σ] ⊢s ⊢σ)) (⊢q ⊢Γ ⊢σ ⊢S)) (qσ∘[I,t]≈σ,t ⊢Γ ⊢S ⊢σ (t[σ] ⊢s ⊢σ))))
                                     , t[σ]-Se ⊢T (s-, ⊢σ ⊢S (t[σ] ⊢s ⊢σ))
  presup-≈ (liftt-[] n ⊢σ ⊢T ⊢t)
    with ⊢Γ , _ ← presup-s ⊢σ        = ⊢Γ , t[σ] (L-I n ⊢t) ⊢σ , conv (L-I n (t[σ] ⊢t ⊢σ)) (≈-sym (Liftt-[] n ⊢σ ⊢T)) , t[σ]-Se (Liftt-wf n ⊢T) ⊢σ
  presup-≈ (unlift-[] n ⊢T ⊢σ ⊢t)
    with ⊢Γ , _ ← presup-s ⊢σ        = ⊢Γ , t[σ] (L-E n ⊢T ⊢t) ⊢σ , L-E n (t[σ]-Se ⊢T ⊢σ) (conv (t[σ] ⊢t ⊢σ) (Liftt-[] n ⊢σ ⊢T)) , t[σ]-Se ⊢T ⊢σ
  presup-≈ (rec-β-ze ⊢T ⊢t ⊢r)
    with ⊢Γ ← proj₁ (presup-tm ⊢t) = ⊢Γ , N-E ⊢T ⊢t ⊢r (ze-I ⊢Γ) , ⊢t , t[σ]-Se ⊢T (⊢I,t ⊢Γ (N-wf ⊢Γ) (ze-I ⊢Γ))
  presup-≈ (rec-β-su {Γ = Γ} {T = T} {s = s} {r = r} {t = t} ⊢T ⊢s ⊢r ⊢t)
    with ⊢TNΓ@(⊢∷ ⊢NΓ@(⊢∷ ⊢Γ ⊢N) _) ← proj₁ (presup-tm ⊢r) = ⊢Γ
                                                           , N-E ⊢T ⊢s ⊢r (su-I ⊢t)
                                                           , conv
                                                             (t[σ] ⊢r ⊢I,t,recTrst)
                                                             (≈-trans ([∘]-Se ⊢T ⊢[wk∘wk],su[v1]′ ⊢I,t,recTrst) ([]-cong-Se″ ⊢T (s-∘ ⊢I,t,recTrst ⊢[wk∘wk],su[v1]′) lemma))
                                                           , t[σ]-Se ⊢T (⊢I,t ⊢Γ ⊢N (su-I ⊢t))
    where
      ⊢recTsrt = N-E ⊢T ⊢s ⊢r ⊢t
      ⊢I,t,recTrst = s-, (⊢I,t ⊢Γ ⊢N ⊢t) ⊢T (N-E ⊢T ⊢s ⊢r ⊢t)
      ⊢wk∘wk = s-∘ (s-wk ⊢TNΓ) (s-wk ⊢NΓ)
      ⊢[wk∘wk],su[v1]′ = s-, ⊢wk∘wk ⊢N (conv-N-[]-sym (su-I (⊢vn∶N L.[ -, T ] ⊢TNΓ refl)) ⊢wk∘wk)

      lemma : Γ ⊢s ((wk ∘ wk) , su (v 1)) ∘ ((I , t) , rec T s r t) ≈ I , su t ∶ (0 , N) ∷ Γ
      lemma =
        begin
          ((wk ∘ wk) , su (v 1)) ∘ ((I , t) , rec T s r t)
        ≈⟨ ,-∘ ⊢wk∘wk ⊢N (conv-N-[]-sym (su-I (⊢vn∶N L.[ -, T ] ⊢TNΓ refl)) ⊢wk∘wk) ⊢I,t,recTrst ⟩
          (wk ∘ wk ∘ ((I , t) , rec T s r t)) , su (v 1) [ (I , t) , rec T s r t ]
        ≈⟨ ,-cong lemma-l ⊢N (≈-conv-N-[]-sym lemma-r (s-∘ ⊢I,t,recTrst ⊢wk∘wk)) ⟩
          I , su t
        ∎
        where
          lemma-r : Γ ⊢ su (v 1) [ (I , t) , rec T s r t ] ≈ su t ∶[ 0 ] N
          lemma-r =
            begin
              su (v 1) [ (I , t) , rec T s r t ]
            ≈⟨ su-[] ⊢I,t,recTrst (⊢vn∶N L.[ -, T ] ⊢TNΓ refl) ⟩
              su (v 1 [ (I , t) , rec T s r t ])
            ≈⟨ su-cong (≈-conv ([,]-v-su ⊢NΓ (⊢I,t ⊢Γ ⊢N ⊢t) ⊢T ⊢recTsrt (here ⊢Γ ⊢N)) (N-[][] (s-wk ⊢NΓ) (⊢I,t ⊢Γ ⊢N ⊢t))) ⟩
              su (v 0 [ I , t ])
            ≈⟨ su-cong (≈-conv-N-[] ([,]-v-ze (s-I ⊢Γ) ⊢N (conv-N-[]-sym ⊢t (s-I ⊢Γ))) (s-I ⊢Γ)) ⟩
              su t
            ∎
            where
              open ER

          open SR

          lemma-l : Γ ⊢s wk ∘ wk ∘ ((I , t) , rec T s r t) ≈ I ∶ Γ
          lemma-l = wk∘wk∘,, ⊢Γ (s-I ⊢Γ) ⊢N ⊢T (conv ⊢t (≈-sym ([I] ⊢N))) ⊢recTsrt

  presup-≈ (Λ-β ⊢S ⊢T ⊢t ⊢s)
    with ⊢∷ ⊢Γ _ , _ ← presup-tm ⊢t       = ⊢Γ , Λ-E ⊢S ⊢T (Λ-I ⊢S ⊢t refl) ⊢s refl , t[σ] ⊢t (⊢I,t ⊢Γ ⊢S ⊢s) , t[σ]-Se ⊢T (⊢I,t ⊢Γ ⊢S ⊢s)
  presup-≈ (Λ-η ⊢S ⊢T ⊢s eq)
    with ⊢Γ , ⊢ΠST ← presup-tm ⊢s         = ⊢Γ , ⊢s
                                          , conv (Λ-I ⊢S (Λ-E ⊢S[wk]
                                                              (t[σ]-Se ⊢T (⊢q ⊢SΓ (s-wk ⊢SΓ) ⊢S))
                                                              (conv (t[σ] ⊢s (s-wk ⊢SΓ)) (Π-[] (s-wk ⊢SΓ) ⊢S ⊢T eq))
                                                              ⊢v0 eq)
                                                         eq)
                                                 (Π-cong ⊢S (≈-refl ⊢S)
                                                         (≈-trans ([∘]-Se ⊢T (⊢q ⊢SΓ (s-wk ⊢SΓ) ⊢S) ⊢I,v0)
                                                         (≈-trans ([]-cong-Se″ ⊢T (s-∘ ⊢I,v0 (⊢q ⊢SΓ (s-wk ⊢SΓ) ⊢S)) (q[wk]∘[I,v0]≈I ⊢SΓ))
                                                                  ([I] ⊢T)))
                                                         eq)
                                          , ⊢ΠST
    where
      ⊢SΓ    = ⊢∷ ⊢Γ ⊢S
      ⊢S[wk] = t[σ]-Se ⊢S (s-wk ⊢SΓ)
      ⊢v0    = vlookup ⊢SΓ (here ⊢Γ ⊢S)
      ⊢I,v0  = ⊢I,t ⊢SΓ ⊢S[wk] ⊢v0
  presup-≈ (L-β n ⊢t)
    with presup-tm ⊢t
  ...  | ⊢Γ , ⊢T                          = ⊢Γ , L-E n ⊢T (L-I n ⊢t) , ⊢t , ⊢T
  presup-≈ (L-η n ⊢T ⊢t)
    with presup-tm ⊢t
  ...  | ⊢Γ , ⊢LT                         = ⊢Γ , ⊢t , L-I n (L-E n ⊢T ⊢t) , ⊢LT
  presup-≈ ([I] ⊢t)
    with ⊢Γ , ⊢T ← presup-tm ⊢t           = ⊢Γ , conv (t[σ] ⊢t (s-I ⊢Γ)) ([I] ⊢T) , ⊢t , ⊢T
  presup-≈ ([wk] ⊢Γ ⊢S T∈Γ)               = ⊢SΓ , t[σ] (vlookup ⊢Γ T∈Γ) (s-wk ⊢SΓ) , vlookup ⊢SΓ (there ⊢Γ ⊢S T∈Γ) , t[σ]-Se (∈⇒ty-wf ⊢Γ T∈Γ) (s-wk ⊢SΓ)
    where ⊢SΓ = ⊢∷ ⊢Γ ⊢S
  presup-≈ ([∘] ⊢τ ⊢σ ⊢t)
    with ⊢Γ ← proj₁ (presup-s ⊢τ)
       | _ , ⊢T ← presup-tm ⊢t            = ⊢Γ , t[σ] ⊢t (s-∘ ⊢τ ⊢σ) , conv (t[σ] (t[σ] ⊢t ⊢σ) ⊢τ) ([∘]-Se ⊢T ⊢σ ⊢τ) , t[σ]-Se ⊢T (s-∘ ⊢τ ⊢σ)
  presup-≈ ([,]-v-ze ⊢σ ⊢S ⊢t)
    with ⊢Γ , ⊢Δ ← presup-s ⊢σ            = ⊢Γ
                                          , conv (t[σ] (vlookup ⊢SΔ (here ⊢Δ ⊢S)) ⊢σ,t) (≈-trans ([∘]-Se ⊢S (s-wk ⊢SΔ) ⊢σ,t) ([]-cong-Se″ ⊢S (s-∘ ⊢σ,t (s-wk ⊢SΔ)) (p-, ⊢σ ⊢S ⊢t)))
                                          , ⊢t , t[σ]-Se ⊢S ⊢σ
    where
      ⊢SΔ  = ⊢∷ ⊢Δ ⊢S
      ⊢σ,t = s-, ⊢σ ⊢S ⊢t
  presup-≈ ([,]-v-su ⊢Δ ⊢σ ⊢S ⊢s T∈Δ)
    with ⊢Γ , _ ← presup-s ⊢σ
       | ⊢T ← ∈⇒ty-wf ⊢Δ T∈Δ              = ⊢Γ
                                          , conv (t[σ] (vlookup ⊢SΔ (there ⊢Δ ⊢S T∈Δ)) ⊢σ,s)
                                                 (≈-trans ([∘]-Se ⊢T (s-wk ⊢SΔ) ⊢σ,s) ([]-cong-Se″ ⊢T (s-∘ ⊢σ,s (s-wk ⊢SΔ)) (wk∘[σ,t]≈σ ⊢SΔ ⊢σ ⊢s)))
                                          , t[σ] (vlookup ⊢Δ T∈Δ) ⊢σ , t[σ]-Se ⊢T ⊢σ
    where
      ⊢SΔ  = ⊢∷ ⊢Δ ⊢S
      ⊢σ,s = s-, ⊢σ ⊢S ⊢s
  presup-≈ (≈-conv s≈t S≈T)
    with ⊢Γ , ⊢s , ⊢t , _ ← presup-≈ s≈t
       | _ , _ , ⊢T , _ ← presup-≈ S≈T    = ⊢Γ , conv ⊢s S≈T , conv ⊢t S≈T , ⊢T
  presup-≈ (≈-sym t≈s)
    with ⊢Γ , ⊢t , ⊢s , ⊢T ← presup-≈ t≈s = ⊢Γ , ⊢s , ⊢t , ⊢T
  presup-≈ (≈-trans s≈t′ t′≈t)
    with ⊢Γ , ⊢s , _ ← presup-≈ s≈t′
       | _ , _ , ⊢t , ⊢T ← presup-≈ t′≈t  = ⊢Γ , ⊢s , ⊢t , ⊢T


  presup-s-≈ : Γ ⊢s σ ≈ τ ∶ Δ →
               -----------------------------------
               ⊢ Γ × Γ ⊢s σ ∶ Δ × Γ ⊢s τ ∶ Δ × ⊢ Δ
  presup-s-≈ (I-≈ ⊢Γ)                          = ⊢Γ , s-I ⊢Γ , s-I ⊢Γ , ⊢Γ
  presup-s-≈ (wk-≈ ⊢TΓ@(⊢∷ ⊢Γ _))              = ⊢TΓ , s-wk ⊢TΓ , s-wk ⊢TΓ , ⊢Γ
  presup-s-≈ (∘-cong σ≈σ′ τ≈τ′)
    with ⊢Γ , ⊢σ , ⊢σ′ , _ ← presup-s-≈ σ≈σ′
       | _  , ⊢τ , ⊢τ′ , ⊢Δ ← presup-s-≈ τ≈τ′  = ⊢Γ , s-∘ ⊢σ ⊢τ , s-∘ ⊢σ′ ⊢τ′ , ⊢Δ
  presup-s-≈ (,-cong σ≈τ ⊢T t≈t′)
    with ⊢Γ , ⊢σ , ⊢τ , ⊢Δ ← presup-s-≈ σ≈τ
       | _  , ⊢t , ⊢t′ , _ ← presup-≈ t≈t′     = ⊢Γ , s-, ⊢σ ⊢T ⊢t , s-, ⊢τ ⊢T (conv ⊢t′ ([]-cong-Se″ ⊢T ⊢σ σ≈τ)) , ⊢∷ ⊢Δ ⊢T
  presup-s-≈ (I-∘ ⊢σ)
    with ⊢Γ , ⊢Δ ← presup-s ⊢σ                 = ⊢Γ , s-∘ ⊢σ (s-I ⊢Δ) , ⊢σ , ⊢Δ
  presup-s-≈ (∘-I ⊢σ)
    with ⊢Γ , ⊢Δ ← presup-s ⊢σ                 = ⊢Γ , s-∘ (s-I ⊢Γ) ⊢σ , ⊢σ , ⊢Δ
  presup-s-≈ (∘-assoc ⊢σ ⊢σ′ ⊢σ″)              = proj₁ (presup-s ⊢σ″) , s-∘ ⊢σ″ (s-∘ ⊢σ′ ⊢σ) , s-∘ (s-∘ ⊢σ″ ⊢σ′) ⊢σ , proj₂ (presup-s ⊢σ)
  presup-s-≈ (,-∘ ⊢σ ⊢T ⊢t ⊢τ)                 = proj₁ (presup-s ⊢τ) , s-∘ ⊢τ (s-, ⊢σ ⊢T ⊢t) , s-, (s-∘ ⊢τ ⊢σ) ⊢T (conv (t[σ] ⊢t ⊢τ) ([∘]-Se ⊢T ⊢σ ⊢τ)) , ⊢∷ (proj₂ (presup-s ⊢σ)) ⊢T
  presup-s-≈ (p-, ⊢τ ⊢T ⊢t)
    with ⊢Γ , ⊢Δ ← presup-s ⊢τ                 = ⊢Γ , ⊢p (⊢∷ ⊢Δ ⊢T) (s-, ⊢τ ⊢T ⊢t) , ⊢τ , ⊢Δ
  presup-s-≈ (,-ext ⊢σ)
    with ⊢Γ , ⊢TΔ@(⊢∷ ⊢Δ ⊢T) ← presup-s ⊢σ     = ⊢Γ , ⊢σ , s-, (⊢p ⊢TΔ ⊢σ) ⊢T (conv (t[σ] (vlookup ⊢TΔ (here ⊢Δ ⊢T)) ⊢σ) (≈-trans ([∘]-Se ⊢T (s-wk ⊢TΔ) ⊢σ) (≈-refl (t[σ]-Se ⊢T (⊢p ⊢TΔ ⊢σ))))) , ⊢TΔ
  presup-s-≈ (s-≈-sym σ≈τ)
    with ⊢Γ , ⊢σ , ⊢τ , ⊢Δ ← presup-s-≈ σ≈τ    = ⊢Γ , ⊢τ , ⊢σ , ⊢Δ
  presup-s-≈ (s-≈-trans σ≈σ′ σ′≈σ″)
    with ⊢Γ , ⊢σ , ⊢σ′ , _ ← presup-s-≈ σ≈σ′
       | _  , _  , ⊢σ″ , ⊢Δ ← presup-s-≈ σ′≈σ″ = ⊢Γ , ⊢σ , ⊢σ″ , ⊢Δ
  presup-s-≈ (s-≈-conv σ≈τ Δ′≈Δ)
    with ⊢Γ , ⊢σ , ⊢τ , ⊢Δ′ ← presup-s-≈ σ≈τ   = ⊢Γ , s-conv ⊢σ Δ′≈Δ , s-conv ⊢τ Δ′≈Δ , proj₂ (presup-⊢≈ Δ′≈Δ)
