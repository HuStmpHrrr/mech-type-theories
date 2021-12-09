{-# OPTIONS --without-K --safe #-}

module kMLTT.Statics.Presup where

open import Data.Nat.Properties as ℕ

open import Lib
open import kMLTT.Statics.Full
open import kMLTT.Statics.Refl
open import kMLTT.Statics.Misc
open import kMLTT.Statics.CtxEquiv
open import kMLTT.Statics.PER
open import kMLTT.Statics.Properties.Pi
open import kMLTT.Statics.Properties.Box
open import kMLTT.Statics.Properties.Contexts
open import kMLTT.Statics.Properties.Substs
open import kMLTT.Statics.Properties.Ops

mutual
  presup-tm : Γ ⊢ t ∶ T →
              ------------
              ⊢ Γ × Γ ⊢ T
  presup-tm (N-wf i ⊢Γ)           = ⊢Γ , suc i , Se-wf i ⊢Γ
  presup-tm (Se-wf i ⊢Γ)          = ⊢Γ , suc (suc i) , Se-wf (suc i) ⊢Γ
  presup-tm (Π-wf ⊢S ⊢T)          = presup-tm ⊢S
  presup-tm (□-wf {i = i} ⊢T)
    with presup-tm ⊢T
  ... | ⊢κ ⊢Γ , _                 = ⊢Γ , suc i , Se-wf i ⊢Γ
  presup-tm (vlookup ⊢Γ T∈Γ)      = ⊢Γ , ∈!⇒ty-wf ⊢Γ T∈Γ
  presup-tm (ze-I ⊢T)             = ⊢T , zero , N-wf zero ⊢T
  presup-tm (su-I ⊢t)             = presup-tm ⊢t
  presup-tm (N-E ⊢T ⊢s ⊢r ⊢t)
    with presup-tm ⊢t
  ...  | ⊢Γ , _                   = ⊢Γ , _ , t[σ]-Se ⊢T (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) ⊢t)
  presup-tm (Λ-I ⊢S ⊢t)
    with presup-tm ⊢t
  ... | ⊢∷ ⊢Γ ⊢S , _ , ⊢T         = ⊢Γ , _ , Π-wf (lift-⊢-Se-max ⊢S) (lift-⊢-Se-max′ ⊢T)
  presup-tm (Λ-E ⊢t ⊢s)
    with presup-tm ⊢s | presup-tm ⊢t
  ...  | _  , _ , ⊢S
       | ⊢Γ , _ , ⊢Π              = ⊢Γ , _ , t[σ]-Se (proj₂ (inv-Π-wf ⊢Π)) (⊢I,t ⊢Γ ⊢S ⊢s)
  presup-tm (□-I ⊢t)
    with presup-tm ⊢t
  ...  | ⊢κ ⊢Γ , _ , ⊢T           = ⊢Γ , _ , □-wf ⊢T
  presup-tm (□-E Ψs ⊢t ⊢ΨsΓ eq)
    with presup-tm ⊢t
  ...  | ⊢Γ , _ , ⊢□T             = ⊢ΨsΓ , _ , t[σ]-Se (proj₂ (inv-□-wf ⊢□T)) (s-； Ψs (s-I ⊢Γ) ⊢ΨsΓ eq)
  presup-tm (t[σ] ⊢t ⊢σ)
    with presup-tm ⊢t | presup-s ⊢σ
  ...  | _ , _ , ⊢T | ⊢Γ , _      = ⊢Γ , _ , t[σ]-Se ⊢T ⊢σ
  presup-tm (cumu ⊢T)
    with presup-tm ⊢T
  ...  | ⊢Γ , _                   = ⊢Γ , suc (suc _) , Se-wf (suc _) ⊢Γ
  presup-tm (conv ⊢t S≈T)
    with presup-≈ S≈T
  ...  | ⊢Γ , _ , ⊢T , _          = ⊢Γ , _ , ⊢T


  presup-s : Γ ⊢s σ ∶ Δ →
             ------------
             ⊢ Γ × ⊢ Δ
  presup-s (s-I ⊢Γ)             = ⊢Γ , ⊢Γ
  presup-s (s-wk ⊢TΓ@(⊢∷ ⊢Γ _)) = ⊢TΓ , ⊢Γ
  --   with presup-s ⊢σ
  -- ... | ⊢Γ , ⊢∷ ⊢Δ _            = ⊢Γ , ⊢Δ
  presup-s (s-∘ ⊢σ ⊢δ)
    with presup-s ⊢σ | presup-s ⊢δ
  ...  | ⊢Γ , _ | _ , ⊢Δ        = ⊢Γ , ⊢Δ
  presup-s (s-, ⊢σ ⊢T ⊢t)
    with presup-s ⊢σ
  ... | ⊢Γ , ⊢Δ                 = ⊢Γ , ⊢∷ ⊢Δ ⊢T
  presup-s (s-； Ψs ⊢σ ⊢ΨsΓ eq)
    with presup-s ⊢σ
  ... | _ , ⊢Δ                  = ⊢ΨsΓ , ⊢κ ⊢Δ
  presup-s (s-conv ⊢σ Δ′≈Δ)
    with presup-s ⊢σ
  ... | ⊢Γ , _                  = ⊢Γ , proj₂ (presup-⊢≈ Δ′≈Δ)


  presup-≈ : Γ ⊢ s ≈ t ∶ T →
             -----------------------------------
             ⊢ Γ × Γ ⊢ s ∶ T × Γ ⊢ t ∶ T × Γ ⊢ T
  presup-≈ (N-[] i ⊢σ)
    with presup-s ⊢σ
  ... | ⊢Γ , ⊢Δ      = ⊢Γ , t[σ]-Se (N-wf _ ⊢Δ) ⊢σ , N-wf _ ⊢Γ , _ , Se-wf _ ⊢Γ
  presup-≈ (Se-[] i ⊢σ)
    with presup-s ⊢σ
  ... | ⊢Γ , ⊢Δ      = ⊢Γ , t[σ]-Se (Se-wf _ ⊢Δ) ⊢σ , Se-wf _ ⊢Γ , _ , Se-wf _ ⊢Γ
  presup-≈ (Π-[] ⊢σ ⊢S ⊢T)
    with presup-s ⊢σ
  ... | ⊢Γ , ⊢Δ      = ⊢Γ
                     , t[σ]-Se (Π-wf ⊢S ⊢T) ⊢σ
                     , Π-wf (t[σ]-Se ⊢S ⊢σ) (t[σ]-Se ⊢T (⊢q ⊢Γ ⊢σ ⊢S))
                     , _ , Se-wf _ ⊢Γ
  presup-≈ (□-[] ⊢σ ⊢T)
    with presup-s ⊢σ
  ... | ⊢Γ , ⊢Δ      = ⊢Γ , t[σ]-Se (□-wf ⊢T) ⊢σ , □-wf (t[σ]-Se ⊢T (⊢σ；1 (⊢κ ⊢Γ) ⊢σ)) , _ , Se-wf _ ⊢Γ
  presup-≈ (Π-cong ⊢S S≈S′ T≈T′)
    with presup-≈ S≈S′   | presup-≈ T≈T′
  ... | ⊢Γ , ⊢S , ⊢S′ , _ | _ , ⊢T , ⊢T′ , _  = ⊢Γ , Π-wf ⊢S ⊢T , Π-wf ⊢S′ (ctxeq-tm (∷-cong′ ⊢Γ ⊢S ⊢S′ S≈S′) ⊢T′) , _ , Se-wf _ ⊢Γ
  presup-≈ (□-cong T≈T′)
    with presup-≈ T≈T′
  ... | ⊢κ ⊢Γ , ⊢T , ⊢T′ , _ = ⊢Γ , □-wf ⊢T , □-wf ⊢T′ , _ , Se-wf _ ⊢Γ
  presup-≈ (v-≈ ⊢Γ T∈Γ) = ⊢Γ , vlookup ⊢Γ T∈Γ , vlookup ⊢Γ T∈Γ , _ , proj₂ (∈!⇒ty-wf ⊢Γ T∈Γ)
  presup-≈ (ze-≈ ⊢Γ) = ⊢Γ , ze-I ⊢Γ , ze-I ⊢Γ , _ , N-wf 0 ⊢Γ
  presup-≈ (su-cong t≈t′)
    with presup-≈ t≈t′
  ... | ⊢Γ , ⊢t , ⊢t′ , _ = ⊢Γ , su-I ⊢t , su-I ⊢t′ , _ , N-wf 0 ⊢Γ
  presup-≈ (rec-cong ⊢T T≈T′ s≈s′ r≈r′ t≈t′)
    with presup-≈ T≈T′     | presup-≈ s≈s′     | presup-≈ r≈r′       | presup-≈ t≈t′
  ... | ⊢NΓ , ⊢T , ⊢T′ , _ | ⊢Γ , ⊢s , ⊢s′ , _ | ⊢TNΓ , ⊢r , ⊢r′ , _ | _ , ⊢t , ⊢t′ , _
      = ⊢Γ
      , N-E ⊢T ⊢s ⊢r ⊢t
      , conv (N-E ⊢T′ (conv ⊢s′ ([]-cong-Se′ T≈T′ (⊢I,ze ⊢Γ))) (ctxeq-tm (∷-cong′ ⊢NΓ ⊢T ⊢T′ T≈T′) (conv ⊢r′ ([]-cong-Se′ T≈T′ (⊢[wk∘wk],su[v1] ⊢TNΓ)))) ⊢t′) (≈-sym ([]-cong-Se T≈T′ (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) ⊢t) (,-cong (I-≈ ⊢Γ) (N-wf 0 ⊢Γ) (≈-conv-N-[]-sym t≈t′ (s-I ⊢Γ)))))
      , _ , (t[σ]-Se ⊢T (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) ⊢t))
  presup-≈ (Λ-cong ⊢S t≈t′)
    with presup-≈ t≈t′
  ... | ⊢∷ ⊢Γ _ , ⊢t , ⊢t′ , _ , ⊢T = ⊢Γ , Λ-I ⊢S ⊢t , Λ-I ⊢S ⊢t′ , _ , Π-wf (lift-⊢-Se-max ⊢S) (lift-⊢-Se-max′ ⊢T)
  presup-≈ ($-cong r≈r′ s≈s′)
    with presup-≈ r≈r′           | presup-≈ s≈s′
  ... | ⊢Γ , ⊢r , ⊢r′ , _ , ⊢ΠST | _ , ⊢s , ⊢s′ , _
      with inv-Π-wf′ ⊢ΠST | inv-Π-wf ⊢ΠST
  ...   | _ , ⊢S          | _ , ⊢T           = ⊢Γ
                                             , Λ-E ⊢r ⊢s
                                             , conv (Λ-E ⊢r′ ⊢s′) ([]-cong-Se″ ⊢T (⊢I,t ⊢Γ ⊢S ⊢s′) (,-cong (I-≈ ⊢Γ) ⊢S (≈-conv (≈-sym s≈s′) (≈-sym ([I] ⊢S)))))
                                             , _ , t[σ]-Se ⊢T (⊢I,t ⊢Γ ⊢S ⊢s)
  presup-≈ (box-cong t≈t′)
    with presup-≈ t≈t′
  ... | ⊢κ ⊢Γ , ⊢t , ⊢t′ , _ , ⊢T     = ⊢Γ , □-I ⊢t , □-I ⊢t′ , _ , □-wf ⊢T
  presup-≈ (unbox-cong Ψs t≈t′ ⊢ΨsΓ eq)
    with presup-≈ t≈t′
  ... | ⊢Γ , ⊢t , ⊢t′ , _ , ⊢□T
      with inv-□-wf ⊢□T
  ...   | _ , ⊢T               = ⊢ΨsΓ , □-E Ψs ⊢t ⊢ΨsΓ eq , □-E Ψs ⊢t′ ⊢ΨsΓ eq , _ , t[σ]-Se ⊢T (s-； Ψs (s-I ⊢Γ) ⊢ΨsΓ eq)
  presup-≈ ([]-cong t≈t′ σ≈σ′)
    with presup-≈ t≈t′        | presup-s-≈ σ≈σ′
  ... | _ , ⊢t , ⊢t′ , _ , ⊢T | ⊢Γ , ⊢σ , ⊢σ′ , _  = ⊢Γ , t[σ] ⊢t ⊢σ , conv (t[σ] ⊢t′ ⊢σ′) ([]-cong-Se″ ⊢T ⊢σ′ (s-≈-sym σ≈σ′)) , _ , t[σ]-Se ⊢T ⊢σ
  presup-≈ (ze-[] ⊢σ)
    with presup-s ⊢σ
  ... | ⊢Γ , ⊢Δ          = ⊢Γ , t[σ]-N (ze-I ⊢Δ) ⊢σ , ze-I ⊢Γ , _ , N-wf 0 ⊢Γ
  presup-≈ (su-[] ⊢σ ⊢t)
    with presup-s ⊢σ
  ... | ⊢Γ , _           = ⊢Γ , t[σ]-N (su-I ⊢t) ⊢σ , su-I (t[σ]-N ⊢t ⊢σ) , _ , N-wf 0 ⊢Γ
  presup-≈ (rec-[] {Γ = Γ} {σ = σ} {Δ = Δ} {T = T} {t = t} {i = i} ⊢σ ⊢T ⊢s ⊢r ⊢t)
    -- FIXME! This proof is crazy (and tons of redundancy).
    with presup-s ⊢σ
  ... | ⊢Γ , ⊢Δ          = ⊢Γ
                         , conv
                             (t[σ] (N-E ⊢T ⊢s ⊢r ⊢t) ⊢σ)
                             (ER.begin
                                T [| t ] [ σ ]
                              ER.≈⟨ [∘]-Se ⊢T (⊢I,t ⊢Δ (N-wf 0 ⊢Δ) ⊢t) ⊢σ ⟩
                                T [ (I , t) ∘ σ ]
                              ER.≈⟨ []-cong-Se″ ⊢T (s-∘ ⊢σ (⊢I,t ⊢Δ (N-wf 0 ⊢Δ) ⊢t)) ([I,t]∘σ≈σ,t[σ] ⊢NΔ ⊢σ ⊢t) ⟩
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
                                  ER.≈˘⟨ [∘]-Se ⊢T ⊢qσ (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) (ze-I ⊢Γ)) ⟩
                                    T [ q σ ] [| ze ]
                                  ER.∎))
                               (conv (t[σ] ⊢r ⊢q[qσ]) (by-[∘] ([]-cong-Se″ ⊢T (s-∘ ⊢q[qσ] ⊢[wk∘wk],su[v1]′) lemmaT)))
                               (t[σ]-N ⊢t ⊢σ))
                             (≈-trans
                               ([∘]-Se ⊢T ⊢qσ (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) (t[σ]-N ⊢t ⊢σ)))
                               ([]-cong-Se″ ⊢T (s-∘ (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) (t[σ]-N ⊢t ⊢σ)) ⊢qσ) (qσ∘[I,t]≈σ,t ⊢Γ (N-wf 0 ⊢Δ) ⊢σ (t[σ] ⊢t ⊢σ))))
                          , _ , t[σ]-Se ⊢T (s-, ⊢σ (N-wf 0 ⊢Δ) (t[σ] ⊢t ⊢σ))
    where
      ⊢qσ = ⊢q-N ⊢Γ ⊢Δ ⊢σ
      ⊢T[qσ] = t[σ]-Se ⊢T ⊢qσ
      ⊢NΓ = ⊢∷ ⊢Γ (N-wf 0 ⊢Γ)
      ⊢q[qσ] = ⊢q ⊢NΓ ⊢qσ ⊢T
      ⊢T[qσ]NΓ = ⊢∷ ⊢NΓ ⊢T[qσ]
      ⊢NΔ = ⊢∷ ⊢Δ (N-wf 0 ⊢Δ)
      ⊢TNΔ = ⊢∷ ⊢NΔ ⊢T

      ⊢wk∘wk = (s-∘ (s-wk ⊢TNΔ) (s-wk ⊢NΔ))
      ⊢wk∘wk′ = (s-∘ (s-wk ⊢T[qσ]NΓ) (s-wk ⊢NΓ))
      ⊢v1 = ⊢vn∶N L.[ T ] ⊢TNΔ refl
      ⊢v1′ = ⊢vn∶N L.[ T [ q σ ] ] ⊢T[qσ]NΓ refl
      ⊢su[v1] = conv-N-[]-sym (su-I ⊢v1) ⊢wk∘wk
      ⊢su[v1]′ = conv-N-[]-sym (su-I ⊢v1′) ⊢wk∘wk′
      ⊢[wk∘wk],su[v1]′ = ⊢[wk∘wk],su[v1] ⊢TNΔ
      ⊢[wk∘wk],su[v1]′′ = ⊢[wk∘wk],su[v1] ⊢T[qσ]NΓ
      ⊢qσ∘wk = s-∘ (s-wk ⊢T[qσ]NΓ) ⊢qσ
      ⊢σ∘wk = s-∘ (s-wk ⊢NΓ) ⊢σ
      ⊢σ∘wk∘wk = s-∘ (s-wk ⊢T[qσ]NΓ) ⊢σ∘wk

      by-[∘] : (T [ q σ ]) ∺ N ∺ Γ ⊢ T [ ((wk ∘ wk) , su (v 1)) ∘ q (q σ) ] ≈ T [ q σ ∘ ((wk ∘ wk) , su (v 1)) ] ∶ Se i →
               (T [ q σ ]) ∺ N ∺ Γ ⊢ T [ ((wk ∘ wk) , su (v 1)) ] [ q (q σ) ] ≈ T [ q σ ] [ ((wk ∘ wk) , su (v 1)) ] ∶ Se i
      by-[∘] x = ≈-trans ([∘]-Se ⊢T ⊢[wk∘wk],su[v1]′ ⊢q[qσ]) (≈-trans x (≈-sym ([∘]-Se ⊢T ⊢qσ ⊢[wk∘wk],su[v1]′′)))

      lemmaT : (T [ q σ ]) ∺ N ∺ Γ ⊢s ((wk ∘ wk) , su (v 1)) ∘ q (q σ) ≈ q σ ∘ ((wk ∘ wk) , su (v 1)) ∶ N ∺ Δ
      lemmaT =
        begin
          ((wk ∘ wk) , su (v 1)) ∘ q (q σ)
        ≈⟨ ,-∘ ⊢wk∘wk (N-wf 0 ⊢Δ) ⊢su[v1] ⊢q[qσ] ⟩
          (wk ∘ wk ∘ q (q σ)) , su (v 1) [ q (q σ) ]
        ≈⟨ ,-cong lemmaT-l (N-wf 0 ⊢Δ) (≈-conv-N-[]-sym lemmaT-r (s-∘ ⊢q[qσ] ⊢wk∘wk)) ⟩
          (σ ∘ wk ∘ ((wk ∘ wk) , su (v 1))) , v 0 [ (wk ∘ wk) , su (v 1) ]
        ≈˘⟨ ,-∘ ⊢σ∘wk (N-wf 0 ⊢Δ) (conv (⊢vn∶N [] ⊢NΓ refl) (≈-sym (N-[] 0 ⊢σ∘wk))) ⊢[wk∘wk],su[v1]′′ ⟩
          q σ ∘ ((wk ∘ wk) , su (v 1))
        ∎
        where
          lemmaT-r : (T [ q σ ]) ∺ N ∺ Γ ⊢ su (v 1) [ q (q σ) ] ≈ v 0 [ (wk ∘ wk) , su (v 1) ] ∶ N
          lemmaT-r =
            begin
              su (v 1) [ q (q σ) ]
            ≈⟨ su-[] ⊢q[qσ] ⊢v1 ⟩
              su (v 1 [ q (q σ) ])
            ≈⟨ su-cong (≈-conv ([,]-v-su ⊢qσ∘wk ⊢T (conv (vlookup ⊢T[qσ]NΓ here) ([∘]-Se ⊢T ⊢qσ (s-wk ⊢T[qσ]NΓ))) here) (N-[][] 0 (s-wk ⊢NΔ) ⊢qσ∘wk)) ⟩
              su (v 0 [ q σ ∘ wk ])
            ≈⟨ su-cong ([]-cong-N″ (⊢vn∶N [] ⊢NΔ refl) ⊢qσ∘wk (,-∘ ⊢σ∘wk (N-wf 0 ⊢Δ) (conv (⊢vn∶N L.[] ⊢NΓ refl) (≈-sym (N-[] 0 ⊢σ∘wk))) (s-wk ⊢T[qσ]NΓ))) ⟩
              su (v 0 [ (σ ∘ wk ∘ wk) , v 0 [ wk ] ])
            ≈⟨ su-cong (≈-conv-N-[] ([,]-v-ze ⊢σ∘wk∘wk (N-wf 0 ⊢Δ) (conv (t[σ] (conv (⊢vn∶N L.[] ⊢NΓ refl) (≈-sym (N-[] 0 ⊢σ∘wk))) (s-wk ⊢T[qσ]NΓ)) ([∘]-Se (N-wf 0 ⊢Δ) ⊢σ∘wk (s-wk ⊢T[qσ]NΓ)))) ⊢σ∘wk∘wk) ⟩
              su (v 0 [ wk ])
            ≈⟨ su-cong (≈-conv (≈-trans ([wk] ⊢T[qσ]NΓ here) (≈-sym ([I] (⊢vn∶T[wk]suc[n] {Ψ = L.[ T [ q σ ] ]} ⊢T[qσ]NΓ refl)))) (N-[][] 0 (s-wk ⊢NΓ) (s-wk ⊢T[qσ]NΓ))) ⟩
              su (v 1 [ I ])
            ≈⟨ su-cong ([I] ⊢v1′) ⟩
              su (v 1)
            ≈˘⟨ ≈-conv-N-[] ([,]-v-ze ⊢wk∘wk′ (N-wf 0 ⊢Γ) ⊢su[v1]′) ⊢wk∘wk′ ⟩
              v 0 [ (wk ∘ wk) , su (v 1) ]
            ∎
            where
              open ER

          open SR

          lemmaT-l : (T [ q σ ]) ∺ N ∺ Γ ⊢s wk ∘ wk ∘ q (q σ) ≈ σ ∘ wk ∘ ((wk ∘ wk) , su (v 1)) ∶ Δ
          lemmaT-l =
            begin
              wk ∘ wk ∘ q (q σ)
            ≈⟨ [wk∘wk]∘q[qσ]≈σ∘[wk∘wk]-TN ⊢Γ ⊢TNΔ ⊢σ ⟩
              σ ∘ (wk ∘ wk)
            ≈˘⟨ ∘-cong (wk∘[σ,t]≈σ ⊢NΓ ⊢wk∘wk′ ⊢su[v1]′) (s-≈-refl ⊢σ) ⟩
              σ ∘ (wk ∘ ((wk ∘ wk), su (v 1)))
            ≈˘⟨ ∘-assoc ⊢σ (s-wk ⊢NΓ) ⊢[wk∘wk],su[v1]′′ ⟩
              (σ ∘ wk ∘ ((wk ∘ wk) , su (v 1)))
            ∎
  presup-≈ (Λ-[] ⊢σ ⊢t)
    with presup-s ⊢σ | presup-tm ⊢t
  ... | ⊢Γ , _       | ⊢∷ _ ⊢S , _ , ⊢T = ⊢Γ , t[σ] (Λ-I ⊢S ⊢t) ⊢σ , conv (Λ-I (t[σ]-Se ⊢S ⊢σ) (t[σ] ⊢t (⊢q ⊢Γ ⊢σ ⊢S))) (≈-sym (Π-[] ⊢σ (lift-⊢-Se-max ⊢S) (lift-⊢-Se-max′ ⊢T))) , _ , t[σ]-Se (Π-wf (lift-⊢-Se-max ⊢S) (lift-⊢-Se-max′ ⊢T)) ⊢σ
  presup-≈ ($-[] ⊢σ ⊢r ⊢s)
    with presup-s ⊢σ | presup-tm ⊢r
  ... | ⊢Γ , ⊢Δ      | _ , _ , ⊢ΠST
      with inv-Π-wf′ ⊢ΠST | inv-Π-wf ⊢ΠST
  ...   | _ , ⊢S          | _ , ⊢T        = ⊢Γ , conv (t[σ] (Λ-E ⊢r ⊢s) ⊢σ) (≈-trans ([∘]-Se ⊢T (⊢I,t ⊢Δ ⊢S ⊢s) ⊢σ) ([]-cong-Se″ ⊢T (s-∘ ⊢σ (⊢I,t ⊢Δ ⊢S ⊢s)) ([I,t]∘σ≈σ,t[σ] (⊢∷ ⊢Δ ⊢S) ⊢σ ⊢s))) , conv (Λ-E (conv (t[σ] ⊢r ⊢σ) (Π-[] ⊢σ (lift-⊢-Se-max ⊢S) (lift-⊢-Se-max′ ⊢T))) (t[σ] ⊢s ⊢σ)) (≈-trans ([∘]-Se ⊢T (⊢q ⊢Γ ⊢σ ⊢S) (⊢I,t ⊢Γ (t[σ]-Se ⊢S ⊢σ) (t[σ] ⊢s ⊢σ))) ([]-cong-Se″ ⊢T (s-∘ (⊢I,t ⊢Γ (t[σ]-Se ⊢S ⊢σ) (t[σ] ⊢s ⊢σ)) (⊢q ⊢Γ ⊢σ ⊢S)) (qσ∘[I,t]≈σ,t ⊢Γ ⊢S ⊢σ (t[σ] ⊢s ⊢σ)))) , _ , t[σ]-Se ⊢T (s-, ⊢σ ⊢S (t[σ] ⊢s ⊢σ))
  presup-≈ (box-[] ⊢σ ⊢t)
    with presup-s ⊢σ | presup-tm ⊢t
  ... | ⊢Γ , ⊢Δ      | _ , _ , ⊢T        = ⊢Γ , t[σ] (□-I ⊢t) ⊢σ , conv (□-I (t[σ] ⊢t (s-； L.[ [] ] ⊢σ (⊢κ ⊢Γ) refl))) (≈-sym (□-[] ⊢σ ⊢T)) , _ , t[σ]-Se (□-wf ⊢T) ⊢σ
  presup-≈ (unbox-[] Ψ ⊢t ⊢σ eqΨ)
    with presup-s ⊢σ | presup-tm ⊢t | ∥-⊢s′ Ψ ⊢σ
  ... | ⊢Γ , ⊢ΨΔ     | _ , _ , ⊢□T   | Ψ′ , Γ′ , refl , eqΨ′ , ⊢σ∥
      rewrite eqΨ
        with inv-□-wf ⊢□T
  ...     | _ , ⊢T         = ⊢Γ , conv (t[σ] (□-E Ψ ⊢t ⊢ΨΔ eqΨ) ⊢σ) (≈-trans ([∘]-Se ⊢T ⊢I；n ⊢σ) ([]-cong-Se″ ⊢T (s-∘ ⊢σ ⊢I；n) (s-≈-trans (；-∘ Ψ (s-I ⊢Δ) ⊢σ ⊢ΨΔ eqΨ) (；-cong Ψ′ (I-∘ ⊢σ∥) ⊢Γ eqΨ′)))) , conv (□-E Ψ′ (conv (t[σ] ⊢t ⊢σ∥) (□-[] ⊢σ∥ ⊢T)) ⊢Γ eqΨ′) (≈-trans ([∘]-Se ⊢T ⊢σ∥；1 ⊢I；Lσn) ([]-cong-Se″ ⊢T (s-∘ ⊢I；Lσn ⊢σ∥；1) (s-≈-trans (；-∘ L.[ [] ] ⊢σ∥ ⊢I；Lσn (⊢κ ⊢Γ′) refl) (s-≈-trans (s-≈-sym (；-≡-cong Ψ′ (s-∘ (s-I ⊢Γ′) ⊢σ∥) ⊢Γ eqΨ′ (sym (+-identityʳ _)))) (；-cong Ψ′ (∘-I ⊢σ∥) ⊢Γ eqΨ′))))) , _ , (t[σ]-Se ⊢T (s-； Ψ′ ⊢σ∥ ⊢Γ eqΨ′))
    where
      ⊢Γ′ = ⊢⇒∥⊢ Ψ′ ⊢Γ
      ⊢Δ = ⊢⇒∥⊢ Ψ ⊢ΨΔ
      ⊢I；n = s-； Ψ (s-I ⊢Δ) ⊢ΨΔ eqΨ
      ⊢I；Lσn = s-； Ψ′ (s-I ⊢Γ′) ⊢Γ eqΨ′
      ⊢σ∥；1 = s-； L.[ [] ] ⊢σ∥ (⊢κ ⊢Γ′) refl
  presup-≈ (rec-β-ze ⊢T ⊢t ⊢r)
    with presup-tm ⊢t
  ... | ⊢Γ , _            = ⊢Γ , N-E ⊢T ⊢t ⊢r (ze-I ⊢Γ) , ⊢t , _ , t[σ]-Se ⊢T (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) (ze-I ⊢Γ))
  presup-≈ (rec-β-su {Γ = Γ} {T = T} {s = s} {r = r} {t = t} ⊢T ⊢s ⊢r ⊢t)
    with presup-tm ⊢r
  ... | ⊢TNΓ@(⊢∷ ⊢NΓ@(⊢∷ ⊢Γ _) _) , _ = ⊢Γ , N-E ⊢T ⊢s ⊢r (su-I ⊢t) , conv (t[σ] ⊢r ⊢I,t,recTrst) (≈-trans ([∘]-Se ⊢T ⊢[wk∘wk],su[v1]′ ⊢I,t,recTrst) ([]-cong-Se″ ⊢T (s-∘ ⊢I,t,recTrst ⊢[wk∘wk],su[v1]′) lemma)) , _ , t[σ]-Se ⊢T (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) (su-I ⊢t))
    where
      ⊢recTsrt = N-E ⊢T ⊢s ⊢r ⊢t
      ⊢I,t,recTrst = s-, (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) ⊢t) ⊢T (N-E ⊢T ⊢s ⊢r ⊢t)
      ⊢wk∘wk = s-∘ (s-wk ⊢TNΓ) (s-wk ⊢NΓ)
      ⊢[wk∘wk],su[v1]′ = s-, ⊢wk∘wk (N-wf 0 ⊢Γ) (conv-N-[]-sym (su-I (⊢vn∶N L.[ T ] ⊢TNΓ refl)) ⊢wk∘wk)

      lemma : Γ ⊢s ((wk ∘ wk) , su (v 1)) ∘ ((I , t) , rec T s r t) ≈ I , su t ∶ N ∺ Γ
      lemma =
        begin
          ((wk ∘ wk) , su (v 1)) ∘ ((I , t) , rec T s r t)
        ≈⟨ ,-∘ ⊢wk∘wk (N-wf 0 ⊢Γ) (conv-N-[]-sym (su-I (⊢vn∶N L.[ T ] ⊢TNΓ refl)) ⊢wk∘wk) ⊢I,t,recTrst ⟩
          (wk ∘ wk ∘ ((I , t) , rec T s r t)) , su (v 1) [ (I , t) , rec T s r t ]
        ≈⟨ ,-cong lemma-l (N-wf 0 ⊢Γ) (≈-conv-N-[]-sym lemma-r (s-∘ ⊢I,t,recTrst ⊢wk∘wk)) ⟩
          I , su t
        ∎
        where
          lemma-r : Γ ⊢ su (v 1) [ (I , t) , rec T s r t ] ≈ su t ∶ N
          lemma-r =
            begin
              su (v 1) [ (I , t) , rec T s r t ]
            ≈⟨ su-[] ⊢I,t,recTrst (⊢vn∶N L.[ T ] ⊢TNΓ refl) ⟩
              su (v 1 [ (I , t) , rec T s r t ])
            ≈⟨ su-cong (≈-conv ([,]-v-su (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) ⊢t) ⊢T ⊢recTsrt here) (N-[][] 0 (s-wk ⊢NΓ) (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) ⊢t))) ⟩
              su (v 0 [ I , t ])
            ≈⟨ su-cong (≈-conv-N-[] ([,]-v-ze (s-I ⊢Γ) (N-wf 0 ⊢Γ) (conv-N-[]-sym ⊢t (s-I ⊢Γ))) (s-I ⊢Γ)) ⟩
              su t
            ∎
            where
              open ER

          open SR

          lemma-l : Γ ⊢s wk ∘ wk ∘ ((I , t) , rec T s r t) ≈ I ∶ Γ
          lemma-l =
            begin
              wk ∘ wk ∘ ((I , t) , rec T s r t)
            ≈⟨ ∘-assoc (s-wk ⊢NΓ) (s-wk ⊢TNΓ) ⊢I,t,recTrst ⟩
              wk ∘ (wk ∘ ((I , t) , rec T s r t))
            ≈⟨ ∘-cong (wk∘[σ,t]≈σ ⊢TNΓ (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) ⊢t) ⊢recTsrt) (s-≈-refl (s-wk ⊢NΓ)) ⟩
              wk ∘ (I , t)
            ≈⟨ wk∘[σ,t]≈σ ⊢NΓ (s-I ⊢Γ) (conv-N-[]-sym ⊢t (s-I ⊢Γ)) ⟩
              I
            ∎

  presup-≈ (Λ-β ⊢S ⊢t ⊢s)
    with presup-tm ⊢t
  ... | ⊢∷ ⊢Γ _ , _ , ⊢T = ⊢Γ , Λ-E (Λ-I ⊢S ⊢t) ⊢s , t[σ] ⊢t (⊢I,t ⊢Γ ⊢S ⊢s) , _ , t[σ]-Se ⊢T (⊢I,t ⊢Γ ⊢S ⊢s)
  presup-≈ (Λ-η ⊢s)
    with presup-tm ⊢s
  ... | ⊢Γ , _ , ⊢ΠST
      with inv-Π-wf′ ⊢ΠST | inv-Π-wf ⊢ΠST
  ...   | _ , ⊢S          | _ , ⊢T        = ⊢Γ , ⊢s , conv (Λ-I ⊢S (Λ-E (conv (t[σ] ⊢s (s-wk ⊢SΓ)) (Π-[] (s-wk ⊢SΓ) ⊢S′ ⊢T′)) ⊢v0)) (Π-cong ⊢S′ (≈-refl ⊢S′) (≈-trans ([∘]-Se ⊢T′ (⊢q ⊢SΓ (s-wk ⊢SΓ) ⊢S) ⊢I,v0) (≈-trans ([]-cong-Se″ ⊢T′ (s-∘ ⊢I,v0 (⊢q ⊢SΓ (s-wk ⊢SΓ) ⊢S)) (q[wk]∘[I,v0]≈I ⊢SΓ)) ([I] ⊢T′)))) , _ , ⊢ΠST
    where
      ⊢SΓ = ⊢∷ ⊢Γ ⊢S
      ⊢S[wk] = t[σ]-Se ⊢S (s-wk ⊢SΓ)
      ⊢v0 = vlookup ⊢SΓ here
      ⊢S′ = lift-⊢-Se-max ⊢S
      ⊢T′ = lift-⊢-Se-max′ ⊢T
      ⊢I,v0 = ⊢I,t ⊢SΓ ⊢S[wk] ⊢v0
  presup-≈ (□-β Ψ ⊢t ⊢ΨΓ eq)
    with presup-tm ⊢t
  ... | ⊢κ ⊢Γ , _ , ⊢T  = ⊢ΨΓ , □-E Ψ (□-I ⊢t) ⊢ΨΓ eq , t[σ] ⊢t (s-； Ψ (s-I ⊢Γ) ⊢ΨΓ eq) , _ , t[σ]-Se ⊢T (s-； Ψ (s-I ⊢Γ) ⊢ΨΓ eq)
  presup-≈ (□-η ⊢s)
    with presup-tm ⊢s 
  ... | ⊢Γ , _ , ⊢□T
      with inv-□-wf ⊢□T
  ...   | _ , ⊢T       = ⊢Γ , ⊢s , conv (□-I (□-E L.[ [] ] ⊢s (⊢κ ⊢Γ) refl)) (≈-trans (≈-sym (□-[] (s-I ⊢Γ) (lift-⊢-Se-max ⊢T))) ([I] (lift-⊢-Se-max′ ⊢□T))) , _ , ⊢□T
  presup-≈ ([I] ⊢t)
    with presup-tm ⊢t
  ... | ⊢Γ , _ , ⊢T    = ⊢Γ , conv (t[σ] ⊢t (s-I ⊢Γ)) ([I] ⊢T) , ⊢t , _ , ⊢T
  presup-≈ ([wk] ⊢SΓ@(⊢∷ ⊢Γ _) T∈Γ) = ⊢SΓ , t[σ] (vlookup ⊢Γ T∈Γ) (s-wk ⊢SΓ) , vlookup ⊢SΓ (there T∈Γ) , _ , (t[σ]-Se (proj₂ (∈!⇒ty-wf ⊢Γ T∈Γ)) (s-wk ⊢SΓ))
  presup-≈ ([∘] ⊢τ ⊢σ ⊢t)
    with presup-s ⊢τ | presup-tm ⊢t
  ... | ⊢Γ , _ | _ , _ , ⊢T = ⊢Γ , t[σ] ⊢t (s-∘ ⊢τ ⊢σ) , conv (t[σ] (t[σ] ⊢t ⊢σ) ⊢τ) ([∘]-Se ⊢T ⊢σ ⊢τ) , _ , t[σ]-Se ⊢T (s-∘ ⊢τ ⊢σ)
  presup-≈ ([,]-v-ze ⊢σ ⊢S ⊢t)
    with presup-s ⊢σ
  ... | ⊢Γ , ⊢Δ             = ⊢Γ , conv (t[σ] (vlookup ⊢SΔ here) ⊢σ,t) (≈-trans ([∘]-Se ⊢S (s-wk ⊢SΔ) ⊢σ,t) ([]-cong-Se″ ⊢S (s-∘ ⊢σ,t (s-wk ⊢SΔ)) (wk∘[σ,t]≈σ ⊢SΔ ⊢σ ⊢t))) , ⊢t , _ , (t[σ]-Se ⊢S ⊢σ)
    where
      ⊢SΔ = ⊢∷ ⊢Δ ⊢S
      ⊢σ,t = s-, ⊢σ ⊢S ⊢t
  presup-≈ ([,]-v-su ⊢σ ⊢S ⊢s T∈Δ)
    with presup-s ⊢σ
  ... | ⊢Γ , ⊢Δ
      with ∈!⇒ty-wf ⊢Δ T∈Δ
  ...   | _ , ⊢T        = ⊢Γ , conv (t[σ] (vlookup ⊢SΔ (there T∈Δ)) ⊢σ,s) (≈-trans ([∘]-Se ⊢T (s-wk ⊢SΔ) ⊢σ,s) ([]-cong-Se″ ⊢T (s-∘ ⊢σ,s (s-wk ⊢SΔ)) (wk∘[σ,t]≈σ ⊢SΔ ⊢σ ⊢s))) , t[σ] (vlookup ⊢Δ T∈Δ) ⊢σ , _ , t[σ]-Se ⊢T ⊢σ
    where
      ⊢SΔ = ⊢∷ ⊢Δ ⊢S
      ⊢σ,s = s-, ⊢σ ⊢S ⊢s
  presup-≈ (≈-cumu s≈t)
    with presup-≈ s≈t
  ... | ⊢Γ , ⊢s , ⊢t , _ = ⊢Γ , cumu ⊢s , cumu ⊢t , _ , Se-wf _ ⊢Γ
  presup-≈ (≈-conv s≈t S≈T)
    with presup-≈ s≈t      | presup-≈ S≈T
  ... | ⊢Γ , ⊢s , ⊢t , _ | _ , _ , ⊢T , _ = ⊢Γ , conv ⊢s S≈T , conv ⊢t S≈T , _ , ⊢T
  presup-≈ (≈-sym t≈s)
    with presup-≈ t≈s
  ... | ⊢Γ , ⊢t , ⊢s , ⊢T = ⊢Γ , ⊢s , ⊢t , ⊢T
  presup-≈ (≈-trans s≈t′ t′≈t)
    with presup-≈ s≈t′ | presup-≈ t′≈t
  ... | ⊢Γ , ⊢s , _  | _ , _ , ⊢t , ⊢T = ⊢Γ , ⊢s , ⊢t , ⊢T


  presup-s-≈ : Γ ⊢s σ ≈ τ ∶ Δ →
               -----------------------------------
               ⊢ Γ × Γ ⊢s σ ∶ Δ × Γ ⊢s τ ∶ Δ × ⊢ Δ
  presup-s-≈ (I-≈ ⊢Γ)                   = ⊢Γ , s-I ⊢Γ , s-I ⊢Γ , ⊢Γ
  presup-s-≈ (wk-≈ ⊢TΓ@(⊢∷ ⊢Γ _))       = ⊢TΓ , s-wk ⊢TΓ , s-wk ⊢TΓ , ⊢Γ
  presup-s-≈ (∘-cong σ≈σ′ τ≈τ′)
    with presup-s-≈ σ≈σ′ | presup-s-≈ τ≈τ′
  ...  | ⊢Γ , ⊢σ , ⊢σ′ , _
       | _  , ⊢τ , ⊢τ′ , ⊢Δ             = ⊢Γ , s-∘ ⊢σ ⊢τ , s-∘ ⊢σ′ ⊢τ′ , ⊢Δ
  presup-s-≈ (,-cong σ≈τ ⊢T t≈t′)
    with presup-s-≈ σ≈τ | presup-≈ t≈t′
  ...  | ⊢Γ , ⊢σ , ⊢τ , ⊢Δ
       | _  , ⊢t , ⊢t′ , _              = ⊢Γ , s-, ⊢σ ⊢T ⊢t , s-, ⊢τ ⊢T (conv ⊢t′ ([]-cong-Se″ ⊢T ⊢σ σ≈τ)) , ⊢∷ ⊢Δ ⊢T
  presup-s-≈ (；-cong Ψs σ≈τ ⊢ΨsΓ eq)
    with presup-s-≈ σ≈τ
  ...  | ⊢Γ , ⊢σ , ⊢τ , ⊢Δ              = ⊢ΨsΓ , s-； Ψs ⊢σ ⊢ΨsΓ eq , s-； Ψs ⊢τ ⊢ΨsΓ eq , ⊢κ ⊢Δ
  presup-s-≈ (I-∘ ⊢σ)
    with presup-s ⊢σ
  ...  | ⊢Γ , ⊢Δ                        = ⊢Γ , s-∘ ⊢σ (s-I ⊢Δ) , ⊢σ , ⊢Δ
  presup-s-≈ (∘-I ⊢σ)
    with presup-s ⊢σ
  ...  | ⊢Γ , ⊢Δ                        = ⊢Γ , s-∘ (s-I ⊢Γ) ⊢σ , ⊢σ , ⊢Δ
  presup-s-≈ (∘-assoc ⊢σ ⊢σ′ ⊢σ″)
    with presup-s ⊢σ | presup-s ⊢σ″
  ...  | _ , ⊢Δ      | ⊢Γ , _           = ⊢Γ , s-∘ ⊢σ″ (s-∘ ⊢σ′ ⊢σ) , s-∘ (s-∘ ⊢σ″ ⊢σ′) ⊢σ , ⊢Δ
  presup-s-≈ (,-∘ ⊢σ ⊢T ⊢t ⊢τ)
    with presup-s ⊢σ | presup-s ⊢τ
  ...  | _ , ⊢Δ      | ⊢Γ , _           = ⊢Γ , s-∘ ⊢τ (s-, ⊢σ ⊢T ⊢t) , s-, (s-∘ ⊢τ ⊢σ) ⊢T (conv (t[σ] ⊢t ⊢τ) ([∘]-Se ⊢T ⊢σ ⊢τ)) , ⊢∷ ⊢Δ ⊢T
  presup-s-≈ (；-∘ Ψs ⊢σ ⊢τ ⊢ΨsΓ refl)
    with presup-s ⊢σ | presup-s ⊢τ
  ...  | _ , ⊢Δ      | ⊢Γ , _
       with ∥-⊢s′ Ψs ⊢τ
  ...     | Ψs′ , Γ′ , refl , eql , ⊢τ∥ = ⊢Γ , s-∘ ⊢τ (s-； Ψs ⊢σ ⊢ΨsΓ refl) , s-； Ψs′ (s-∘ ⊢τ∥ ⊢σ) ⊢Γ eql , ⊢κ ⊢Δ
  presup-s-≈ (p-, ⊢τ ⊢T ⊢t)
    with presup-s ⊢τ
  ...  | ⊢Γ , ⊢Δ                        = ⊢Γ , ⊢p (⊢∷ ⊢Δ ⊢T) (s-, ⊢τ ⊢T ⊢t) , ⊢τ , ⊢Δ
  presup-s-≈ (,-ext ⊢σ)
    with presup-s ⊢σ
  ... | ⊢Γ , ⊢TΔ@(⊢∷ ⊢Δ ⊢T)             = ⊢Γ , ⊢σ , s-, (⊢p ⊢TΔ ⊢σ) ⊢T (conv (t[σ] (vlookup ⊢TΔ here) ⊢σ) (≈-trans ([∘]-Se ⊢T (s-wk ⊢TΔ) ⊢σ) (≈-refl (t[σ]-Se ⊢T (⊢p ⊢TΔ ⊢σ))))) , ⊢TΔ
  presup-s-≈ (；-ext ⊢σ)
    with presup-s ⊢σ
  ...  | ⊢Γ , ⊢κ ⊢Δ
       with ∥-⊢s′ ([] ∷ []) ⊢σ
  ...     | Ψs′ , Γ′ , refl , eql , ⊢σ∥ = ⊢Γ , ⊢σ , s-； Ψs′ ⊢σ∥ ⊢Γ eql , ⊢κ ⊢Δ
  presup-s-≈ (s-≈-sym σ≈τ)
    with presup-s-≈ σ≈τ
  ...  | ⊢Γ , ⊢σ , ⊢τ , ⊢Δ              = ⊢Γ , ⊢τ , ⊢σ , ⊢Δ
  presup-s-≈ (s-≈-trans σ≈σ′ σ′≈σ″)
    with presup-s-≈ σ≈σ′ | presup-s-≈ σ′≈σ″
  ...  | ⊢Γ , ⊢σ , ⊢σ′ , _
       | _  , _  , ⊢σ″ , ⊢Δ             = ⊢Γ , ⊢σ , ⊢σ″ , ⊢Δ
  presup-s-≈ (s-≈-conv σ≈τ Δ′≈Δ)
    with presup-s-≈ σ≈τ
  ...  | ⊢Γ , ⊢σ , ⊢τ , ⊢Δ′             = ⊢Γ , s-conv ⊢σ Δ′≈Δ , s-conv ⊢τ Δ′≈Δ , proj₂ (presup-⊢≈ Δ′≈Δ)
