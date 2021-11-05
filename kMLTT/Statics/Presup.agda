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
  ...  | ⊢Γ , _                   = ⊢Γ , _ , conv-Se ⊢T (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) ⊢t)
  presup-tm (Λ-I ⊢S ⊢t)
    with presup-tm ⊢t
  ... | ⊢∷ ⊢Γ ⊢S , _ , ⊢T         = ⊢Γ , _ , Π-wf (lift-⊢-Se-max ⊢S) (lift-⊢-Se-max′ ⊢T)
  presup-tm (Λ-E ⊢t ⊢s)
    with presup-tm ⊢s | presup-tm ⊢t
  ...  | _  , _ , ⊢S
       | ⊢Γ , _ , ⊢Π              = ⊢Γ , _ , conv-Se (proj₂ (inv-Π-wf ⊢Π)) (⊢I,t ⊢Γ ⊢S ⊢s)
  presup-tm (□-I ⊢t)
    with presup-tm ⊢t
  ...  | ⊢κ ⊢Γ , _ , ⊢T           = ⊢Γ , _ , □-wf ⊢T
  presup-tm (□-E Ψs ⊢t ⊢ΨsΓ eq)
    with presup-tm ⊢t
  ...  | ⊢Γ , _ , ⊢□T             = ⊢ΨsΓ , _ , conv-Se (proj₂ (inv-□-wf ⊢□T)) (s-； Ψs (s-I ⊢Γ) ⊢ΨsΓ eq)
  presup-tm (t[σ] ⊢t ⊢σ)
    with presup-tm ⊢t | presup-s ⊢σ
  ...  | _ , _ , ⊢T | ⊢Γ , _      = ⊢Γ , _ , conv-Se ⊢T ⊢σ
  presup-tm (cumu ⊢T)
    with presup-tm ⊢T
  ...  | ⊢Γ , _                   = ⊢Γ , suc (suc _) , Se-wf (suc _) ⊢Γ
  presup-tm (conv ⊢t S≈T)
    with presup-≈ S≈T
  ...  | ⊢Γ , _ , ⊢T , _          = ⊢Γ , _ , ⊢T


  presup-s : Γ ⊢s σ ∶ Δ →
             ------------
             ⊢ Γ × ⊢ Δ
  presup-s (s-I ⊢Γ)      = ⊢Γ , ⊢Γ
  presup-s (s-p ⊢σ)
    with presup-s ⊢σ
  ... | ⊢Γ , ⊢∷ ⊢Δ _     = ⊢Γ , ⊢Δ
  presup-s (s-∘ ⊢σ ⊢δ)
    with presup-s ⊢σ | presup-s ⊢δ
  ...  | ⊢Γ , _ | _ , ⊢Δ = ⊢Γ , ⊢Δ
  presup-s (s-, ⊢σ ⊢T ⊢t)
    with presup-s ⊢σ
  ... | ⊢Γ , ⊢Δ          = ⊢Γ , ⊢∷ ⊢Δ ⊢T
  presup-s (s-； Ψs ⊢σ ⊢ΨsΓ eq)
    with presup-s ⊢σ
  ... | _ , ⊢Δ           = ⊢ΨsΓ , ⊢κ ⊢Δ
  presup-s (s-conv ⊢σ Δ′≈Δ)
    with presup-s ⊢σ
  ... | ⊢Γ , _           = ⊢Γ , proj₂ (presup-⊢≈ Δ′≈Δ)


  presup-≈ : Γ ⊢ s ≈ t ∶ T →
             -----------------------------------
             ⊢ Γ × Γ ⊢ s ∶ T × Γ ⊢ t ∶ T × Γ ⊢ T
  presup-≈ (N-[] i ⊢σ)
    with presup-s ⊢σ
  ... | ⊢Γ , ⊢Δ      = ⊢Γ , conv-Se (N-wf _ ⊢Δ) ⊢σ , N-wf _ ⊢Γ , _ , Se-wf _ ⊢Γ
  presup-≈ (Se-[] i ⊢σ)
    with presup-s ⊢σ
  ... | ⊢Γ , ⊢Δ      = ⊢Γ , conv-Se (Se-wf _ ⊢Δ) ⊢σ , Se-wf _ ⊢Γ , _ , Se-wf _ ⊢Γ
  presup-≈ (Π-[] ⊢σ ⊢S ⊢T)
    with presup-s ⊢σ
  ... | ⊢Γ , ⊢Δ with ⊢∷ ⊢Γ (conv-Se ⊢S ⊢σ)
  ...               | ⊢S[σ]Γ      = ⊢Γ , conv-Se (Π-wf ⊢S ⊢T) ⊢σ , Π-wf (conv-Se ⊢S ⊢σ) (conv-Se ⊢T (s-, (s-∘ (s-p (s-I ⊢S[σ]Γ)) ⊢σ) ⊢S (conv (vlookup ⊢S[σ]Γ here) (([∘]-Se ⊢S ⊢σ (s-p (s-I ⊢S[σ]Γ))))))) , _ , Se-wf _ ⊢Γ
  presup-≈ (□-[] ⊢σ ⊢T)
    with presup-s ⊢σ
  ... | ⊢Γ , ⊢Δ      = ⊢Γ , conv-Se (□-wf ⊢T) ⊢σ , □-wf (conv-Se ⊢T (s-； L.[ [] ] ⊢σ (⊢κ ⊢Γ) refl)) , _ , Se-wf _ ⊢Γ
  presup-≈ (Π-cong ⊢S S≈S′ T≈T′)
    with presup-≈ S≈S′   | presup-≈ T≈T′
  ... | ⊢Γ , ⊢S , ⊢S′ , _ | _ , ⊢T , ⊢T′ , _  = ⊢Γ , Π-wf ⊢S ⊢T , Π-wf ⊢S′ (ctxeq-tm (∷-cong (≈-Ctx-refl ⊢Γ) ⊢S ⊢S′ S≈S′ S≈S′) ⊢T′) , _ , Se-wf _ ⊢Γ
  presup-≈ (□-cong T≈T′)
    with presup-≈ T≈T′
  ... | ⊢κ ⊢Γ , ⊢T , ⊢T′ , _ = ⊢Γ , □-wf ⊢T , □-wf ⊢T′ , _ , Se-wf _ ⊢Γ
  presup-≈ (v-≈ ⊢Γ T∈Γ) = ⊢Γ , vlookup ⊢Γ T∈Γ , vlookup ⊢Γ T∈Γ , _ , proj₂ (∈!⇒ty-wf ⊢Γ T∈Γ)
  presup-≈ (ze-≈ ⊢Γ) = ⊢Γ , ze-I ⊢Γ , ze-I ⊢Γ , _ , N-wf 0 ⊢Γ
  presup-≈ (su-cong t≈t′)
    with presup-≈ t≈t′
  ... | ⊢Γ , ⊢t , ⊢t′ , _ = ⊢Γ , su-I ⊢t , su-I ⊢t′ , _ , N-wf 0 ⊢Γ
  presup-≈ (rec-cong ⊢T T≈T′ s≈s′ r≈r′ t≈t′) -- FIXME! Proof is quite complex.
    with presup-≈ T≈T′     | presup-≈ s≈s′     | presup-≈ r≈r′       | presup-≈ t≈t′
  ... | ⊢NΓ , ⊢T , ⊢T′ , _ | ⊢Γ , ⊢s , ⊢s′ , _ | ⊢TNΓ , ⊢r , ⊢r′ , _ | _ , ⊢t , ⊢t′ , _
      = ⊢Γ
      , N-E ⊢T ⊢s ⊢r ⊢t
      , conv (N-E ⊢T′ (conv ⊢s′ (≈-conv-Se′ T≈T′ (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) (ze-I ⊢Γ)))) (ctxeq-tm (∷-cong′ ⊢NΓ ⊢T ⊢T′ T≈T′) (conv ⊢r′ (≈-conv-Se′ T≈T′ (s-, (s-∘ (⊢wk ⊢TNΓ) (⊢wk ⊢NΓ)) (N-wf 0 ⊢Γ) (conv (su-I (conv (vlookup ⊢TNΓ (there here)) (N[wk][wk]≈N 0 ⊢TNΓ))) (≈-sym (N-[] 0 (s-∘ (⊢wk ⊢TNΓ) (⊢wk ⊢NΓ))))))))) ⊢t′) (≈-sym (≈-conv-Se T≈T′ (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) ⊢t) (,-cong (I-≈ ⊢Γ) (N-wf 0 ⊢Γ) (≈-conv t≈t′ (≈-sym (N-[] 0 (s-I ⊢Γ)))))))
      , _ , (conv-Se ⊢T (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) ⊢t))
  presup-≈ (Λ-cong ⊢S t≈t′)
    with presup-≈ t≈t′
  ... | ⊢∷ ⊢Γ _ , ⊢t , ⊢t′ , _ , ⊢T = ⊢Γ , Λ-I ⊢S ⊢t , Λ-I ⊢S ⊢t′ , _ , Π-wf (lift-⊢-Se-max ⊢S) (lift-⊢-Se-max′ ⊢T)
  presup-≈ ($-cong r≈r′ s≈s′)
    with presup-≈ r≈r′           | presup-≈ s≈s′
  ... | ⊢Γ , ⊢r , ⊢r′ , _ , ⊢ΠST | _ , ⊢s , ⊢s′ , _
      with inv-Π-wf′ ⊢ΠST | inv-Π-wf ⊢ΠST
  ...   | _ , ⊢S          | _ , ⊢T           = ⊢Γ
                                             , Λ-E ⊢r ⊢s
                                             , conv (Λ-E ⊢r′ ⊢s′) (≈-conv-Se (≈-refl ⊢T) (⊢I,t ⊢Γ ⊢S ⊢s′) (,-cong (I-≈ ⊢Γ) ⊢S (≈-conv (≈-sym s≈s′) (≈-sym ([I] ⊢S)))))
                                             , _ , conv-Se ⊢T (⊢I,t ⊢Γ ⊢S ⊢s)
  presup-≈ (box-cong t≈t′)
    with presup-≈ t≈t′
  ... | ⊢κ ⊢Γ , ⊢t , ⊢t′ , _ , ⊢T     = ⊢Γ , □-I ⊢t , □-I ⊢t′ , _ , □-wf ⊢T
  presup-≈ (unbox-cong Ψ t≈t′ ⊢ΨΓ eq)
    with presup-≈ t≈t′
  ... | ⊢Γ , ⊢t , ⊢t′ , _ , ⊢□T
      with inv-□-wf ⊢□T
  ...   | _ , ⊢T               = ⊢ΨΓ , □-E Ψ ⊢t ⊢ΨΓ eq , □-E Ψ ⊢t′ ⊢ΨΓ eq , _ , conv-Se ⊢T (s-； Ψ (s-I ⊢Γ) ⊢ΨΓ eq)
  presup-≈ ([]-cong t≈t′ σ≈σ′)
    with presup-≈ t≈t′        | presup-s-≈ σ≈σ′
  ... | _ , ⊢t , ⊢t′ , _ , ⊢T | ⊢Γ , ⊢σ , ⊢σ′ , _  = ⊢Γ , t[σ] ⊢t ⊢σ , conv (t[σ] ⊢t′ ⊢σ′) (≈-conv-Se (≈-refl ⊢T) ⊢σ′ (s-≈-sym σ≈σ′)) , _ , conv-Se ⊢T ⊢σ
  presup-≈ (ze-[] ⊢σ)
    with presup-s ⊢σ
  ... | ⊢Γ , ⊢Δ          = ⊢Γ , conv-N (ze-I ⊢Δ) ⊢σ , ze-I ⊢Γ , _ , N-wf 0 ⊢Γ
  presup-≈ (su-[] ⊢σ ⊢t)
    with presup-s ⊢σ
  ... | ⊢Γ , _           = ⊢Γ , conv-N (su-I ⊢t) ⊢σ , su-I (conv-N ⊢t ⊢σ) , _ , N-wf 0 ⊢Γ
  presup-≈ (rec-[] {Γ = Γ} {σ = σ} {Δ = Δ} {T = T} {i = i} ⊢σ ⊢T ⊢s ⊢r ⊢t)
    -- FIXME! This proof is crazy (and tons of redundancy).
    with presup-s ⊢σ
  ... | ⊢Γ , ⊢Δ          = ⊢Γ
                         , conv (t[σ] (N-E ⊢T ⊢s ⊢r ⊢t) ⊢σ) (≈-trans ([∘]-Se ⊢T (⊢I,t ⊢Δ (N-wf 0 ⊢Δ) ⊢t) ⊢σ) (≈-conv-Se (≈-refl ⊢T) (s-∘ ⊢σ (⊢I,t ⊢Δ (N-wf 0 ⊢Δ) ⊢t)) (s-≈-trans (,-∘ (s-I ⊢Δ) (N-wf 0 ⊢Δ) (conv ⊢t (≈-sym ([I] (N-wf 0 ⊢Δ)))) ⊢σ) (,-cong (I-∘ ⊢σ) (N-wf 0 ⊢Δ) (≈-refl (conv (t[σ] ⊢t ⊢σ) (≈-trans (≈-conv-Se′ (≈-sym ([I] (N-wf 0 ⊢Δ))) ⊢σ) ([∘]-Se (N-wf 0 ⊢Δ) (s-I ⊢Δ) ⊢σ))))))))
                         , conv
                             (N-E ⊢T[qσ]
                               (conv (t[σ] ⊢s ⊢σ) (≈-sym (≈-trans ([∘]-Se ⊢T ⊢qσ (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) (ze-I ⊢Γ))) (≈-trans (≈-conv-Se (≈-refl ⊢T) (s-∘ (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) (ze-I ⊢Γ)) ⊢qσ) (s-≈-trans (qσ∘[I,t]≈σ,t ⊢Γ (N-wf 0 ⊢Δ) ⊢σ (conv (ze-I ⊢Γ) (≈-sym (N-[] 0 ⊢σ)))) (s-≈-sym (s-≈-trans ([I,t]∘σ≈σ,t[σ] ⊢Γ ⊢NΔ ⊢σ (ze-I ⊢Δ)) (,-cong (s-≈-refl ⊢σ) (N-wf 0 ⊢Δ) (≈-conv (ze-[] ⊢σ) (≈-sym (N-[] 0 ⊢σ)))))))) (≈-sym ([∘]-Se ⊢T (⊢I,t ⊢Δ (N-wf 0 ⊢Δ) (ze-I ⊢Δ)) ⊢σ))))))
                               (conv (t[σ] ⊢r ⊢q[qσ]) (by-[∘] (≈-conv-Se (≈-refl ⊢T) (s-∘ ⊢q[qσ] ⊢[wk∘wk],su[v1]) lemmaT)))
                               (conv-N ⊢t ⊢σ))
                             (≈-trans
                               ([∘]-Se ⊢T ⊢qσ (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) (conv-N ⊢t ⊢σ)))
                               (≈-conv-Se (≈-refl ⊢T) (s-∘ (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) (conv-N ⊢t ⊢σ)) ⊢qσ) (qσ∘[I,t]≈σ,t ⊢Γ (N-wf 0 ⊢Δ) ⊢σ (t[σ] ⊢t ⊢σ))))
                          , _ , conv-Se ⊢T (s-, ⊢σ (N-wf 0 ⊢Δ) (t[σ] ⊢t ⊢σ))
    where
      ⊢qσ = ⊢q-N ⊢Γ ⊢Δ ⊢σ
      ⊢T[qσ] = conv-Se ⊢T ⊢qσ
      ⊢NΓ = ⊢∷ ⊢Γ (N-wf 0 ⊢Γ)
      ⊢q[qσ] = ⊢q ⊢NΓ ⊢qσ ⊢T
      ⊢T[qσ]NΓ = ⊢∷ ⊢NΓ ⊢T[qσ]
      ⊢NΔ = ⊢∷ ⊢Δ (N-wf 0 ⊢Δ)
      ⊢TNΔ = ⊢∷ ⊢NΔ ⊢T

      ⊢wk∘wk = (s-∘ (⊢wk ⊢TNΔ) (⊢wk ⊢NΔ))
      ⊢wk∘wk′ = (s-∘ (⊢wk ⊢T[qσ]NΓ) (⊢wk ⊢NΓ))
      ⊢v1 = conv (vlookup ⊢TNΔ (there here)) (N[wk][wk]≈N 0 ⊢TNΔ)
      ⊢v1′ = conv (vlookup ⊢T[qσ]NΓ (there here)) (N[wk][wk]≈N 0 ⊢T[qσ]NΓ)
      ⊢su[v1] = conv (su-I ⊢v1) (≈-sym (N-[] 0 ⊢wk∘wk))
      ⊢su[v1]′ = conv (su-I ⊢v1′) (≈-sym (N-[] 0 ⊢wk∘wk′))
      ⊢[wk∘wk],su[v1] = s-, ⊢wk∘wk (N-wf 0 ⊢Δ) ⊢su[v1]
      ⊢[wk∘wk],su[v1]′ = s-, ⊢wk∘wk′ (N-wf 0 ⊢Γ) ⊢su[v1]′
      ⊢qσ∘wk = s-∘ (⊢wk ⊢T[qσ]NΓ) ⊢qσ
      ⊢σ∘wk = s-∘ (⊢wk ⊢NΓ) ⊢σ
      ⊢σ∘wk∘wk = s-∘ (⊢wk ⊢T[qσ]NΓ) ⊢σ∘wk

      by-[∘] : (T [ q σ ]) ∺ N ∺ Γ ⊢ T [ ((wk ∘ wk) , su (v 1)) ∘ q (q σ) ] ≈ T [ q σ ∘ ((wk ∘ wk) , su (v 1)) ] ∶ Se i →
               (T [ q σ ]) ∺ N ∺ Γ ⊢ T [ ((wk ∘ wk) , su (v 1)) ] [ q (q σ) ] ≈ T [ q σ ] [ ((wk ∘ wk) , su (v 1)) ] ∶ Se i
      by-[∘] x = ≈-trans ([∘]-Se ⊢T ⊢[wk∘wk],su[v1] ⊢q[qσ]) (≈-trans x (≈-sym ([∘]-Se ⊢T ⊢qσ ⊢[wk∘wk],su[v1]′)))

      lemmaT : (T [ q σ ]) ∺ N ∺ Γ ⊢s ((wk ∘ wk) , su (v 1)) ∘ q (q σ) ≈ q σ ∘ ((wk ∘ wk) , su (v 1)) ∶ N ∺ Δ
      lemmaT =
        begin
          ((wk ∘ wk) , su (v 1)) ∘ q (q σ)
        ≈⟨ ,-∘ ⊢wk∘wk (N-wf 0 ⊢Δ) ⊢su[v1] ⊢q[qσ] ⟩
          (wk ∘ wk ∘ q (q σ)) , su (v 1) [ q (q σ) ]
        ≈⟨ ,-cong lemmaT-l (N-wf 0 ⊢Δ) (≈-conv lemmaT-r (≈-sym (N-[] 0 (s-∘ ⊢q[qσ] ⊢wk∘wk)))) ⟩
          (σ ∘ wk ∘ ((wk ∘ wk) , su (v 1))) , v 0 [ (wk ∘ wk) , su (v 1) ]
        ≈˘⟨ ,-∘ ⊢σ∘wk (N-wf 0 ⊢Δ) (conv (vlookup ⊢NΓ here) (N[σ]≈N[τ] 0 (⊢wk ⊢NΓ) ⊢σ∘wk)) ⊢[wk∘wk],su[v1]′ ⟩
          q σ ∘ ((wk ∘ wk) , su (v 1))
        ∎
        where
          lemmaT-r : (T [ q σ ]) ∺ N ∺ Γ ⊢ su (v 1) [ q (q σ) ] ≈ v 0 [ (wk ∘ wk) , su (v 1) ] ∶ N
          lemmaT-r =
            begin
              su (v 1) [ q (q σ) ]
            ≈⟨ su-[] ⊢q[qσ] ⊢v1 ⟩
              su (v 1 [ q (q σ) ])
            ≈⟨ su-cong (≈-conv ([,]-v-su ⊢qσ∘wk ⊢T (conv (vlookup ⊢T[qσ]NΓ here) ([∘]-Se ⊢T ⊢qσ (⊢wk ⊢T[qσ]NΓ))) here) (N-[][] 0 (⊢wk ⊢NΔ) ⊢qσ∘wk)) ⟩
              su (v 0 [ q σ ∘ wk ])
            ≈⟨ su-cong (≈-conv ([]-cong (≈-refl (vlookup ⊢NΔ here)) (,-∘ ⊢σ∘wk (N-wf 0 ⊢Δ) (conv (vlookup ⊢NΓ here) (N[σ]≈N[τ] 0 (⊢wk ⊢NΓ) ⊢σ∘wk)) (⊢wk ⊢T[qσ]NΓ))) (N-[][] 0 (⊢wk ⊢NΔ) ⊢qσ∘wk)) ⟩
              su (v 0 [ (σ ∘ wk ∘ wk) , v 0 [ wk ] ])
            ≈⟨ su-cong (≈-conv ([,]-v-ze ⊢σ∘wk∘wk (N-wf 0 ⊢Δ) (conv (t[σ] (conv (vlookup ⊢NΓ here) (N[σ]≈N[τ] 0 (⊢wk ⊢NΓ) ⊢σ∘wk)) (⊢wk ⊢T[qσ]NΓ)) ([∘]-Se (N-wf 0 ⊢Δ) ⊢σ∘wk (⊢wk ⊢T[qσ]NΓ)))) (N-[] 0 ⊢σ∘wk∘wk)) ⟩
              su (v 0 [ wk ])
            ≈⟨ su-cong (≈-conv ([p] (s-I ⊢T[qσ]NΓ) here) (N-[][] 0 (⊢wk ⊢NΓ) (⊢wk ⊢T[qσ]NΓ))) ⟩
              su (v 1 [ I ])
            ≈⟨ su-cong ([I] ⊢v1′) ⟩
              su (v 1)
            ≈˘⟨ ≈-conv ([,]-v-ze ⊢wk∘wk′ (N-wf 0 ⊢Γ) ⊢su[v1]′) (N-[] 0 ⊢wk∘wk′) ⟩
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
            ≈˘⟨ ∘-assoc ⊢σ (⊢wk ⊢NΓ) ⊢[wk∘wk],su[v1]′ ⟩
              (σ ∘ wk ∘ ((wk ∘ wk) , su (v 1)))
            ∎
  presup-≈ (Λ-[] ⊢σ ⊢t)
    with presup-s ⊢σ | presup-tm ⊢t
  ... | ⊢Γ , _       | ⊢∷ _ ⊢S , _ , ⊢T = ⊢Γ , t[σ] (Λ-I ⊢S ⊢t) ⊢σ , conv (Λ-I (conv-Se ⊢S ⊢σ) (t[σ] ⊢t (⊢q ⊢Γ ⊢σ ⊢S))) (≈-sym (Π-[] ⊢σ (lift-⊢-Se-max ⊢S) (lift-⊢-Se-max′ ⊢T))) , _ , conv-Se (Π-wf (lift-⊢-Se-max ⊢S) (lift-⊢-Se-max′ ⊢T)) ⊢σ
  presup-≈ ($-[] ⊢σ ⊢r ⊢s)
    with presup-s ⊢σ | presup-tm ⊢r
  ... | ⊢Γ , ⊢Δ      | _ , _ , ⊢ΠST
      with inv-Π-wf′ ⊢ΠST | inv-Π-wf ⊢ΠST
  ...   | _ , ⊢S          | _ , ⊢T        = ⊢Γ , conv (t[σ] (Λ-E ⊢r ⊢s) ⊢σ) (≈-trans ([∘]-Se ⊢T (⊢I,t ⊢Δ ⊢S ⊢s) ⊢σ) (≈-conv-Se (≈-refl ⊢T) (s-∘ ⊢σ (⊢I,t ⊢Δ ⊢S ⊢s)) ([I,t]∘σ≈σ,t[σ] ⊢Γ (⊢∷ ⊢Δ ⊢S) ⊢σ ⊢s))) , conv (Λ-E (conv (t[σ] ⊢r ⊢σ) (Π-[] ⊢σ (lift-⊢-Se-max ⊢S) (lift-⊢-Se-max′ ⊢T))) (t[σ] ⊢s ⊢σ)) (≈-trans ([∘]-Se ⊢T (⊢q ⊢Γ ⊢σ ⊢S) (⊢I,t ⊢Γ (conv-Se ⊢S ⊢σ) (t[σ] ⊢s ⊢σ))) (≈-conv-Se (≈-refl ⊢T) (s-∘ (⊢I,t ⊢Γ (conv-Se ⊢S ⊢σ) (t[σ] ⊢s ⊢σ)) (⊢q ⊢Γ ⊢σ ⊢S)) (qσ∘[I,t]≈σ,t ⊢Γ ⊢S ⊢σ (t[σ] ⊢s ⊢σ)))) , _ , conv-Se ⊢T (s-, ⊢σ ⊢S (t[σ] ⊢s ⊢σ))
  presup-≈ (box-[] ⊢σ ⊢t)
    with presup-s ⊢σ | presup-tm ⊢t
  ... | ⊢Γ , ⊢Δ      | _ , _ , ⊢T        = ⊢Γ , t[σ] (□-I ⊢t) ⊢σ , conv (□-I (t[σ] ⊢t (s-； L.[ [] ] ⊢σ (⊢κ ⊢Γ) refl))) (≈-sym (□-[] ⊢σ ⊢T)) , _ , conv-Se (□-wf ⊢T) ⊢σ
  presup-≈ (unbox-[] Ψ ⊢t ⊢σ eqΨ)
    with presup-s ⊢σ | presup-tm ⊢t | ∥-⊢s′ Ψ ⊢σ
  ... | ⊢Γ , ⊢ΨΔ     | _ , _ , ⊢□T   | Ψ′ , Γ′ , refl , eqΨ′ , ⊢σ∥
      rewrite eqΨ
        with inv-□-wf ⊢□T
  ...     | _ , ⊢T         = ⊢Γ , conv (t[σ] (□-E Ψ ⊢t ⊢ΨΔ eqΨ) ⊢σ) (≈-trans ([∘]-Se ⊢T ⊢I；n ⊢σ) (≈-conv-Se (≈-refl ⊢T) (s-∘ ⊢σ ⊢I；n) (s-≈-trans (；-∘ Ψ (s-I ⊢Δ) ⊢σ ⊢ΨΔ eqΨ) (；-cong Ψ′ (I-∘ ⊢σ∥) ⊢Γ eqΨ′)))) , conv (□-E Ψ′ (conv (t[σ] ⊢t ⊢σ∥) (□-[] ⊢σ∥ ⊢T)) ⊢Γ eqΨ′) (≈-trans ([∘]-Se ⊢T ⊢σ∥；1 ⊢I；Lσn) (≈-conv-Se (≈-refl ⊢T) (s-∘ ⊢I；Lσn ⊢σ∥；1) (s-≈-trans (；-∘ L.[ [] ] ⊢σ∥ ⊢I；Lσn (⊢κ ⊢Γ′) refl) (s-≈-trans (s-≈-sym (；-≡-cong Ψ′ (s-∘ (s-I ⊢Γ′) ⊢σ∥) ⊢Γ eqΨ′ (sym (+-identityʳ _)))) (；-cong Ψ′ (∘-I ⊢σ∥) ⊢Γ eqΨ′))))) , _ , (conv-Se ⊢T (s-； Ψ′ ⊢σ∥ ⊢Γ eqΨ′))
    where
      ⊢Γ′ = ⊢⇒∥⊢ Ψ′ ⊢Γ
      ⊢Δ = ⊢⇒∥⊢ Ψ ⊢ΨΔ
      ⊢I；n = s-； Ψ (s-I ⊢Δ) ⊢ΨΔ eqΨ
      ⊢I；Lσn = s-； Ψ′ (s-I ⊢Γ′) ⊢Γ eqΨ′
      ⊢σ∥；1 = s-； L.[ [] ] ⊢σ∥ (⊢κ ⊢Γ′) refl
  presup-≈ (rec-β-ze ⊢T ⊢t ⊢r)
    with presup-tm ⊢t
  ... | ⊢Γ , _            = ⊢Γ , N-E ⊢T ⊢t ⊢r (ze-I ⊢Γ) , ⊢t , _ , conv-Se ⊢T (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) (ze-I ⊢Γ))
  presup-≈ (rec-β-su {Γ = Γ} {T = T} {s = s} {r = r} {t = t} ⊢T ⊢s ⊢r ⊢t)
    with presup-tm ⊢r
  ... | ⊢TNΓ@(⊢∷ ⊢NΓ@(⊢∷ ⊢Γ _) _) , _ = ⊢Γ , N-E ⊢T ⊢s ⊢r (su-I ⊢t) , conv (t[σ] ⊢r ⊢I,t,recTrst) (≈-trans ([∘]-Se ⊢T ⊢[wk∘wk],su[v1] ⊢I,t,recTrst) (≈-conv-Se (≈-refl ⊢T) (s-∘ ⊢I,t,recTrst ⊢[wk∘wk],su[v1]) lemma)) , _ , conv-Se ⊢T (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) (su-I ⊢t))
    where
      ⊢recTsrt = N-E ⊢T ⊢s ⊢r ⊢t
      ⊢I,t,recTrst = s-, (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) ⊢t) ⊢T (N-E ⊢T ⊢s ⊢r ⊢t)
      ⊢wk∘wk = s-∘ (⊢wk ⊢TNΓ) (⊢wk ⊢NΓ)
      ⊢[wk∘wk],su[v1] = s-, ⊢wk∘wk (N-wf 0 ⊢Γ) (conv (su-I (conv (vlookup ⊢TNΓ (there here)) (N[wk][wk]≈N 0 ⊢TNΓ))) (≈-sym (N-[] 0 ⊢wk∘wk)))

      lemma : Γ ⊢s ((wk ∘ wk) , su (v 1)) ∘ ((I , t) , rec T s r t) ≈ I , su t ∶ N ∺ Γ
      lemma =
        begin
          ((wk ∘ wk) , su (v 1)) ∘ ((I , t) , rec T s r t)
        ≈⟨ ,-∘ ⊢wk∘wk (N-wf 0 ⊢Γ) (conv (su-I (conv (vlookup ⊢TNΓ (there here)) (N[wk][wk]≈N 0 ⊢TNΓ))) (≈-sym (N-[] 0 ⊢wk∘wk))) ⊢I,t,recTrst ⟩
          (wk ∘ wk ∘ ((I , t) , rec T s r t)) , su (v 1) [ (I , t) , rec T s r t ]
        ≈⟨ ,-cong lemma-l (N-wf 0 ⊢Γ) (≈-conv lemma-r (≈-sym (N-[] 0 (s-∘ ⊢I,t,recTrst ⊢wk∘wk)))) ⟩
          I , su t
        ∎
        where
          lemma-r : Γ ⊢ su (v 1) [ (I , t) , rec T s r t ] ≈ su t ∶ N
          lemma-r =
            begin
              su (v 1) [ (I , t) , rec T s r t ]
            ≈⟨ su-[] ⊢I,t,recTrst (conv (vlookup ⊢TNΓ (there here)) (N[wk][wk]≈N 0 ⊢TNΓ)) ⟩
              su (v 1 [ (I , t) , rec T s r t ])
            ≈⟨ su-cong (≈-conv ([,]-v-su (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) ⊢t) ⊢T ⊢recTsrt here) (N-[][] 0 (⊢wk ⊢NΓ) (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) ⊢t))) ⟩
              su (v 0 [ I , t ])
            ≈⟨ su-cong (≈-conv ([,]-v-ze (s-I ⊢Γ) (N-wf 0 ⊢Γ) (conv ⊢t (≈-sym ([I] (N-wf 0 ⊢Γ))))) ([I] (N-wf 0 ⊢Γ))) ⟩
              su t
            ∎
            where
              open ER

          open SR

          lemma-l : Γ ⊢s wk ∘ wk ∘ ((I , t) , rec T s r t) ≈ I ∶ Γ
          lemma-l =
            begin
              wk ∘ wk ∘ ((I , t) , rec T s r t)
            ≈⟨ ∘-assoc (⊢wk ⊢NΓ) (⊢wk ⊢TNΓ) ⊢I,t,recTrst ⟩
              wk ∘ (wk ∘ ((I , t) , rec T s r t))
            ≈⟨ ∘-cong (wk∘[σ,t]≈σ ⊢TNΓ (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) ⊢t) ⊢recTsrt) (s-≈-refl (⊢wk ⊢NΓ)) ⟩
              wk ∘ (I , t)
            ≈⟨ wk∘[σ,t]≈σ ⊢NΓ (s-I ⊢Γ) (conv ⊢t (≈-sym ([I] (N-wf 0 ⊢Γ)))) ⟩
              I
            ∎

  presup-≈ (Λ-β ⊢S ⊢t ⊢s)
    with presup-tm ⊢t
  ... | ⊢∷ ⊢Γ _ , _ , ⊢T = ⊢Γ , Λ-E (Λ-I ⊢S ⊢t) ⊢s , t[σ] ⊢t (⊢I,t ⊢Γ ⊢S ⊢s) , _ , conv-Se ⊢T (⊢I,t ⊢Γ ⊢S ⊢s)
  presup-≈ (Λ-η ⊢s)
    with presup-tm ⊢s
  ... | ⊢Γ , _ , ⊢ΠST
      with inv-Π-wf′ ⊢ΠST | inv-Π-wf ⊢ΠST
  ...   | _ , ⊢S          | _ , ⊢T        = ⊢Γ , ⊢s , conv (Λ-I ⊢S (Λ-E (conv (t[σ] ⊢s (⊢wk ⊢SΓ)) (Π-[] (⊢wk ⊢SΓ) ⊢S′ ⊢T′)) ⊢v0)) (Π-cong ⊢S′ (≈-refl ⊢S′) (≈-trans ([∘]-Se ⊢T′ (⊢q ⊢SΓ (⊢wk ⊢SΓ) ⊢S) ⊢I,v0) (≈-trans (≈-conv-Se (≈-refl ⊢T′) (s-∘ ⊢I,v0 (⊢q ⊢SΓ (⊢wk ⊢SΓ) ⊢S)) (q[wk]∘[I,v0]≈I ⊢SΓ)) ([I] ⊢T′)))) , _ , ⊢ΠST
    where
      ⊢SΓ = ⊢∷ ⊢Γ ⊢S
      ⊢S[wk] = conv-Se ⊢S (⊢wk ⊢SΓ)
      ⊢v0 = vlookup ⊢SΓ here
      ⊢S′ = lift-⊢-Se-max ⊢S
      ⊢T′ = lift-⊢-Se-max′ ⊢T
      ⊢I,v0 = ⊢I,t ⊢SΓ ⊢S[wk] ⊢v0
  presup-≈ (□-β Ψ ⊢t ⊢ΨΓ eq)
    with presup-tm ⊢t
  ... | ⊢κ ⊢Γ , _ , ⊢T  = ⊢ΨΓ , □-E Ψ (□-I ⊢t) ⊢ΨΓ eq , t[σ] ⊢t (s-； Ψ (s-I ⊢Γ) ⊢ΨΓ eq) , _ , conv-Se ⊢T (s-； Ψ (s-I ⊢Γ) ⊢ΨΓ eq)
  presup-≈ (□-η ⊢s)
    with presup-tm ⊢s
  ... | ⊢Γ , _ , ⊢□T   = ⊢Γ , ⊢s , conv (□-I (□-E L.[ [] ] ⊢s (⊢κ ⊢Γ) refl)) (≈-trans (≈-sym (□-[] (s-I ⊢Γ) (lift-⊢-Se-max (proj₂ (inv-□-wf ⊢□T))))) ([I] (lift-⊢-Se-max′ ⊢□T))) , _ , ⊢□T
  presup-≈ ([I] ⊢t)
    with presup-tm ⊢t
  ... | ⊢Γ , _ , ⊢T    = ⊢Γ , conv (t[σ] ⊢t (s-I ⊢Γ)) ([I] ⊢T) , ⊢t , _ , ⊢T
  presup-≈ ([p] ⊢σ T∈Γ′)
    with presup-s ⊢σ
  ... | ⊢Γ , ⊢SΓ′@(⊢∷ ⊢Γ′ ⊢S)
      with ∈!⇒ty-wf ⊢Γ′ T∈Γ′
  ...   | _ , ⊢T        = ⊢Γ , t[σ] (vlookup ⊢Γ′ T∈Γ′) (s-p ⊢σ) , conv (t[σ] (vlookup ⊢SΓ′ (there T∈Γ′)) ⊢σ) (≈-trans ([∘]-Se ⊢T (⊢wk ⊢SΓ′) ⊢σ) (≈-conv-Se (≈-refl ⊢T) (s-∘ ⊢σ (⊢wk ⊢SΓ′)) (wk∘σ≈pσ ⊢SΓ′ ⊢σ))) , _ , conv-Se ⊢T (s-p ⊢σ)
  presup-≈ ([∘] ⊢τ ⊢σ ⊢t)
    with presup-s ⊢τ | presup-tm ⊢t
  ... | ⊢Γ , _ | _ , _ , ⊢T = ⊢Γ , t[σ] ⊢t (s-∘ ⊢τ ⊢σ) , conv (t[σ] (t[σ] ⊢t ⊢σ) ⊢τ) ([∘]-Se ⊢T ⊢σ ⊢τ) , _ , conv-Se ⊢T (s-∘ ⊢τ ⊢σ)
  presup-≈ ([,]-v-ze ⊢σ ⊢S ⊢t)
    with presup-s ⊢σ
  ... | ⊢Γ , ⊢Δ             = ⊢Γ , conv (t[σ] (vlookup ⊢SΔ here) (s-, ⊢σ ⊢S ⊢t)) (≈-trans ([∘]-Se ⊢S (⊢wk ⊢SΔ) (s-, ⊢σ ⊢S ⊢t)) (≈-conv-Se (≈-refl ⊢S) (s-∘ (s-, ⊢σ ⊢S ⊢t) (⊢wk ⊢SΔ)) (wk∘[σ,t]≈σ ⊢SΔ ⊢σ ⊢t))) , ⊢t , _ , (conv-Se ⊢S ⊢σ)
    where
      ⊢SΔ = ⊢∷ ⊢Δ ⊢S
  presup-≈ ([,]-v-su ⊢σ ⊢S ⊢s T∈Δ)
    with presup-s ⊢σ
  ... | ⊢Γ , ⊢Δ
      with ∈!⇒ty-wf ⊢Δ T∈Δ
  ...   | _ , ⊢T        = ⊢Γ , conv (t[σ] (vlookup ⊢SΔ (there T∈Δ)) (s-, ⊢σ ⊢S ⊢s)) (≈-trans ([∘]-Se ⊢T (⊢wk ⊢SΔ) (s-, ⊢σ ⊢S ⊢s)) (≈-conv-Se (≈-refl ⊢T) (s-∘ (s-, ⊢σ ⊢S ⊢s) (⊢wk ⊢SΔ)) (wk∘[σ,t]≈σ ⊢SΔ ⊢σ ⊢s))) , t[σ] (vlookup ⊢Δ T∈Δ) ⊢σ , _ , conv-Se ⊢T ⊢σ
    where
      ⊢SΔ = ⊢∷ ⊢Δ ⊢S
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
  presup-s-≈ (p-cong σ≈τ)
    with presup-s-≈ σ≈τ
  ...  | ⊢Γ , ⊢σ , ⊢τ , ⊢∷ ⊢Δ _         = ⊢Γ , s-p ⊢σ , s-p ⊢τ , ⊢Δ
  presup-s-≈ (∘-cong σ≈σ′ τ≈τ′)
    with presup-s-≈ σ≈σ′ | presup-s-≈ τ≈τ′
  ...  | ⊢Γ , ⊢σ , ⊢σ′ , _
       | _  , ⊢τ , ⊢τ′ , ⊢Δ             = ⊢Γ , s-∘ ⊢σ ⊢τ , s-∘ ⊢σ′ ⊢τ′ , ⊢Δ
  presup-s-≈ (,-cong σ≈τ ⊢T t≈t′)
    with presup-s-≈ σ≈τ | presup-≈ t≈t′
  ...  | ⊢Γ , ⊢σ , ⊢τ , ⊢Δ
       | _  , ⊢t , ⊢t′ , _              = ⊢Γ , s-, ⊢σ ⊢T ⊢t , s-, ⊢τ ⊢T (conv ⊢t′ (≈-conv-Se (≈-refl ⊢T) ⊢σ σ≈τ)) , ⊢∷ ⊢Δ ⊢T
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
  presup-s-≈ (p-∘ ⊢σ ⊢τ)
    with presup-s ⊢σ | presup-s ⊢τ
  ... | _ , ⊢∷ ⊢Δ ⊢T | ⊢Γ , _           = ⊢Γ , s-∘ ⊢τ (s-p ⊢σ) , s-p (s-∘ ⊢τ ⊢σ) , ⊢Δ
  presup-s-≈ (；-∘ Ψs ⊢σ ⊢τ ⊢ΨsΓ refl)
    with presup-s ⊢σ | presup-s ⊢τ
  ...  | _ , ⊢Δ      | ⊢Γ , _
       with ∥-⊢s′ Ψs ⊢τ
  ...     | Ψs′ , Γ′ , refl , eql , ⊢τ∥ = ⊢Γ , s-∘ ⊢τ (s-； Ψs ⊢σ ⊢ΨsΓ refl) , s-； Ψs′ (s-∘ ⊢τ∥ ⊢σ) ⊢Γ eql , ⊢κ ⊢Δ
  presup-s-≈ (p-, ⊢τ ⊢T ⊢t)
    with presup-s ⊢τ
  ...  | ⊢Γ , ⊢Δ                        = ⊢Γ , s-p (s-, ⊢τ ⊢T ⊢t) , ⊢τ , ⊢Δ
  presup-s-≈ (,-ext ⊢σ)
    with presup-s ⊢σ
  ... | ⊢Γ , ⊢TΔ@(⊢∷ ⊢Δ ⊢T)             = ⊢Γ , ⊢σ , s-, (s-p ⊢σ) ⊢T (conv (t[σ] (vlookup ⊢TΔ here) ⊢σ) (≈-trans ([∘]-Se ⊢T (⊢wk ⊢TΔ) ⊢σ) (≈-conv-Se (≈-refl ⊢T) (s-∘ ⊢σ (⊢wk ⊢TΔ)) (s-≈-trans (p-∘ (s-I ⊢TΔ) ⊢σ) (p-cong (I-∘ ⊢σ)))))) , ⊢TΔ
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
