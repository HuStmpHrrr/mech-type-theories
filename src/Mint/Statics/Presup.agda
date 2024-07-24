{-# OPTIONS --without-K --safe #-}

-- Presupposition: from a judgment, we can obtain the well-formedness of its
-- components.
module Mint.Statics.Presup where

open import Data.Nat.Properties as ℕ

open import Lib
open import Mint.Statics.Full
open import Mint.Statics.Refl
open import Mint.Statics.Misc
open import Mint.Statics.CtxEquiv
open import Mint.Statics.PER
open import Mint.Statics.Properties.Contexts
open import Mint.Statics.Properties.Substs
open import Mint.Statics.Properties.Ops

mutual
  presup-tm : Γ ⊢ t ∶ T →
              ------------
              ⊢ Γ × Γ ⊢ T
  presup-tm (N-wf i ⊢Γ)                   = ⊢Γ , suc i , Se-wf i ⊢Γ
  presup-tm (Se-wf i ⊢Γ)                  = ⊢Γ , suc (suc i) , Se-wf (suc i) ⊢Γ
  presup-tm (Π-wf ⊢S ⊢T)                  = presup-tm ⊢S
  presup-tm (□-wf {i = i} ⊢T)
    with ⊢κ ⊢Γ ← proj₁ (presup-tm ⊢T)     = ⊢Γ , suc i , Se-wf i ⊢Γ
  presup-tm (vlookup ⊢Γ T∈Γ)              = ⊢Γ , ∈!⇒ty-wf ⊢Γ T∈Γ
  presup-tm (ze-I ⊢T)                     = ⊢T , zero , N-wf zero ⊢T
  presup-tm (su-I ⊢t)                     = presup-tm ⊢t
  presup-tm (N-E ⊢T ⊢s ⊢r ⊢t)
    with ⊢Γ ← proj₁ (presup-tm ⊢t)        = ⊢Γ , _ , t[σ]-Se ⊢T (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) ⊢t)
  presup-tm (Λ-I ⊢S ⊢t)
    with ⊢∺ ⊢Γ ⊢S , _ , ⊢T ← presup-tm ⊢t = ⊢Γ , _ , Π-wf (lift-⊢-Se-max ⊢S) (lift-⊢-Se-max′ ⊢T)
  presup-tm (Λ-E ⊢S ⊢T ⊢t ⊢s)
    with _  , _ , ⊢S ← presup-tm ⊢s
       | ⊢Γ , _ , ⊢Π ← presup-tm ⊢t       = ⊢Γ , _ , t[σ]-Se ⊢T (⊢I,t ⊢Γ ⊢S ⊢s)
  presup-tm (□-I ⊢t)
    with ⊢κ ⊢Γ , _ , ⊢T ← presup-tm ⊢t    = ⊢Γ , _ , □-wf ⊢T
  presup-tm (□-E Ψs ⊢T ⊢t ⊢ΨsΓ eq)
    with ⊢Γ , _ , ⊢□T ← presup-tm ⊢t      = ⊢ΨsΓ , _ , t[σ]-Se ⊢T (s-； Ψs (s-I ⊢Γ) ⊢ΨsΓ eq)
  presup-tm (t[σ] ⊢t ⊢σ)
    with _ , _ , ⊢T ← presup-tm ⊢t        = proj₁ (presup-s ⊢σ) , _ , t[σ]-Se ⊢T ⊢σ
  presup-tm (cumu ⊢T)
    with ⊢Γ ← proj₁ (presup-tm ⊢T)        = ⊢Γ , suc (suc _) , Se-wf (suc _) ⊢Γ
  presup-tm (conv ⊢t S≈T)
    with ⊢Γ , _ , ⊢T , _ ← presup-≈ S≈T   = ⊢Γ , _ , ⊢T


  presup-s : Γ ⊢s σ ∶ Δ →
             ------------
             ⊢ Γ × ⊢ Δ
  presup-s (s-I ⊢Γ)             = ⊢Γ , ⊢Γ
  presup-s (s-wk ⊢TΓ@(⊢∺ ⊢Γ _)) = ⊢TΓ , ⊢Γ
  presup-s (s-∘ ⊢σ ⊢δ)          = proj₁ (presup-s ⊢σ) , proj₂ (presup-s ⊢δ)
  presup-s (s-, ⊢σ ⊢T ⊢t)
    with ⊢Γ , ⊢Δ ← presup-s ⊢σ  = ⊢Γ , ⊢∺ ⊢Δ ⊢T
  presup-s (s-； Ψs ⊢σ ⊢ΨsΓ eq) = ⊢ΨsΓ , ⊢κ (proj₂ (presup-s ⊢σ))
  presup-s (s-conv ⊢σ Δ′≈Δ)     = proj₁ (presup-s ⊢σ) , proj₂ (presup-⊢≈ Δ′≈Δ)


  presup-≈ : Γ ⊢ s ≈ t ∶ T →
             -----------------------------------
             ⊢ Γ × Γ ⊢ s ∶ T × Γ ⊢ t ∶ T × Γ ⊢ T
  presup-≈ (N-[] i ⊢σ)
    with ⊢Γ , ⊢Δ ← presup-s ⊢σ = ⊢Γ , t[σ]-Se (N-wf _ ⊢Δ) ⊢σ , N-wf _ ⊢Γ , _ , Se-wf _ ⊢Γ
  presup-≈ (Se-[] i ⊢σ)
    with ⊢Γ , ⊢Δ ← presup-s ⊢σ = ⊢Γ , t[σ]-Se (Se-wf _ ⊢Δ) ⊢σ , Se-wf _ ⊢Γ , _ , Se-wf _ ⊢Γ
  presup-≈ (Π-[] ⊢σ ⊢S ⊢T)
    with ⊢Γ , ⊢Δ ← presup-s ⊢σ = ⊢Γ
                               , t[σ]-Se (Π-wf ⊢S ⊢T) ⊢σ
                               , Π-wf (t[σ]-Se ⊢S ⊢σ) (t[σ]-Se ⊢T (⊢q ⊢Γ ⊢σ ⊢S))
                               , _ , Se-wf _ ⊢Γ
  presup-≈ (□-[] ⊢σ ⊢T)
    with ⊢Γ , ⊢Δ ← presup-s ⊢σ = ⊢Γ , t[σ]-Se (□-wf ⊢T) ⊢σ , □-wf (t[σ]-Se ⊢T (⊢σ；1 (⊢κ ⊢Γ) ⊢σ)) , _ , Se-wf _ ⊢Γ
  presup-≈ (Π-cong ⊢S S≈S′ T≈T′)
    with ⊢Γ , ⊢S , ⊢S′ , _ ← presup-≈ S≈S′
      | _ , ⊢T , ⊢T′ , _ ← presup-≈ T≈T′   = ⊢Γ , Π-wf ⊢S ⊢T , Π-wf ⊢S′ (ctxeq-tm (∺-cong′ ⊢Γ ⊢S ⊢S′ S≈S′) ⊢T′) , _ , Se-wf _ ⊢Γ
  presup-≈ (□-cong T≈T′)
    with ⊢κ ⊢Γ , ⊢T , ⊢T′ , _ ← presup-≈ T≈T′ = ⊢Γ , □-wf ⊢T , □-wf ⊢T′ , _ , Se-wf _ ⊢Γ
  presup-≈ (v-≈ ⊢Γ T∈Γ) = ⊢Γ , vlookup ⊢Γ T∈Γ , vlookup ⊢Γ T∈Γ , _ , proj₂ (∈!⇒ty-wf ⊢Γ T∈Γ)
  presup-≈ (ze-≈ ⊢Γ) = ⊢Γ , ze-I ⊢Γ , ze-I ⊢Γ , _ , N-wf 0 ⊢Γ
  presup-≈ (su-cong t≈t′)
    with ⊢Γ , ⊢t , ⊢t′ , _ ← presup-≈ t≈t′ = ⊢Γ , su-I ⊢t , su-I ⊢t′ , _ , N-wf 0 ⊢Γ
  presup-≈ (rec-cong ⊢T T≈T′ s≈s′ r≈r′ t≈t′)
    with ⊢NΓ , ⊢T , ⊢T′ , _ ← presup-≈ T≈T′
       | ⊢Γ , ⊢s , ⊢s′ , _ ← presup-≈ s≈s′
       | ⊢TNΓ , ⊢r , ⊢r′ , _ ← presup-≈ r≈r′
       | _ , ⊢t , ⊢t′ , _ ← presup-≈ t≈t′    = ⊢Γ
                                             , N-E ⊢T ⊢s ⊢r ⊢t
                                             , conv
                                               (N-E ⊢T′ (conv ⊢s′ ([]-cong-Se′ T≈T′ (⊢I,ze ⊢Γ))) (ctxeq-tm (∺-cong′ ⊢NΓ ⊢T ⊢T′ T≈T′) (conv ⊢r′ ([]-cong-Se′ T≈T′ (⊢[wk∘wk],su[v1] ⊢TNΓ)))) ⊢t′)
                                               (≈-sym ([]-cong-Se T≈T′ (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) ⊢t) (,-cong (I-≈ ⊢Γ) (N-wf 0 ⊢Γ) (≈-conv-N-[]-sym t≈t′ (s-I ⊢Γ)))))
                                             , _
                                             , (t[σ]-Se ⊢T (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) ⊢t))
  presup-≈ (Λ-cong ⊢S t≈t′)
    with ⊢∺ ⊢Γ _ , ⊢t , ⊢t′ , _ , ⊢T ← presup-≈ t≈t′ = ⊢Γ , Λ-I ⊢S ⊢t , Λ-I ⊢S ⊢t′ , _ , Π-wf (lift-⊢-Se-max ⊢S) (lift-⊢-Se-max′ ⊢T)
  presup-≈ ($-cong ⊢S ⊢T r≈r′ s≈s′)
    with ⊢Γ , ⊢r , ⊢r′ , _ , ⊢ΠST ← presup-≈ r≈r′
       | _ , ⊢s , ⊢s′ , _ ← presup-≈ s≈s′         = ⊢Γ
                                                  , Λ-E ⊢S ⊢T ⊢r ⊢s
                                                  , conv (Λ-E ⊢S ⊢T ⊢r′ ⊢s′) ([]-cong-Se″ ⊢T (⊢I,t ⊢Γ ⊢S ⊢s′) (,-cong (I-≈ ⊢Γ) ⊢S (≈-conv (≈-sym s≈s′) (≈-sym ([I] ⊢S)))))
                                                  , _
                                                  , t[σ]-Se ⊢T (⊢I,t ⊢Γ ⊢S ⊢s)
  presup-≈ (box-cong t≈t′)
    with ⊢κ ⊢Γ , ⊢t , ⊢t′ , _ , ⊢T ← presup-≈ t≈t′ = ⊢Γ , □-I ⊢t , □-I ⊢t′ , _ , □-wf ⊢T
  presup-≈ (unbox-cong Ψs ⊢T t≈t′ ⊢ΨsΓ eq)
    with ⊢Γ , ⊢t , ⊢t′ , _ , ⊢□T ← presup-≈ t≈t′ = ⊢ΨsΓ , □-E Ψs ⊢T ⊢t ⊢ΨsΓ eq , □-E Ψs ⊢T ⊢t′ ⊢ΨsΓ eq , _ , t[σ]-Se ⊢T (s-； Ψs (s-I ⊢Γ) ⊢ΨsΓ eq)
  presup-≈ ([]-cong t≈t′ σ≈σ′)
    with _ , ⊢t , ⊢t′ , _ , ⊢T ← presup-≈ t≈t′
       | ⊢Γ , ⊢σ , ⊢σ′ , _ ← presup-s-≈ σ≈σ′   = ⊢Γ , t[σ] ⊢t ⊢σ , conv (t[σ] ⊢t′ ⊢σ′) ([]-cong-Se″ ⊢T ⊢σ′ (s-≈-sym σ≈σ′)) , _ , t[σ]-Se ⊢T ⊢σ
  presup-≈ (ze-[] ⊢σ)
    with ⊢Γ , ⊢Δ ← presup-s ⊢σ = ⊢Γ , t[σ]-N (ze-I ⊢Δ) ⊢σ , ze-I ⊢Γ , _ , N-wf 0 ⊢Γ
  presup-≈ (su-[] ⊢σ ⊢t)
    with ⊢Γ ← proj₁ (presup-s ⊢σ) = ⊢Γ , t[σ]-N (su-I ⊢t) ⊢σ , su-I (t[σ]-N ⊢t ⊢σ) , _ , N-wf 0 ⊢Γ
  presup-≈ (rec-[] {Γ = Γ} {σ = σ} {Δ = Δ} {T = T} {t = t} {i = i} ⊢σ ⊢T ⊢s ⊢r ⊢t)
    with ⊢Γ , ⊢Δ ← presup-s ⊢σ = ⊢Γ
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
                                     (conv (t[σ] ⊢r ⊢q[qσ]) (rec-β-su-T-swap ⊢Γ ⊢TNΔ ⊢σ))
                                     (t[σ]-N ⊢t ⊢σ))
                                   (≈-trans
                                     ([∘]-Se ⊢T ⊢qσ (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) (t[σ]-N ⊢t ⊢σ)))
                                     ([]-cong-Se″ ⊢T (s-∘ (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) (t[σ]-N ⊢t ⊢σ)) ⊢qσ) (qσ∘[I,t]≈σ,t ⊢Γ (N-wf 0 ⊢Δ) ⊢σ (t[σ] ⊢t ⊢σ))))
                                , _
                                , t[σ]-Se ⊢T (s-, ⊢σ (N-wf 0 ⊢Δ) (t[σ] ⊢t ⊢σ))
    where
      ⊢qσ = ⊢q-N ⊢Γ ⊢Δ ⊢σ
      ⊢T[qσ] = t[σ]-Se ⊢T ⊢qσ
      ⊢NΓ = ⊢∺ ⊢Γ (N-wf 0 ⊢Γ)
      ⊢q[qσ] = ⊢q ⊢NΓ ⊢qσ ⊢T
      ⊢T[qσ]NΓ = ⊢∺ ⊢NΓ ⊢T[qσ]
      ⊢NΔ = ⊢∺ ⊢Δ (N-wf 0 ⊢Δ)
      ⊢TNΔ = ⊢∺ ⊢NΔ ⊢T

  presup-≈ (Λ-[] ⊢σ ⊢t)
    with ⊢Γ ← proj₁ (presup-s ⊢σ)
       | ⊢∺ _ ⊢S , _ , ⊢T ← presup-tm ⊢t = ⊢Γ
                                         , t[σ] (Λ-I ⊢S ⊢t) ⊢σ
                                         , conv
                                           (Λ-I (t[σ]-Se ⊢S ⊢σ) (t[σ] ⊢t (⊢q ⊢Γ ⊢σ ⊢S)))
                                           (≈-sym (Π-[] ⊢σ (lift-⊢-Se-max ⊢S) (lift-⊢-Se-max′ ⊢T)))
                                         , _
                                         , t[σ]-Se (Π-wf (lift-⊢-Se-max ⊢S) (lift-⊢-Se-max′ ⊢T)) ⊢σ
  presup-≈ ($-[] ⊢S ⊢T ⊢σ ⊢r ⊢s)
    with ⊢Γ , ⊢Δ ← presup-s ⊢σ = ⊢Γ
                               , conv (t[σ] (Λ-E ⊢S ⊢T ⊢r ⊢s) ⊢σ) (≈-trans ([∘]-Se ⊢T (⊢I,t ⊢Δ ⊢S ⊢s) ⊢σ) ([]-cong-Se″ ⊢T (s-∘ ⊢σ (⊢I,t ⊢Δ ⊢S ⊢s)) ([I,t]∘σ≈σ,t[σ] (⊢∺ ⊢Δ ⊢S) ⊢σ ⊢s)))
                               , conv (Λ-E (t[σ]-Se ⊢S ⊢σ) (t[σ]-Se ⊢T (⊢q ⊢Γ ⊢σ ⊢S)) (conv (t[σ] ⊢r ⊢σ) (Π-[] ⊢σ (lift-⊢-Se-max ⊢S) (lift-⊢-Se-max′ ⊢T))) (t[σ] ⊢s ⊢σ))
                                      (≈-trans ([∘]-Se ⊢T (⊢q ⊢Γ ⊢σ ⊢S) (⊢I,t ⊢Γ (t[σ]-Se ⊢S ⊢σ) (t[σ] ⊢s ⊢σ)))
                                               ([]-cong-Se″ ⊢T (s-∘ (⊢I,t ⊢Γ (t[σ]-Se ⊢S ⊢σ) (t[σ] ⊢s ⊢σ)) (⊢q ⊢Γ ⊢σ ⊢S)) (qσ∘[I,t]≈σ,t ⊢Γ ⊢S ⊢σ (t[σ] ⊢s ⊢σ))))
                               , _
                               , t[σ]-Se ⊢T (s-, ⊢σ ⊢S (t[σ] ⊢s ⊢σ))
  presup-≈ (box-[] ⊢σ ⊢t)
    with ⊢Γ , ⊢Δ ← presup-s ⊢σ
       | _ , _ , ⊢T ← presup-tm ⊢t = ⊢Γ
                                   , t[σ] (□-I ⊢t) ⊢σ
                                   , conv
                                     (□-I (t[σ] ⊢t (s-； L.[ [] ] ⊢σ (⊢κ ⊢Γ) refl)))
                                     (≈-sym (□-[] ⊢σ ⊢T))
                                   , _
                                   , t[σ]-Se (□-wf ⊢T) ⊢σ
  presup-≈ (unbox-[] Ψs ⊢T ⊢t ⊢σ refl)
    with ⊢Γ , ⊢ΨsΔ ← presup-s ⊢σ
       | Ψs′ , Γ′ , refl , eql′ , ⊢σ∥ ← ∥-⊢s′ Ψs ⊢σ = ⊢Γ
                                                     , conv
                                                       (t[σ] (□-E Ψs ⊢T ⊢t ⊢ΨsΔ refl) ⊢σ)
                                                       (≈-trans ([∘]-Se ⊢T ⊢I；n ⊢σ) ([]-cong-Se″ ⊢T (s-∘ ⊢σ ⊢I；n) (s-≈-trans (；-∘ Ψs (s-I ⊢Δ) ⊢σ ⊢ΨsΔ refl) (；-cong Ψs′ (I-∘ ⊢σ∥) ⊢Γ eql′))))
                                                     , conv
                                                       (□-E Ψs′ (t[σ]-Se ⊢T (s-； L.[ [] ] ⊢σ∥ (⊢κ ⊢Γ′) refl)) (conv (t[σ] ⊢t ⊢σ∥) (□-[] ⊢σ∥ ⊢T)) ⊢Γ eql′)
                                                       (≈-trans
                                                         ([∘]-Se ⊢T ⊢σ∥；1 ⊢I；Lσn)
                                                         ([]-cong-Se″ ⊢T (s-∘ ⊢I；Lσn ⊢σ∥；1) (s-≈-trans (；-∘ L.[ [] ] ⊢σ∥ ⊢I；Lσn (⊢κ ⊢Γ′) refl) (s-≈-trans (s-≈-sym (；-≡-cong Ψs′ (s-∘ (s-I ⊢Γ′) ⊢σ∥) ⊢Γ eql′ (sym (+-identityʳ _)))) (；-cong Ψs′ (∘-I ⊢σ∥) ⊢Γ eql′)))))
                                                     , _
                                                     , (t[σ]-Se ⊢T (s-； Ψs′ ⊢σ∥ ⊢Γ eql′))
    where
      ⊢Γ′ = ⊢⇒∥⊢ Ψs′ ⊢Γ
      ⊢Δ = ⊢⇒∥⊢ Ψs ⊢ΨsΔ
      ⊢I；n = s-； Ψs (s-I ⊢Δ) ⊢ΨsΔ refl
      ⊢I；Lσn = s-； Ψs′ (s-I ⊢Γ′) ⊢Γ eql′
      ⊢σ∥；1 = s-； L.[ [] ] ⊢σ∥ (⊢κ ⊢Γ′) refl
  presup-≈ (rec-β-ze ⊢T ⊢t ⊢r)
    with ⊢Γ ← proj₁ (presup-tm ⊢t) = ⊢Γ , N-E ⊢T ⊢t ⊢r (ze-I ⊢Γ) , ⊢t , _ , t[σ]-Se ⊢T (⊢I,t ⊢Γ (N-wf 0 ⊢Γ) (ze-I ⊢Γ))
  presup-≈ (rec-β-su {Γ = Γ} {T = T} {s = s} {r = r} {t = t} ⊢T ⊢s ⊢r ⊢t)
    with ⊢TNΓ@(⊢∺ ⊢NΓ@(⊢∺ ⊢Γ _) _) ← proj₁ (presup-tm ⊢r) = ⊢Γ
                                                          , N-E ⊢T ⊢s ⊢r (su-I ⊢t)
                                                          , conv
                                                            (t[σ] ⊢r ⊢I,t,recTrst)
                                                            (≈-trans ([∘]-Se ⊢T ⊢[wk∘wk],su[v1]′ ⊢I,t,recTrst) ([]-cong-Se″ ⊢T (s-∘ ⊢I,t,recTrst ⊢[wk∘wk],su[v1]′) lemma))
                                                          , _
                                                          , t[σ]-Se ⊢T (⊢I,t ⊢Γ ⊢N (su-I ⊢t))
    where
      ⊢N = N-wf 0 ⊢Γ
      ⊢recTsrt = N-E ⊢T ⊢s ⊢r ⊢t
      ⊢I,t,recTrst = s-, (⊢I,t ⊢Γ ⊢N ⊢t) ⊢T (N-E ⊢T ⊢s ⊢r ⊢t)
      ⊢wk∘wk = s-∘ (s-wk ⊢TNΓ) (s-wk ⊢NΓ)
      ⊢[wk∘wk],su[v1]′ = s-, ⊢wk∘wk ⊢N (conv-N-[]-sym (su-I (⊢vn∶N L.[ T ] ⊢TNΓ refl)) ⊢wk∘wk)

      lemma : Γ ⊢s ((wk ∘ wk) , su (v 1)) ∘ ((I , t) , rec T s r t) ≈ I , su t ∶ N ∺ Γ
      lemma =
        begin
          ((wk ∘ wk) , su (v 1)) ∘ ((I , t) , rec T s r t)
        ≈⟨ ,-∘ ⊢wk∘wk ⊢N (conv-N-[]-sym (su-I (⊢vn∶N L.[ T ] ⊢TNΓ refl)) ⊢wk∘wk) ⊢I,t,recTrst ⟩
          (wk ∘ wk ∘ ((I , t) , rec T s r t)) , su (v 1) [ (I , t) , rec T s r t ]
        ≈⟨ ,-cong lemma-l ⊢N (≈-conv-N-[]-sym lemma-r (s-∘ ⊢I,t,recTrst ⊢wk∘wk)) ⟩
          I , su t
        ∎
        where
          lemma-r : Γ ⊢ su (v 1) [ (I , t) , rec T s r t ] ≈ su t ∶ N
          lemma-r =
            begin
              su (v 1) [ (I , t) , rec T s r t ]
            ≈⟨ su-[] ⊢I,t,recTrst (⊢vn∶N L.[ T ] ⊢TNΓ refl) ⟩
              su (v 1 [ (I , t) , rec T s r t ])
            ≈⟨ su-cong (≈-conv ([,]-v-su (⊢I,t ⊢Γ ⊢N ⊢t) ⊢T ⊢recTsrt here) (N-[][] 0 (s-wk ⊢NΓ) (⊢I,t ⊢Γ ⊢N ⊢t))) ⟩
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
    with ⊢∺ ⊢Γ _ , _ , _ ← presup-tm ⊢t = ⊢Γ , Λ-E ⊢S ⊢T (Λ-I ⊢S ⊢t) ⊢s , t[σ] ⊢t (⊢I,t ⊢Γ ⊢S ⊢s) , _ , t[σ]-Se ⊢T (⊢I,t ⊢Γ ⊢S ⊢s)
  presup-≈ (Λ-η ⊢S ⊢T ⊢s)
    with ⊢Γ , _ , ⊢ΠST ← presup-tm ⊢s = ⊢Γ , ⊢s , conv (Λ-I ⊢S (Λ-E ⊢S[wk] (t[σ]-Se ⊢T (⊢q ⊢SΓ (s-wk ⊢SΓ) ⊢S)) (conv (t[σ] ⊢s (s-wk ⊢SΓ)) (Π-[] (s-wk ⊢SΓ) ⊢S ⊢T)) ⊢v0)) (Π-cong ⊢S (≈-refl ⊢S) (≈-trans ([∘]-Se ⊢T (⊢q ⊢SΓ (s-wk ⊢SΓ) ⊢S) ⊢I,v0) (≈-trans ([]-cong-Se″ ⊢T (s-∘ ⊢I,v0 (⊢q ⊢SΓ (s-wk ⊢SΓ) ⊢S)) (q[wk]∘[I,v0]≈I ⊢SΓ)) ([I] ⊢T)))) , _ , ⊢ΠST
    where
      ⊢SΓ    = ⊢∺ ⊢Γ ⊢S
      ⊢S[wk] = t[σ]-Se ⊢S (s-wk ⊢SΓ)
      ⊢v0    = vlookup ⊢SΓ here
      ⊢I,v0  = ⊢I,t ⊢SΓ ⊢S[wk] ⊢v0
  presup-≈ (□-β Ψs ⊢T ⊢t ⊢ΨsΓ eq)
    with ⊢κ ⊢Γ , _ , _ ← presup-tm ⊢t = ⊢ΨsΓ , □-E Ψs ⊢T (□-I ⊢t) ⊢ΨsΓ eq , t[σ] ⊢t (s-； Ψs (s-I ⊢Γ) ⊢ΨsΓ eq) , _ , t[σ]-Se ⊢T (s-； Ψs (s-I ⊢Γ) ⊢ΨsΓ eq)
  presup-≈ (□-η ⊢T ⊢s)
    with ⊢Γ , _ , ⊢□T ← presup-tm ⊢s = ⊢Γ , ⊢s , conv (□-I (□-E L.[ [] ] ⊢T ⊢s (⊢κ ⊢Γ) refl)) (≈-trans (≈-sym (□-[] (s-I ⊢Γ) (lift-⊢-Se-max ⊢T))) ([I] (lift-⊢-Se-max′ ⊢□T))) , _ , ⊢□T
  presup-≈ ([I] ⊢t)
    with ⊢Γ , _ , ⊢T ← presup-tm ⊢t = ⊢Γ , conv (t[σ] ⊢t (s-I ⊢Γ)) ([I] ⊢T) , ⊢t , _ , ⊢T
  presup-≈ ([wk] ⊢SΓ@(⊢∺ ⊢Γ _) T∈Γ) = ⊢SΓ , t[σ] (vlookup ⊢Γ T∈Γ) (s-wk ⊢SΓ) , vlookup ⊢SΓ (there T∈Γ) , _ , (t[σ]-Se (proj₂ (∈!⇒ty-wf ⊢Γ T∈Γ)) (s-wk ⊢SΓ))
  presup-≈ ([∘] ⊢τ ⊢σ ⊢t)
    with ⊢Γ ← proj₁ (presup-s ⊢τ)
       | _ , _ , ⊢T ← presup-tm ⊢t = ⊢Γ , t[σ] ⊢t (s-∘ ⊢τ ⊢σ) , conv (t[σ] (t[σ] ⊢t ⊢σ) ⊢τ) ([∘]-Se ⊢T ⊢σ ⊢τ) , _ , t[σ]-Se ⊢T (s-∘ ⊢τ ⊢σ)
  presup-≈ ([,]-v-ze ⊢σ ⊢S ⊢t)
    with ⊢Γ , ⊢Δ ← presup-s ⊢σ = ⊢Γ , conv (t[σ] (vlookup ⊢SΔ here) ⊢σ,t) (≈-trans ([∘]-Se ⊢S (s-wk ⊢SΔ) ⊢σ,t) ([]-cong-Se″ ⊢S (s-∘ ⊢σ,t (s-wk ⊢SΔ)) (wk∘[σ,t]≈σ ⊢SΔ ⊢σ ⊢t))) , ⊢t , _ , (t[σ]-Se ⊢S ⊢σ)
    where
      ⊢SΔ = ⊢∺ ⊢Δ ⊢S
      ⊢σ,t = s-, ⊢σ ⊢S ⊢t
  presup-≈ ([,]-v-su ⊢σ ⊢S ⊢s T∈Δ)
    with ⊢Γ , ⊢Δ ← presup-s ⊢σ
      with _ , ⊢T ← ∈!⇒ty-wf ⊢Δ T∈Δ = ⊢Γ , conv (t[σ] (vlookup ⊢SΔ (there T∈Δ)) ⊢σ,s) (≈-trans ([∘]-Se ⊢T (s-wk ⊢SΔ) ⊢σ,s) ([]-cong-Se″ ⊢T (s-∘ ⊢σ,s (s-wk ⊢SΔ)) (wk∘[σ,t]≈σ ⊢SΔ ⊢σ ⊢s))) , t[σ] (vlookup ⊢Δ T∈Δ) ⊢σ , _ , t[σ]-Se ⊢T ⊢σ
    where
      ⊢SΔ = ⊢∺ ⊢Δ ⊢S
      ⊢σ,s = s-, ⊢σ ⊢S ⊢s
  presup-≈ (≈-cumu s≈t)
    with ⊢Γ , ⊢s , ⊢t , _ ← presup-≈ s≈t = ⊢Γ , cumu ⊢s , cumu ⊢t , _ , Se-wf _ ⊢Γ
  presup-≈ (≈-conv s≈t S≈T)
    with ⊢Γ , ⊢s , ⊢t , _ ← presup-≈ s≈t
       | _ , _ , ⊢T , _ ← presup-≈ S≈T   = ⊢Γ , conv ⊢s S≈T , conv ⊢t S≈T , _ , ⊢T
  presup-≈ (≈-sym t≈s)
    with ⊢Γ , ⊢t , ⊢s , ⊢T ← presup-≈ t≈s = ⊢Γ , ⊢s , ⊢t , ⊢T
  presup-≈ (≈-trans s≈t′ t′≈t)
    with ⊢Γ , ⊢s , _ ← presup-≈ s≈t′
       | _ , _ , ⊢t , ⊢T ← presup-≈ t′≈t = ⊢Γ , ⊢s , ⊢t , ⊢T


  presup-s-≈ : Γ ⊢s σ ≈ τ ∶ Δ →
               -----------------------------------
               ⊢ Γ × Γ ⊢s σ ∶ Δ × Γ ⊢s τ ∶ Δ × ⊢ Δ
  presup-s-≈ (I-≈ ⊢Γ)                                     = ⊢Γ , s-I ⊢Γ , s-I ⊢Γ , ⊢Γ
  presup-s-≈ (wk-≈ ⊢TΓ@(⊢∺ ⊢Γ _))                         = ⊢TΓ , s-wk ⊢TΓ , s-wk ⊢TΓ , ⊢Γ
  presup-s-≈ (∘-cong σ≈σ′ τ≈τ′)
    with ⊢Γ , ⊢σ , ⊢σ′ , _ ← presup-s-≈ σ≈σ′
       | _  , ⊢τ , ⊢τ′ , ⊢Δ ← presup-s-≈ τ≈τ′             = ⊢Γ , s-∘ ⊢σ ⊢τ , s-∘ ⊢σ′ ⊢τ′ , ⊢Δ
  presup-s-≈ (,-cong σ≈τ ⊢T t≈t′)
    with ⊢Γ , ⊢σ , ⊢τ , ⊢Δ ← presup-s-≈ σ≈τ
       | _  , ⊢t , ⊢t′ , _ ← presup-≈ t≈t′                = ⊢Γ , s-, ⊢σ ⊢T ⊢t , s-, ⊢τ ⊢T (conv ⊢t′ ([]-cong-Se″ ⊢T ⊢σ σ≈τ)) , ⊢∺ ⊢Δ ⊢T
  presup-s-≈ (；-cong Ψs σ≈τ ⊢ΨsΓ eq)
    with ⊢Γ , ⊢σ , ⊢τ , ⊢Δ ← presup-s-≈ σ≈τ               = ⊢ΨsΓ , s-； Ψs ⊢σ ⊢ΨsΓ eq , s-； Ψs ⊢τ ⊢ΨsΓ eq , ⊢κ ⊢Δ
  presup-s-≈ (I-∘ ⊢σ)
    with ⊢Γ , ⊢Δ ← presup-s ⊢σ                            = ⊢Γ , s-∘ ⊢σ (s-I ⊢Δ) , ⊢σ , ⊢Δ
  presup-s-≈ (∘-I ⊢σ)
    with ⊢Γ , ⊢Δ ← presup-s ⊢σ                            = ⊢Γ , s-∘ (s-I ⊢Γ) ⊢σ , ⊢σ , ⊢Δ
  presup-s-≈ (∘-assoc ⊢σ ⊢σ′ ⊢σ″)                         = proj₁ (presup-s ⊢σ″) , s-∘ ⊢σ″ (s-∘ ⊢σ′ ⊢σ) , s-∘ (s-∘ ⊢σ″ ⊢σ′) ⊢σ , proj₂ (presup-s ⊢σ)
  presup-s-≈ (,-∘ ⊢σ ⊢T ⊢t ⊢τ)                            = proj₁ (presup-s ⊢τ) , s-∘ ⊢τ (s-, ⊢σ ⊢T ⊢t) , s-, (s-∘ ⊢τ ⊢σ) ⊢T (conv (t[σ] ⊢t ⊢τ) ([∘]-Se ⊢T ⊢σ ⊢τ)) , ⊢∺ (proj₂ (presup-s ⊢σ)) ⊢T
  presup-s-≈ (；-∘ Ψs ⊢σ ⊢τ ⊢ΨsΓ refl)
    with ⊢Γ ← proj₁ (presup-s ⊢τ)
       | Ψs′ , Γ′ , refl , eql , ⊢τ∥ ← ∥-⊢s′ Ψs ⊢τ        = ⊢Γ , s-∘ ⊢τ (s-； Ψs ⊢σ ⊢ΨsΓ refl) , s-； Ψs′ (s-∘ ⊢τ∥ ⊢σ) ⊢Γ eql , ⊢κ (proj₂ (presup-s ⊢σ))
  presup-s-≈ (p-, ⊢τ ⊢T ⊢t)
    with ⊢Γ , ⊢Δ ← presup-s ⊢τ                            = ⊢Γ , ⊢p (⊢∺ ⊢Δ ⊢T) (s-, ⊢τ ⊢T ⊢t) , ⊢τ , ⊢Δ
  presup-s-≈ (,-ext ⊢σ)
    with ⊢Γ , ⊢TΔ@(⊢∺ ⊢Δ ⊢T) ← presup-s ⊢σ                = ⊢Γ , ⊢σ , s-, (⊢p ⊢TΔ ⊢σ) ⊢T (conv (t[σ] (vlookup ⊢TΔ here) ⊢σ) (≈-trans ([∘]-Se ⊢T (s-wk ⊢TΔ) ⊢σ) (≈-refl (t[σ]-Se ⊢T (⊢p ⊢TΔ ⊢σ))))) , ⊢TΔ
  presup-s-≈ (；-ext ⊢σ)
    with ⊢Γ , ⊢κ ⊢Δ ← presup-s ⊢σ
       | Ψs′ , Γ′ , refl , eql , ⊢σ∥ ← ∥-⊢s′ ([] ∷ []) ⊢σ = ⊢Γ , ⊢σ , s-； Ψs′ ⊢σ∥ ⊢Γ eql , ⊢κ ⊢Δ
  presup-s-≈ (s-≈-sym σ≈τ)
    with ⊢Γ , ⊢σ , ⊢τ , ⊢Δ ← presup-s-≈ σ≈τ               = ⊢Γ , ⊢τ , ⊢σ , ⊢Δ
  presup-s-≈ (s-≈-trans σ≈σ′ σ′≈σ″)
    with ⊢Γ , ⊢σ , ⊢σ′ , _ ← presup-s-≈ σ≈σ′
       | _  , _  , ⊢σ″ , ⊢Δ ← presup-s-≈ σ′≈σ″            = ⊢Γ , ⊢σ , ⊢σ″ , ⊢Δ
  presup-s-≈ (s-≈-conv σ≈τ Δ′≈Δ)
    with ⊢Γ , ⊢σ , ⊢τ , ⊢Δ′ ← presup-s-≈ σ≈τ              = ⊢Γ , s-conv ⊢σ Δ′≈Δ , s-conv ⊢τ Δ′≈Δ , proj₂ (presup-⊢≈ Δ′≈Δ)
