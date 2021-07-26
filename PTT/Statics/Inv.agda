{-# OPTIONS --without-K --safe #-}

module PTT.Statics.Inv where

open import Lib
open import PTT.Statics
open import PTT.Statics.Misc
open import PTT.Statics.Complement
open import PTT.Statics.Stable
-- open import PTT.Statics.EnvSubst
-- open import PTT.Statics.RecHelper

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
  ty-eq⇒env-ty-wf-gen (Π-cong ⊢S S≈S′ T≈T′)         = {!!}
  ty-eq⇒env-ty-wf-gen (v-≈ x x₁)                    = {!!}
  ty-eq⇒env-ty-wf-gen (ze-≈ x)                      = {!!}
  ty-eq⇒env-ty-wf-gen (su-cong s≈t)                 = {!!}
  ty-eq⇒env-ty-wf-gen (rec-cong s≈t s≈t₁ s≈t₂ s≈t₃) = {!!}
  ty-eq⇒env-ty-wf-gen (Λ-cong s≈t)                  = {!!}
  ty-eq⇒env-ty-wf-gen ($-cong s≈t s≈t₁)             = {!!}
  ty-eq⇒env-ty-wf-gen ([]-cong x s≈t)               = {!!}
  ty-eq⇒env-ty-wf-gen (ze-[] x)                     = {!!}
  ty-eq⇒env-ty-wf-gen (su-[] x x₁)                  = {!!}
  ty-eq⇒env-ty-wf-gen (Λ-[] x x₁)                   = {!!}
  ty-eq⇒env-ty-wf-gen ($-[] x x₁ x₂)                = {!!}
  ty-eq⇒env-ty-wf-gen (rec-[] x x₁ x₂ x₃ x₄)        = {!!}
  ty-eq⇒env-ty-wf-gen (rec-β-ze x x₁ x₂)            = {!!}
  ty-eq⇒env-ty-wf-gen (rec-β-su x x₁ x₂ x₃)         = {!!}
  ty-eq⇒env-ty-wf-gen (Λ-β x x₁)                    = {!!}
  ty-eq⇒env-ty-wf-gen (Λ-η x)                       = {!!}
  ty-eq⇒env-ty-wf-gen ([I] x)                       = {!!}
  ty-eq⇒env-ty-wf-gen (↑-lookup x x₁)               = {!!}
  ty-eq⇒env-ty-wf-gen ([∘] x x₁ x₂)                 = {!!}
  ty-eq⇒env-ty-wf-gen ([,]-v-ze x x₁ x₂)            = {!!}
  ty-eq⇒env-ty-wf-gen ([,]-v-su x x₁ x₂ x₃)         = {!!}
  ty-eq⇒env-ty-wf-gen (≈-cumu s≈t)                  = {!!}
  ty-eq⇒env-ty-wf-gen (≈-conv s≈t x)                = {!!}
  ty-eq⇒env-ty-wf-gen (≈-sym s≈t)                   = {!!}
  ty-eq⇒env-ty-wf-gen (≈-trans s≈t s≈t₁)            = {!!}

  subst-eq⇒env-subst-wf-gen : Γ ⊢s σ ≈ τ ∶ Δ →
                              -----------------------------------
                              ⊢ Γ × Γ ⊢s σ ∶ Δ × Γ ⊢s τ ∶ Δ × ⊢ Δ
  subst-eq⇒env-subst-wf-gen σ≈τ = {!!}
