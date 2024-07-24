{-# OPTIONS --without-K --safe #-}

module NonCumulative.Statics.Unascribed.Anno.Presup where

open import Lib
open import NonCumulative.Statics.Unascribed.Anno
open import NonCumulative.Statics.Unascribed.Anno.Refl
open import NonCumulative.Statics.Unascribed.Anno.Misc
open import NonCumulative.Statics.Unascribed.Anno.Properties.Contexts

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
  presup-tm (vlookup ⊢Γ T∈Γ) = ⊢Γ , ∈!⇒ty-wf ⊢Γ T∈Γ
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
  presup-≈ (Π-cong S≈S′ T≈T′ eq)
    with presup-≈ S≈S′ | presup-≈ T≈T′
  ...  | ⊢Γ , ⊢S , ⊢S′ , _
       | _ , ⊢T , ⊢T′ , _                  = ⊢Γ , Π-wf ⊢S ⊢T eq , Π-wf ⊢S′ {!⊢T′!} eq , Se-wf _ ⊢Γ
  presup-≈ (Liftt-cong n T≈T′)
    with presup-≈ T≈T′
  ...  | ⊢Γ , ⊢T , ⊢T′ , _                 = ⊢Γ , Liftt-wf n ⊢T , Liftt-wf n ⊢T′ , Se-wf (n + _) ⊢Γ
  presup-≈ (v-≈ ⊢Γ T∈Γ)                    = ⊢Γ , vlookup ⊢Γ T∈Γ , vlookup ⊢Γ T∈Γ , ∈!⇒ty-wf ⊢Γ T∈Γ
  presup-≈ (ze-≈ ⊢Γ)                       = ⊢Γ , ze-I ⊢Γ , ze-I ⊢Γ , N-wf ⊢Γ
  presup-≈ (su-cong t≈t′)
    with presup-≈ t≈t′
  ...  | ⊢Γ , ⊢t , ⊢t′ , ⊢N                 = ⊢Γ , su-I ⊢t , su-I ⊢t′ , ⊢N
  presup-≈ (rec-cong x s≈i s≈i₁ s≈i₂ s≈i₃) = {!!}
  presup-≈ (Λ-cong x s≈i x₁)               = {!!}
  presup-≈ ($-cong x x₁ s≈i s≈i₁ x₂)       = {!!}
  presup-≈ (liftt-cong n s≈i)              = {!!}
  presup-≈ (unlift-cong n x s≈i)           = {!!}
  presup-≈ ([]-cong s≈i x)                 = {!!}
  presup-≈ (ze-[] x)                       = {!!}
  presup-≈ (su-[] x x₁)                    = {!!}
  presup-≈ (rec-[] x x₁ x₂ x₃ x₄)          = {!!}
  presup-≈ (Λ-[] x x₁ x₂ x₃)               = {!!}
  presup-≈ ($-[] x x₁ x₂ x₃ x₄ x₅)         = {!!}
  presup-≈ (liftt-[] n x x₁ x₂)            = {!!}
  presup-≈ (unlift-[] n x x₁)              = {!!}
  presup-≈ (rec-β-ze x x₁ x₂)              = {!!}
  presup-≈ (rec-β-su x x₁ x₂ x₃)           = {!!}
  presup-≈ (Λ-β x x₁ x₂ x₃ x₄)             = {!!}
  presup-≈ (Λ-η x x₁ x₂ x₃)                = {!!}
  presup-≈ (L-β n x)                       = {!!}
  presup-≈ (L-η n x)                       = {!!}
  presup-≈ ([I] x)                         = {!!}
  presup-≈ ([wk] ⊢Γ x x₁)                  = {!!}
  presup-≈ ([∘] x x₁ x₂)                   = {!!}
  presup-≈ ([,]-v-ze x x₁ x₂)              = {!!}
  presup-≈ ([,]-v-su ⊢Δ x x₁ x₂ x₃)        = {!!}
  presup-≈ (≈-conv s≈i s≈i₁)               = {!!}
  presup-≈ (≈-sym s≈i)                     = {!!}
  presup-≈ (≈-trans s≈i s≈i₁)              = {!!}


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
