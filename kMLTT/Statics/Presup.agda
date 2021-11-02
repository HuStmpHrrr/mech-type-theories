{-# OPTIONS --without-K --safe #-}

module kMLTT.Statics.Presup where

open import Lib
open import kMLTT.Statics.Full
open import kMLTT.Statics.Refl
open import kMLTT.Statics.Misc
open import kMLTT.Statics.Properties.Pi
open import kMLTT.Statics.Properties.Box
open import kMLTT.Statics.Properties.Contexts
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
  ...  | ⊢Γ , _                   = ⊢Γ , _ , conv-Se ⊢T (s-, (s-I ⊢Γ) (N-wf 0 ⊢Γ) (conv ⊢t (≈-sym ([I] (N-wf 0 ⊢Γ)))))
  presup-tm (Λ-I ⊢S ⊢t)
    with presup-tm ⊢t
  ... | ⊢∷ ⊢Γ ⊢S , _ , ⊢T         = ⊢Γ , _ , Π-wf (lift-⊢-Se-max ⊢S) (lift-⊢-Se-max′ ⊢T)
  presup-tm (Λ-E ⊢t ⊢s)
    with presup-tm ⊢s | presup-tm ⊢t
  ...  | _  , _ , ⊢S
       | ⊢Γ , _ , ⊢Π              = ⊢Γ , _ , conv-Se (proj₂ (inv-Π-wf ⊢Π)) (s-, (s-I ⊢Γ) ⊢S (conv ⊢s (≈-sym ([I] ⊢S))))
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
  ... | ⊢Γ , ⊢Δ      = ⊢Γ , conv-Se (□-wf ⊢T) ⊢σ , □-wf (conv-Se ⊢T (s-； L.[ L.[] ] ⊢σ (⊢κ ⊢Γ) refl)) , _ , Se-wf _ ⊢Γ
  presup-≈ (Π-cong ⊢S T≈T′ S≈S′) = {!!} , {!!} , {!!} , {!!}
  presup-≈ (□-cong s≈t) = {!!}
  presup-≈ (v-≈ x x₁) = {!!}
  presup-≈ (ze-≈ x) = {!!}
  presup-≈ (su-cong s≈t) = {!!}
  presup-≈ (rec-cong x s≈t s≈t₁ s≈t₂ s≈t₃) = {!!}
  presup-≈ (Λ-cong x s≈t) = {!!}
  presup-≈ ($-cong s≈t s≈t₁) = {!!}
  presup-≈ (box-cong s≈t) = {!!}
  presup-≈ (unbox-cong Ψs s≈t x x₁) = {!!}
  presup-≈ ([]-cong s≈t x) = {!!}
  presup-≈ (ze-[] x) = {!!}
  presup-≈ (su-[] x x₁) = {!!}
  presup-≈ (rec-[] x x₁ x₂ x₃ x₄) = {!!}
  presup-≈ (Λ-[] x x₁) = {!!}
  presup-≈ ($-[] x x₁ x₂) = {!!}
  presup-≈ (box-[] x x₁) = {!!}
  presup-≈ (unbox-[] Ψs x x₁ x₂) = {!!}
  presup-≈ (rec-β-ze x x₁ x₂) = {!!}
  presup-≈ (rec-β-su x x₁ x₂ x₃) = {!!}
  presup-≈ (Λ-β x x₁ x₂) = {!!}
  presup-≈ (Λ-η x) = {!!}
  presup-≈ (□-β Ψs x x₁ x₂) = {!!}
  presup-≈ (□-η x) = {!!}
  presup-≈ ([I] x) = {!!}
  presup-≈ ([p] x x₁) = {!!}
  presup-≈ ([∘] x x₁ x₂) = {!!}
  presup-≈ ([,]-v-ze x x₁ x₂) = {!!}
  presup-≈ ([,]-v-su x x₁ x₂ x₃) = {!!}
  presup-≈ (≈-cumu s≈t) = {!!}
  presup-≈ (≈-conv s≈t s≈t₁) = {!!}
  presup-≈ (≈-sym s≈t) = {!!}
  presup-≈ (≈-trans s≈t s≈t₁) = {!!}


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
