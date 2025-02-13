{-# OPTIONS --without-K --safe #-}

module NonCumulative.Statics.InterAscribed.Presup where

open import Lib
open import NonCumulative.Statics.InterAscribed.Full

presup-⊢≈ : ⊢ Γ ≈ Δ →
            ----------------
            ⊢ Γ × ⊢ Δ
presup-⊢≈ []-≈ = ⊢[] , ⊢[]
presup-⊢≈ (∷-cong ⊢Γ ⊢Δ x₂ ⊢T ⊢T′ x₅ x₆) 
  = (⊢∷ ⊢Γ ⊢T) , (⊢∷ ⊢Δ ⊢T′)

mutual
  presup-tm : ∀ {i} →
              Γ ⊢ t ∶[ i ] T →
              ----------------------
              ⊢ Γ × Γ ⊢ T ∶[ 1 + i ] Se i
  presup-tm (N-wf ⊢Γ) 
    = ⊢Γ , Se-wf zero ⊢Γ
  presup-tm (Se-wf i ⊢Γ) 
    = ⊢Γ , Se-wf (suc i) ⊢Γ
  presup-tm (Liftt-wf n ⊢T)
    with presup-tm ⊢T
  ...  | ⊢Γ , _              = ⊢Γ , Se-wf (n + _) ⊢Γ
  presup-tm (Π-wf ⊢Γ _ _ _) = ⊢Γ , (Se-wf _ ⊢Γ) 
  presup-tm (vlookup ⊢Γ T∈Γ) = ⊢Γ , {!   !} -- ∈⇒ty-wf
  presup-tm (ze-I ⊢Γ)        = ⊢Γ , N-wf ⊢Γ
  presup-tm (su-I ⊢t)        = presup-tm ⊢t
  presup-tm (N-E ⊢Γ ⊢T ⊢s ⊢r ⊢t) 
    = {!   !} -- t[σ]-Se , ⊢I,t
  presup-tm (Λ-I ⊢Γ ⊢S ⊢T i≡maxjk)
    with ⊢∷ ⊢Γ _ , ⊢T ← presup-tm ⊢T  
    = ⊢Γ , (Π-wf ⊢Γ ⊢S ⊢T i≡maxjk)
  presup-tm (Λ-E ⊢Γ ⊢T ⊢s ⊢r ⊢t k≡maxij) 
    = ⊢Γ , {!   !} -- t[σ]-Se , ⊢I,t
  presup-tm (L-I n ⊢t)
    with ⊢Γ , ⊢T ← presup-tm ⊢t = ⊢Γ , Liftt-wf _ ⊢T
  presup-tm (L-E n ⊢Γ ⊢T ⊢t) = ⊢Γ , ⊢T
  presup-tm (t[σ] ⊢Δ ⊢t ⊢σ)
    with _ , ⊢T ← presup-tm ⊢t
       | ⊢Γ , _ ← presup-s ⊢σ 
    = ⊢Γ , {!   !} -- t[σ]-Se
  presup-tm (conv ⊢Γ ⊢t ⊢S S≈T) 
    with _ , _ , ⊢T , _ ← presup-≈ S≈T
      = ⊢Γ , ⊢T

  presup-s : Γ ⊢s σ ∶ Δ →
             ------------
             ⊢ Γ × ⊢ Δ
  presup-s (s-I ⊢Γ) = ⊢Γ , ⊢Γ
  presup-s (s-wk ⊢T∷Γ@(⊢∷ ⊢Γ ⊢T)) = ⊢T∷Γ , ⊢Γ
  presup-s (s-∘ _ ⊢σ ⊢τ) 
    with ⊢Γ , _ ← presup-s ⊢σ
       | _ , ⊢Δ ← presup-s ⊢τ
    = ⊢Γ , ⊢Δ
  presup-s (s-, ⊢Γ ⊢Δ ⊢σ ⊢T ⊢t) = ⊢Γ , ⊢∷ ⊢Δ ⊢T
  presup-s (s-conv _ ⊢σ Δ≈Ψ)
    with ⊢Γ , _ ← presup-s ⊢σ
    with _ , ⊢Ψ ← presup-⊢≈ Δ≈Ψ 
    = ⊢Γ , ⊢Ψ

  presup-≈ : ∀ {i} →
            Γ ⊢ s ≈ t ∶[ i ] T →
            -----------------------------------
            ⊢ Γ × Γ ⊢ s ∶[ i ] T × Γ ⊢ t ∶[ i ] T × Γ ⊢ T ∶[ 1 + i ] Se i
  presup-≈ (N-[] ⊢σ) 
    with ⊢Γ , ⊢Δ ← presup-s ⊢σ
    = ⊢Γ , {!   !} , N-wf ⊢Γ , (Se-wf _ ⊢Γ) -- t[σ]-Se
  presup-≈ (Se-[] i ⊢σ) 
    with ⊢Γ , ⊢Δ ← presup-s ⊢σ
    = ⊢Γ , {!   !} , Se-wf _ ⊢Γ , (Se-wf _ ⊢Γ) -- t[σ]-Se
  presup-≈ (Liftt-[] n ⊢Δ ⊢σ ⊢T) 
    with ⊢Γ , _ ← presup-s ⊢σ
    = ⊢Γ , {!   !} , Liftt-wf {!   !} {!   !} , (Se-wf _ ⊢Γ) -- t[σ]-Se
  presup-≈ (Π-[] ⊢Δ ⊢σ ⊢S ⊢T k≡maxij) 
    with ⊢Γ , _ ← presup-s ⊢σ
    = {!   !} , {!  !} , Π-wf ⊢Γ {!   !} {!   !} k≡maxij , (Se-wf _ ⊢Γ) -- t[σ]-Se
  presup-≈ (Π-cong x x₁ s≈t s≈t₁ x₂) = {!   !}
  presup-≈ (Liftt-cong n s≈t) = {!   !}
  presup-≈ (v-≈ x x₁) = {!   !}
  presup-≈ (ze-≈ x) = {!   !}
  presup-≈ (su-cong s≈t) = {!   !}
  presup-≈ (rec-cong x x₁ s≈t s≈t₁ s≈t₂ s≈t₃) = {!   !}
  presup-≈ (Λ-cong x x₁ s≈t s≈t₁ x₂) = {!   !}
  presup-≈ ($-cong x x₁ x₂ s≈t s≈t₁ x₃) = {!   !}
  presup-≈ (liftt-cong n s≈t) = {!   !}
  presup-≈ (unlift-cong n x x₁ s≈t) = {!   !}
  presup-≈ ([]-cong x s≈t x₁) = {!   !}
  presup-≈ (ze-[] x) = {!   !}
  presup-≈ (su-[] x x₁ x₂) = {!   !}
  presup-≈ (rec-[] x x₁ x₂ x₃ x₄ x₅) = {!   !}
  presup-≈ (Λ-[] x x₁ x₂ x₃ x₄) = {!   !}
  presup-≈ ($-[] x x₁ x₂ x₃ x₄ x₅ x₆) = {!   !}
  presup-≈ (liftt-[] n x x₁ x₂ x₃) = {!   !}
  presup-≈ (unlift-[] n x x₁ x₂ x₃) = {!   !}
  presup-≈ (rec-β-ze x x₁ x₂ x₃) = {!   !}
  presup-≈ (rec-β-su x x₁ x₂ x₃ x₄) = {!   !}
  presup-≈ (Λ-β x x₁ x₂ x₃ x₄) = {!   !}
  presup-≈ (Λ-η x x₁ x₂ x₃ x₄) = {!   !}
  presup-≈ (L-β n x) = {!   !}
  presup-≈ (L-η n x x₁ x₂) = {!   !}
  presup-≈ ([I] x) = {!   !}
  presup-≈ ([wk] x x₁ x₂) = {!   !}
  presup-≈ ([∘] x x₁ x₂ x₃ x₄) = {!   !}
  presup-≈ ([,]-v-ze x x₁ x₂ x₃ x₄) = {!   !}
  presup-≈ ([,]-v-su x x₁ x₂ x₃ x₄ x₅) = {!   !}
  presup-≈ (≈-conv x s≈t s≈t₁) = {!   !}
  presup-≈ (≈-sym s≈t) = {!   !}
  presup-≈ (≈-trans x x₁ s≈t s≈t₁) = {!   !}