{-# OPTIONS --without-K --safe #-}

module Mint.Statics.Properties.Contexts where

open import Data.Nat.Properties

open import Lib
open import Mint.Statics.Full
open import Mint.Statics.Refl
open import Mint.Statics.Misc

≈⇒len≡ : ⊢ Γ ≈ Δ →
         -------------
         len Γ ≡ len Δ
≈⇒len≡ []-≈                 = refl
≈⇒len≡ (κ-cong Γ≈Δ)         = cong suc (≈⇒len≡ Γ≈Δ)
≈⇒len≡ (∺-cong Γ≈Δ _ _ _ _) = ≈⇒len≡ Γ≈Δ

≈⇒∥≈ : ∀ Ψs Ψs′ →
       ⊢ Ψs ++⁺ Γ ≈ Ψs′ ++⁺ Δ →
       len Ψs ≡ len Ψs′ →
       ------------------------
       ⊢ Γ ≈ Δ
≈⇒∥≈ [] [] ⊢≈ eq                               = ⊢≈
≈⇒∥≈ (_ ∷ Ψs) (_ ∷ Ψs′) (κ-cong ⊢≈) eq         = ≈⇒∥≈ Ψs Ψs′ ⊢≈ (suc-injective eq)
≈⇒∥≈ (_ ∷ Ψs) (_ ∷ Ψs′) (∺-cong ⊢≈ _ _ _ _) eq = ≈⇒∥≈ (_ ∷ Ψs) (_ ∷ Ψs′) ⊢≈ eq

≈⇒∥⇒∥ : ∀ Ψs →
        ⊢ Ψs ++⁺ Γ ≈ Δ →
        -----------------
        ∃₂ λ Ψs′ Δ′ → Δ ≡ Ψs′ ++⁺ Δ′ × len Ψs ≡ len Ψs′ × ⊢ Γ ≈ Δ′
≈⇒∥⇒∥ [] ⊢≈                           = [] , _ , refl , refl , ⊢≈
≈⇒∥⇒∥ (_ ∷ Ψs) (κ-cong ⊢≈)
  with ≈⇒∥⇒∥ Ψs ⊢≈
...  | Ψs′ , Δ′ , eq , eql , ⊢≈∥      = [] ∷ Ψs′ , Δ′ , cong ([] ∷⁺_) eq , cong suc eql , ⊢≈∥
≈⇒∥⇒∥ (_ ∷ Ψs) (∺-cong ⊢≈ _ _ _ _)
  with ≈⇒∥⇒∥ (_ ∷ Ψs) ⊢≈
... | Ψ ∷ Ψs′ , Δ′ , refl , eql , ⊢≈∥ = (_ ∷ Ψ) ∷ Ψs′ , Δ′ , refl , eql , ⊢≈∥

⊢⇒∥⊢ : ∀ Ψs →
       ⊢ Ψs ++⁺ Γ →
       ------------
       ⊢ Γ
⊢⇒∥⊢ [] ⊢Γ               = ⊢Γ
⊢⇒∥⊢ (_ ∷ Ψs) (⊢κ ⊢++)   = ⊢⇒∥⊢ Ψs ⊢++
⊢⇒∥⊢ (_ ∷ Ψs) (⊢∺ ⊢++ _) = ⊢⇒∥⊢ (_ ∷ Ψs) ⊢++

≈⇒∺⇒∺ : ⊢ T ∺ Γ ≈ Δ →
        -----------------
        ∃₂ λ T′ Δ′ → Δ ≡ T′ ∺ Δ′ × Γ ⊢ T ≈ T′ × Δ′ ⊢ T ≈ T′ × ⊢ Γ ≈ Δ′
≈⇒∺⇒∺ (∺-cong ⊢≈ ⊢T ⊢T′ T≈T′ T≈T′₁) = _ , _ , refl , (_ , T≈T′) , (_ , T≈T′₁) , ⊢≈

∈!⇒ty-wf : ∀ {x} →
           ⊢ Γ →
           x ∶ T ∈! Γ →
           ------------
           Γ ⊢ T
∈!⇒ty-wf ⊢TΓ@(⊢∺ ⊢Γ ⊢T) here = _ , t[σ]-Se ⊢T (s-wk ⊢TΓ)
∈!⇒ty-wf ⊢TΓ@(⊢∺ ⊢Γ ⊢S) (there T∈Γ)
  with ∈!⇒ty-wf ⊢Γ T∈Γ
...  | i , ⊢T                = _ , t[σ]-Se ⊢T (s-wk ⊢TΓ)

presup-⊢≈ : ⊢ Γ ≈ Δ →
            ----------
            ⊢ Γ × ⊢ Δ
presup-⊢≈ []-≈ = ⊢[] , ⊢[]
presup-⊢≈ (κ-cong Γ≈Δ)
  with presup-⊢≈ Γ≈Δ
...  | ⊢Γ , ⊢Δ = ⊢κ ⊢Γ , ⊢κ ⊢Δ
presup-⊢≈ (∺-cong Γ≈Δ ⊢T ⊢T′ _ _)
  with presup-⊢≈ Γ≈Δ
...  | ⊢Γ , ⊢Δ = ⊢∺ ⊢Γ ⊢T , ⊢∺ ⊢Δ ⊢T′

∈!⇒ty≈ : ∀ {x} →
         ⊢ Γ ≈ Δ →
         x ∶ T ∈! Γ →
         ---------------------------------
         ∃ λ T′ → (x ∶ T′ ∈! Δ) × Γ ⊢ T ≈ T′ × Δ ⊢ T ≈ T′
∈!⇒ty≈ (∺-cong Γ≈Δ ⊢T ⊢T′ T≈T′ T≈T′₁) here
  with presup-⊢≈ Γ≈Δ
...  | ⊢Γ , ⊢Δ                            = -, here , (-, []-cong-Se′ T≈T′ (s-wk (⊢∺ ⊢Γ ⊢T))) , -, []-cong-Se′ T≈T′₁ (s-wk (⊢∺ ⊢Δ ⊢T′))
∈!⇒ty≈ (∺-cong Γ≈Δ ⊢T ⊢T′ _ _) (there T∈Γ)
  with presup-⊢≈ Γ≈Δ | ∈!⇒ty≈ Γ≈Δ T∈Γ
...  | ⊢Γ , ⊢Δ
     | T′ , T′∈Δ , (_ , T≈T′) , _ , T≈T′₁ = -, there T′∈Δ , (-, []-cong-Se′ T≈T′ (s-wk (⊢∺ ⊢Γ ⊢T))) , (-, []-cong-Se′ T≈T′₁ (s-wk (⊢∺ ⊢Δ ⊢T′)))

⊢≈-sym : ⊢ Γ ≈ Δ → ⊢ Δ ≈ Γ
⊢≈-sym []-≈                           = []-≈
⊢≈-sym (κ-cong Γ≈Δ)                   = κ-cong (⊢≈-sym Γ≈Δ)
⊢≈-sym (∺-cong Γ≈Δ ⊢T ⊢T′ T≈T′ T≈T′₁) = ∺-cong (⊢≈-sym Γ≈Δ) ⊢T′ ⊢T (≈-sym T≈T′₁) (≈-sym T≈T′)
