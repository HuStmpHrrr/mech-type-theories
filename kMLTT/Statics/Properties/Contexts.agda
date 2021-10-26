{-# OPTIONS --without-K --safe #-}

module kMLTT.Statics.Properties.Contexts where

open import Data.Nat.Properties

open import Lib
open import kMLTT.Statics.Full
open import kMLTT.Statics.Refl
open import kMLTT.Statics.Misc

≈⇒len≡ : ⊢ Γ ≈ Δ →
         ----------
         len Γ ≡ len Δ
≈⇒len≡ []-≈               = refl
≈⇒len≡ (κ-cong Γ≈Δ)       = cong suc (≈⇒len≡ Γ≈Δ)
≈⇒len≡ (∷-cong Γ≈Δ _ _ _) = ≈⇒len≡ Γ≈Δ

≈⇒∥≈ : ∀ Ψs Ψs′ →
       ⊢ Ψs ++⁺ Γ ≈ Ψs′ ++⁺ Δ →
       len Ψs ≡ len Ψs′ →
       ------------------------
       ⊢ Γ ≈ Δ
≈⇒∥≈ [] [] ⊢≈ eq                             = ⊢≈
≈⇒∥≈ (_ ∷ Ψs) (_ ∷ Ψs′) (κ-cong ⊢≈) eq       = ≈⇒∥≈ Ψs Ψs′ ⊢≈ (suc-injective eq)
≈⇒∥≈ (_ ∷ Ψs) (_ ∷ Ψs′) (∷-cong ⊢≈ _ _ _) eq = ≈⇒∥≈ (_ ∷ Ψs) (_ ∷ Ψs′) ⊢≈ eq

∈!⇒ty-wf : ∀ {x} →
           ⊢ Γ →
           x ∶ T ∈! Γ →
           ------------
           Γ ⊢ T
∈!⇒ty-wf ⊢TΓ@(⊢∷ ⊢Γ ⊢T) here = _ , conv-Se ⊢T (⊢wk ⊢TΓ)
∈!⇒ty-wf ⊢TΓ@(⊢∷ ⊢Γ ⊢S) (there T∈Γ)
  with ∈!⇒ty-wf ⊢Γ T∈Γ
...  | i , ⊢T                = _ , conv-Se ⊢T (⊢wk ⊢TΓ)

∈!⇒ty≈ : ∀ {x} →
         ⊢ Γ →
         ⊢ Γ ≈ Δ →
         x ∶ T ∈! Γ →
         ---------------------------------
         ∃ λ T′ → (x ∶ T′ ∈! Δ) × Γ ⊢ T ≈ T′
∈!⇒ty≈ ⊢Γ (∷-cong Γ≈Δ ⊢T ⊢T′ T≈T′) here = -, here , _ , ≈-conv-Se T≈T′ (⊢wk ⊢Γ)
∈!⇒ty≈ ⊢TΓ@(⊢∷ ⊢Γ _) (∷-cong Γ≈Δ _ _ _) (there T∈Γ)
  with ∈!⇒ty≈ ⊢Γ Γ≈Δ T∈Γ
...  | T′ , T′∈Δ , _ , T≈T′             = -, there T′∈Δ , _ , ≈-conv-Se T≈T′ (⊢wk ⊢TΓ)
