{-# OPTIONS --without-K --safe #-}

module kMLTT.Statics.Properties where

open import Lib

import kMLTT.Statics.Full as F
open import kMLTT.Statics.Concise as C
open import kMLTT.Statics.Equiv
import kMLTT.Statics.Presup as Presup
open import kMLTT.Statics.Properties.Ops as Ops
  using ( O-I
        ; O-∘
        ; O-p
        ; O-,
        ; O-+
        ; I-∥
        ; ∘-∥
        ; ∥-+
        )
  public

≈-refl : Γ ⊢ t ∶ T →
         --------------
         Γ ⊢ t ≈ t ∶ T
≈-refl ⊢t = ≈-trans (≈-sym ([I] ⊢t)) ([I] ⊢t)

s-≈-refl : Γ ⊢s σ ∶ Δ →
           --------------
           Γ ⊢s σ ≈ σ ∶ Δ
s-≈-refl ⊢σ = s-≈-trans (s-≈-sym (I-∘ ⊢σ)) (I-∘ ⊢σ)

presup-tm : Γ ⊢ t ∶ T →
            ------------
            ⊢ Γ × Γ ⊢ T
presup-tm ⊢t
  with Presup.presup-tm (C⇒F-tm ⊢t)
...  | ⊢Γ , _ , ⊢T = F⇒C-⊢ ⊢Γ , -, F⇒C-tm ⊢T

presup-s : Γ ⊢s σ ∶ Δ →
           ------------
           ⊢ Γ × ⊢ Δ
presup-s ⊢σ
  with Presup.presup-s (C⇒F-s ⊢σ)
...  | ⊢Γ , ⊢Δ = F⇒C-⊢ ⊢Γ , F⇒C-⊢ ⊢Δ

presup-≈ : Γ ⊢ s ≈ t ∶ T →
           -----------------------------------
           ⊢ Γ × Γ ⊢ s ∶ T × Γ ⊢ t ∶ T × Γ ⊢ T
presup-≈ s≈t
  with Presup.presup-≈ (C⇒F-≈ s≈t)
...  | ⊢Γ , ⊢s , ⊢t , _ , ⊢T = F⇒C-⊢ ⊢Γ , F⇒C-tm ⊢s , F⇒C-tm ⊢t , -, F⇒C-tm ⊢T

presup-s-≈ : Γ ⊢s σ ≈ τ ∶ Δ →
             -----------------------------------
             ⊢ Γ × Γ ⊢s σ ∶ Δ × Γ ⊢s τ ∶ Δ × ⊢ Δ
presup-s-≈ σ≈τ
  with Presup.presup-s-≈ (C⇒F-s-≈ σ≈τ)
...  | ⊨Γ , ⊢σ , ⊢τ , ⊢Δ = F⇒C-⊢ ⊨Γ , F⇒C-s ⊢σ , F⇒C-s ⊢τ , F⇒C-⊢ ⊢Δ

O-resp-≈ : ∀ n →
           Γ ⊢s σ ≈ σ′ ∶ Δ →
           -----------------
           O σ n ≡ O σ′ n
O-resp-≈ n σ≈σ′ = Ops.O-resp-≈ n (C⇒F-s-≈ σ≈σ′)

∥-resp-≈′ : ∀ Ψs →
            Γ ⊢s σ ≈ σ′ ∶ Ψs ++⁺ Δ →
            --------------------------------------------------
            ∃₂ λ Ψs′ Γ′ →
              Γ ≡ Ψs′ ++⁺ Γ′ × len Ψs′ ≡ O σ (len Ψs) × Γ′ ⊢s σ ∥ len Ψs ≈ σ′ ∥ len Ψs ∶ Δ
∥-resp-≈′ Ψs σ≈σ′
  with Ops.∥-resp-≈′ Ψs (C⇒F-s-≈ σ≈σ′)
... | Ψs′ , Γ′ , eq , eql , σ≈σ′∥ = Ψs′ , Γ′ , eq , eql , F⇒C-s-≈ σ≈σ′∥
