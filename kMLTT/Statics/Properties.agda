{-# OPTIONS --without-K --safe #-}

module kMLTT.Statics.Properties where

open import Lib

import kMLTT.Statics.Full as F
open import kMLTT.Statics.Concise as C
open import kMLTT.Statics.Equiv
import kMLTT.Statics.Presup as Presup
import kMLTT.Statics.Refl as Refl
import kMLTT.Statics.Properties.Contexts as Ctxₚ
import kMLTT.Statics.PER as PER
import kMLTT.Statics.CtxEquiv as CtxEquiv
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

⊢≈-refl : ⊢ Γ →
             --------
             ⊢ Γ ≈ Γ
⊢≈-refl ⊢Γ = F⇒C-⊢≈ (Refl.≈-Ctx-refl (C⇒F-⊢ ⊢Γ))

⊢≈-sym : ⊢ Γ ≈ Δ →
         ---------
         ⊢ Δ ≈ Γ
⊢≈-sym Γ≈Δ = F⇒C-⊢≈ (Ctxₚ.⊢≈-sym (C⇒F-⊢≈ Γ≈Δ))

⊢≈-trans : ⊢ Γ ≈ Γ′ →
           ⊢ Γ′ ≈ Γ″ →
           -----------
           ⊢ Γ ≈ Γ″
⊢≈-trans Γ≈Γ′ Γ′≈Γ″ = F⇒C-⊢≈ (PER.⊢≈-trans (C⇒F-⊢≈ Γ≈Γ′) (C⇒F-⊢≈ Γ′≈Γ″))

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

ctxeq-tm : ⊢ Γ ≈ Δ →
           Γ ⊢ t ∶ T →
           -----------
           Δ ⊢ t ∶ T
ctxeq-tm Γ≈Δ ⊢t = F⇒C-tm (CtxEquiv.ctxeq-tm (C⇒F-⊢≈ Γ≈Δ) (C⇒F-tm ⊢t))

ctxeq-≈ : ⊢ Γ ≈ Δ →
          Γ ⊢ t ≈ t′ ∶ T →
          -----------------
          Δ ⊢ t ≈ t′ ∶ T
ctxeq-≈ Γ≈Δ t≈t′ = F⇒C-≈ (CtxEquiv.ctxeq-≈ (C⇒F-⊢≈ Γ≈Δ) (C⇒F-≈ t≈t′))

ctxeq-s : ⊢ Γ ≈ Δ →
          Γ ⊢s σ ∶ Γ′ →
          -----------
          Δ ⊢s σ ∶ Γ′
ctxeq-s Γ≈Δ ⊢σ = F⇒C-s (CtxEquiv.ctxeq-s (C⇒F-⊢≈ Γ≈Δ) (C⇒F-s ⊢σ))

ctxeq-s-≈ : ⊢ Γ ≈ Δ →
            Γ ⊢s σ ≈ σ′ ∶ Γ′ →
            ------------------
            Δ ⊢s σ ≈ σ′ ∶ Γ′
ctxeq-s-≈ Γ≈Δ σ≈σ′ = F⇒C-s-≈ (CtxEquiv.ctxeq-s-≈ (C⇒F-⊢≈ Γ≈Δ) (C⇒F-s-≈ σ≈σ′))

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


⊢I-inv : Γ ⊢s I ∶ Δ → ⊢ Γ ≈ Δ
⊢I-inv (s-I ⊢Γ)         = ⊢≈-refl ⊢Γ
⊢I-inv (s-conv ⊢I Δ′≈Δ) = ⊢≈-trans (⊢I-inv ⊢I) Δ′≈Δ

[I]-inv : Γ ⊢ t [ I ] ∶ T → Γ ⊢ t ∶ T
[I]-inv (t[σ] t∶T ⊢I)
  with ctxeq-tm (⊢≈-sym (⊢I-inv ⊢I)) t∶T
...  | ⊢t               = conv ⊢t (≈-sym ([I] (proj₂ (proj₂ (presup-tm ⊢t)))))
[I]-inv (cumu t[I])     = cumu ([I]-inv t[I])
[I]-inv (conv t[I] S≈T) = conv ([I]-inv t[I]) S≈T
