{-# OPTIONS --without-K --safe #-}

open import Level
open import Axiom.Extensionality.Propositional

module NonCumulative.Unascribed.Properties.Equivalence.Consequences (fext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂)  where

open import Lib

import NonCumulative.Ascribed.Consequences fext as A
import NonCumulative.Ascribed.Statics.Properties.Contexts as A
import NonCumulative.Ascribed.Statics.PER as A
import NonCumulative.Ascribed.Statics.CtxEquiv as A
import NonCumulative.Ascribed.Statics.Presup as A
open import NonCumulative.Unascribed.Statics.Full
open import NonCumulative.Unascribed.Statics.Transfer
open import NonCumulative.Unascribed.Properties.Equivalence.Soundness fext
open import NonCumulative.Unascribed.Properties.Equivalence.Completeness

consistency : ∀ {j} → [] ⊢ t ∶ Π (Se j) (v 0) → ⊥
consistency ⊢t′
  with i , Γ , t , ._ , ↝[] , t↝ , ↝Π ↝Se ↝v , ⊢t , _ ← fundamental-⊢t⇒⫢t ⊢t′ 
  = A.consistency-gen ⊢t

presup-tm : Γ ⊢ t ∶ T →
            ----------------------
            ∃ λ i → ⊢ Γ × Γ ⊢ T ∶ Se i
presup-tm ⊢t 
  with i , Γ′ , t′ , T′ , Γ′↝ , t′↝ , T′↝ , ⊢t′ ← U⇒A-tm ⊢t
  with ⊢Γ′ , ⊢T′ ← A.presup-tm ⊢t′
  with ⊢Γ ← A⇒U-⊢ ⊢Γ′ Γ′↝
  with ⊢T ← A⇒U-tm ⊢T′ Γ′↝ T′↝ ↝Se
  = _ , ⊢Γ , ⊢T

presup-s : Γ ⊢s σ ∶ Δ →
           ------------
           ⊢ Γ × ⊢ Δ
presup-s ⊢σ 
  with Γ′ , σ′ , Δ′ , Γ′↝ , σ′↝ , Δ′↝ , ⊢σ′ ← U⇒A-s ⊢σ
  with ⊢Γ′ , ⊢Δ′ ← A.presup-s ⊢σ′
  with ⊢Γ ← A⇒U-⊢ ⊢Γ′ Γ′↝
  with ⊢Δ ← A⇒U-⊢ ⊢Δ′ Δ′↝
  = ⊢Γ , ⊢Δ

presup-⊢≈ : ⊢ Γ ≈ Δ →
            ----------------
            ⊢ Γ × ⊢ Δ
presup-⊢≈ ⊢Γ≈Δ
  with Γ′ , Δ′ , Γ′↝ , Δ′↝ , Γ′≈Δ′ ← U⇒A-⊢≈ ⊢Γ≈Δ
  with ⊢Γ′ , ⊢Δ′ ← A.presup-⊢≈ Γ′≈Δ′
  with ⊢Γ ← A⇒U-⊢ ⊢Γ′ Γ′↝
  with ⊢Δ ← A⇒U-⊢ ⊢Δ′ Δ′↝
  = ⊢Γ , ⊢Δ

presup-≈ : Γ ⊢ s ≈ t ∶ T →
           -----------------------------------
           ∃ λ i → ⊢ Γ × Γ ⊢ s ∶ T × Γ ⊢ t ∶ T × Γ ⊢ T ∶ Se i
presup-≈ s≈t 
  with i , Γ′ , s′ , t′ , T′ , Γ′↝ , s′↝ , t′↝ , T′↝ , s′≈t′ ← U⇒A-≈ s≈t
  with ⊢Γ′ , ⊢s′ , ⊢t′ , ⊢T′ ← A.presup-≈ s′≈t′
  with ⊢Γ ← A⇒U-⊢ ⊢Γ′ Γ′↝
  with ⊢s ← A⇒U-tm ⊢s′ Γ′↝ s′↝ T′↝
  with ⊢t ← A⇒U-tm ⊢t′ Γ′↝ t′↝ T′↝
  with ⊢T ← A⇒U-tm ⊢T′ Γ′↝ T′↝ ↝Se
  = _ , ⊢Γ , ⊢s , ⊢t , ⊢T

presup-s-≈ : Γ ⊢s σ ≈ τ ∶ Δ →
             ---------------------------
             ⊢ Γ × Γ ⊢s σ ∶ Δ × Γ ⊢s τ ∶ Δ × ⊢ Δ
presup-s-≈ σ≈τ
  with Γ′ , σ′ , τ′ , Δ′ , Γ′↝ , σ′↝ , τ′↝ , Δ′↝ , σ′≈τ′ ← U⇒A-s≈ σ≈τ
  with ⊢Γ′ , ⊢σ′ , ⊢τ′ , ⊢Δ′ ← A.presup-s-≈ σ′≈τ′
  with ⊢Γ ← A⇒U-⊢ ⊢Γ′ Γ′↝
  with ⊢σ ← A⇒U-s ⊢σ′ Γ′↝ σ′↝ Δ′↝
  with ⊢τ ← A⇒U-s ⊢τ′ Γ′↝ τ′↝ Δ′↝
  with ⊢Δ ← A⇒U-⊢ ⊢Δ′ Δ′↝
  = ⊢Γ , ⊢σ , ⊢τ , ⊢Δ

ctxeq-tm : ⊢ Γ ≈ Δ →
            Γ ⊢ t ∶ T →
            -----------
            Δ ⊢ t ∶ T
ctxeq-tm Γ≈Δ ⊢t 
  with Γ′ , t′ , T′ , i , Γ′↝ , t′↝ , T′↝ , ⊢t′ ← U⇒A-tm ⊢t
  with Γ₁′ , Δ′ , Γ₁′↝ , Δ'↝ , Γ′≈Δ′ , IHΓ , _ ← fundamental-⊢≈⇒⫢≈ Γ≈Δ
  with Γ₁′≈Γ′ ← IHΓ 0 Γ′↝ (proj₁ (A.presup-tm ⊢t′))
  with Δ′⊢t′ ← A.ctxeq-tm (A.⊢≈-trans (A.⊢≈-sym Γ₁′≈Γ′) Γ′≈Δ′) ⊢t′
  = A⇒U-tm Δ′⊢t′ Δ'↝ t′↝ T′↝

ctxeq-≈ : ⊢ Γ ≈ Δ →
          Γ ⊢ t ≈ s ∶ T →
          -----------------
          Δ ⊢ t ≈ s ∶ T
ctxeq-≈ Γ≈Δ t≈s
  with Γ′ , t′ , s′ , T′ , i , Γ′↝ , t′↝ , s′↝ , T′↝ , t′≈s′ ← U⇒A-≈ t≈s
  with Γ₁′ , Δ′ , Γ₁′↝ , Δ'↝ , Γ′≈Δ′ , IHΓ , _ ← fundamental-⊢≈⇒⫢≈ Γ≈Δ
  with Γ₁′≈Γ′ ← IHΓ 0 Γ′↝ (proj₁ (A.presup-≈ t′≈s′))
  with Δ′⊢t′≈s′ ← A.ctxeq-≈ (A.⊢≈-trans (A.⊢≈-sym Γ₁′≈Γ′) Γ′≈Δ′) t′≈s′
  = A⇒U-≈ Δ′⊢t′≈s′ Δ'↝ t′↝ s′↝ T′↝

ctxeq-s : ⊢ Γ ≈ Δ →
          Γ ⊢s σ ∶ Ψ →
          -----------
          Δ ⊢s σ ∶ Ψ
ctxeq-s Γ≈Δ ⊢σ 
  with Γ′ , σ′ , Ψ′ , Γ′↝ , σ′↝ , Ψ′↝ , ⊢σ′ ← U⇒A-s ⊢σ
  with Γ₁′ , Δ′ , Γ₁′↝ , Δ'↝ , Γ′≈Δ′ , IHΓ , _ ← fundamental-⊢≈⇒⫢≈ Γ≈Δ
  with Γ₁′≈Γ′ ← IHΓ 0 Γ′↝ (proj₁ (A.presup-s ⊢σ′))
  with Δ′⊢σ′ ← A.ctxeq-s (A.⊢≈-trans (A.⊢≈-sym Γ₁′≈Γ′) Γ′≈Δ′) ⊢σ′
  = A⇒U-s Δ′⊢σ′ Δ'↝ σ′↝ Ψ′↝

ctxeq-s-≈ : ⊢ Γ ≈ Δ →
            Γ ⊢s σ ≈ τ ∶ Ψ →
            ------------------
            Δ ⊢s σ ≈ τ ∶ Ψ
ctxeq-s-≈ Γ≈Δ σ≈τ
  with Γ′ , σ′ , τ′ , Ψ′ , Γ′↝ , σ′↝ , τ′↝ , Ψ′↝ , σ′≈τ′ ← U⇒A-s≈ σ≈τ
  with Γ₁′ , Δ′ , Γ₁′↝ , Δ'↝ , Γ′≈Δ′ , IHΓ , _ ← fundamental-⊢≈⇒⫢≈ Γ≈Δ
  with Γ₁′≈Γ′ ← IHΓ 0 Γ′↝ (proj₁ (A.presup-s-≈ σ′≈τ′))
  with Δ′⊢σ′≈τ′ ← A.ctxeq-s-≈ (A.⊢≈-trans (A.⊢≈-sym Γ₁′≈Γ′) Γ′≈Δ′) σ′≈τ′
  = A⇒U-s≈ Δ′⊢σ′≈τ′ Δ'↝ Ψ′↝ σ′↝ τ′↝