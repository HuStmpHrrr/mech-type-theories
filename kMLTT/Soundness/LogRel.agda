{-# OPTIONS --without-K --safe #-}

module kMLTT.Soundness.LogRel where

open import Lib
open import Data.Nat

open import kMLTT.Statics public
open import kMLTT.Semantics.Domain public
open import kMLTT.Semantics.Readback
open import kMLTT.Semantics.PER public

open import kMLTT.Soundness.Restricted public

mt : Substs → UMoT
mt I        = vone
mt wk       = vone
mt (σ , _)  = mt σ
mt (σ ； n) = ins (mt σ) n
mt (σ ∘ δ)  = mt σ ø mt δ

infix 4 _⊢_∶N®_∈Nat

data _⊢_∶N®_∈Nat : Ctxs → Exp → D → Set where
  ze : Γ ⊢ ze ∶N® ze ∈Nat
  su : Γ ⊢ t ≈ su t′ ∶ N →
       Γ ⊢ t′ ∶N® a ∈Nat →
       --------------------
       Γ ⊢ t ∶N® su a ∈Nat
  ne : (∀ {Δ σ} → Δ ⊢r σ ∶ Γ → ∃ λ u → Re map len Δ - c [ mt σ ] ↘ u × Δ ⊢ t [ σ ] ≈ Ne⇒Exp u ∶ N) →
       -----------------------
       Γ ⊢ t ∶N® ↑ N c ∈Nat


module Glu i (rec : ∀ {j} → j < i → ∀ {A B} → Ctxs → Typ → A ≈ B ∈ 𝕌 j → Set) where
  infix 4 _⊢_®_ _⊢_∶_®_∈El_

  mutual

    _⊢_®_ : Ctxs → Typ → A ≈ B ∈ 𝕌 i → Set
    Γ ⊢ T ® ne C≈C′      = ∀ {Δ σ} → Δ ⊢r σ ∶ Γ → let V , _ = C≈C′ (map len Δ) (mt σ) in Δ ⊢ T [ σ ] ≈ Ne⇒Exp V ∶ Se i
    Γ ⊢ T ® N            = Γ ⊢ T ≈ N ∶ Se i
    Γ ⊢ T ® U {j} j<i eq = Γ ⊢ T ≈ Se j ∶ Se i
    Γ ⊢ T ® □ A≈B        = {!!}
    Γ ⊢ T ® Π iA RT      = {!!}

    _⊢_∶_®_∈El_ : Ctxs → Exp → Typ → D → A ≈ B ∈ 𝕌 i → Set
    Γ ⊢ t ∶ T ® a ∈El ne C≈C′      = Σ (Neu a a)
                                   λ { (ne c≈c′) →
                                       ∀ {Δ σ} →
                                       Δ ⊢r σ ∶ Γ →
                                       let V , _ = C≈C′ (map len Δ) (mt σ)
                                           u , _ = c≈c′ (map len Δ) (mt σ)
                                       in Δ ⊢ T [ σ ] ≈ Ne⇒Exp V ∶ Se i
                                        × Δ ⊢ t [ σ ] ≈ Ne⇒Exp u ∶ T [ σ ]
                                      }
    Γ ⊢ t ∶ T ® a ∈El N            = Γ ⊢ t ∶N® a ∈Nat × Γ ⊢ T ≈ N ∶ Se i
    Γ ⊢ t ∶ T ® a ∈El U {j} j<i eq = (Σ (a ∈′ 𝕌 j) λ a∈𝕌 → rec j<i Γ t a∈𝕌) × Γ ⊢ T ≈ Se j ∶ Se i
    Γ ⊢ t ∶ T ® a ∈El □ A≈B        = {!!}
    Γ ⊢ t ∶ T ® a ∈El Π iA RT      = {!!}

-- infix 4 _⊢_®_ _⊢_∶_®_∈El_
