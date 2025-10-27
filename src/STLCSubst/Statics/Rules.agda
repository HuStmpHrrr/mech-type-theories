{-# OPTIONS --without-K --safe #-}

module STLCSubst.Statics.Rules where

open import Lib
open import STLCSubst.Statics.Definitions


infix 4 _⊢_∶_

data _⊢_∶_ : Ctx → Exp → Typ → Set where
  vlookup : ∀ {x} →
            x ∶ T ∈ Γ →
            ------------
            Γ ⊢ v x ∶ T
  ze-I    : Γ ⊢ ze ∶ N
  su-I    : Γ ⊢ t ∶ N →
            -------------
            Γ ⊢ su t ∶ N
  N-E     : Γ ⊢ s ∶ T →
            T ∷ N ∷ Γ ⊢ r ∶ T →
            Γ ⊢ t ∶ N →
            ----------------------
            Γ ⊢ rec T s r t ∶ T
  Λ-I     : S ∷ Γ ⊢ t ∶ T →
            ------------------
            Γ ⊢ Λ t ∶ S ⟶ T
  Λ-E     : Γ ⊢ r ∶ S ⟶ T →
            Γ ⊢ s ∶ S →
            ------------------
            Γ ⊢ r $ s ∶ T

infix 4 _⊢w_∶_ _⊢s_∶_

_⊢w_∶_ : Ctx → Wk → Ctx → Set
Γ ⊢w ϕ ∶ Δ = ∀ {x T} → x ∶ T ∈ Δ → ϕ x ∶ T ∈ Γ

_⊢s_∶_ : Ctx → Subst → Ctx → Set
Γ ⊢s σ ∶ Δ = ∀ {x T} → x ∶ T ∈ Δ → Γ ⊢ σ x ∶ T

infix 4 _⊢_≈_∶_

data _⊢_≈_∶_ : Ctx → Exp → Exp → Typ → Set where
  v-≈      : ∀ {x} →
             x ∶ T ∈ Γ →
             -----------------------------------
             Γ ⊢ v x              ≈ v x ∶ T
  ze-≈     : Γ ⊢ ze               ≈ ze ∶ N
  su-cong  : Γ ⊢ t                ≈ t′ ∶ N →
             ------------------------------------
             Γ ⊢ su t             ≈ su t′ ∶ N
  rec-cong : Γ ⊢ s                ≈ s′ ∶ T →
             T ∷ N ∷ Γ ⊢ r        ≈ r′ ∶ T →
             Γ ⊢ t                ≈ t′ ∶ N →
             -----------------------------------------
             Γ ⊢ rec T s r t      ≈ rec T s′ r′ t′ ∶ T
  Λ-cong   : S ∷ Γ ⊢ t            ≈ t′ ∶ T →
             -------------------------------------
             Γ ⊢ Λ t              ≈ Λ t′ ∶ S ⟶ T
  $-cong   : Γ ⊢ r                ≈ r′ ∶ S ⟶ T →
             Γ ⊢ s                ≈ s′ ∶ S →
             -------------------------------------
             Γ ⊢ r $ s            ≈ r′ $ s′ ∶ T
  rec-β-ze : Γ ⊢ s ∶ T →
             T ∷ N ∷ Γ ⊢ r ∶ T →
             -----------------------------
             Γ ⊢ rec T s r ze     ≈ s ∶ T
  rec-β-su : Γ ⊢ s ∶ T →
             T ∷ N ∷ Γ ⊢ r ∶ T →
             Γ ⊢ t ∶ N →
             --------------------------------------------------
             Γ ⊢ rec T s r (su t) ≈ r [ id ↦ t ↦ rec T s r t ] ∶ T
  Λ-β      : S ∷ Γ ⊢ t ∶ T →
             Γ ⊢ s ∶ S →
             --------------------------------------
             Γ ⊢ Λ t $ s          ≈ t [ id ↦ s ] ∶ T
  Λ-η      : Γ ⊢ t ∶ S ⟶ T →
             ------------------------------------------------
             Γ ⊢ t                ≈ Λ ((t [ ↑ ]) $ v 0) ∶ S ⟶ T
  ≈-sym    : Γ ⊢ t                ≈ t′ ∶ T →
             -------------------------------
             Γ ⊢ t′               ≈ t ∶ T
  ≈-trans  : Γ ⊢ t                ≈ t′ ∶ T →
             Γ ⊢ t′               ≈ t″ ∶ T →
             --------------------------------
             Γ ⊢ t                ≈ t″ ∶ T


infix 4 _⊢s_≈_∶_

_⊢s_≈_∶_ : Ctx → Subst → Subst → Ctx → Set
Γ ⊢s σ ≈ σ′ ∶ Δ = ∀ {x T} → x ∶ T ∈ Δ → Γ ⊢ σ x ≈ σ′ x ∶ T

≈-refl : Γ ⊢ t ∶ T → Γ ⊢ t ≈ t ∶ T
≈-refl (vlookup T∈Γ) = v-≈ T∈Γ
≈-refl ze-I          = ze-≈
≈-refl (su-I t)      = su-cong (≈-refl t)
≈-refl (N-E s r t)   = rec-cong (≈-refl s) (≈-refl r) (≈-refl t)
≈-refl (Λ-I t)       = Λ-cong (≈-refl t)
≈-refl (Λ-E r s)     = $-cong (≈-refl r) (≈-refl s)

subst-≈-refl : Γ ⊢s σ ∶ Δ → Γ ⊢s σ ≈ σ ∶ Δ
subst-≈-refl ⊢σ T∈Δ = ≈-refl (⊢σ T∈Δ)
