{-# OPTIONS --without-K --safe #-}

module CLayered.Statics where

open import CLayered.Typ public
open import Lib

mutual
  data Exp : Set where
    v      : ℕ → Exp
    gv     : ℕ → LSubst → Exp
    ze     : Exp
    su     : Exp → Exp
    Λ      : Exp → Exp
    _$_    : Exp → Exp → Exp
    box    : Exp → Exp
    letbox : Exp → Exp → Exp
    case   : Exp → List Exp → Exp
    _[[_]] : Exp → GSubst → Exp
    _[_]   : Exp → LSubst → Exp

  data LSubst : Set where
    ↑   : LSubst
    I   : LSubst
    _∘_ : LSubst → LSubst → LSubst
    _,_ : LSubst → Exp → LSubst

  data GSubst : Set where
    ↑    : GSubst
    I    : GSubst
    _∘_  : GSubst → GSubst → GSubst
    _,_  : GSubst → Exp → GSubst

variable
  t t′ t″ : Exp
  r r′ r″ : Exp
  s s′ s″ : Exp
  σ σ′ σ″ : GSubst
  τ τ′ τ″ : GSubst
  δ δ′ δ″ : LSubst

infixr 5 _∷′_
data vbranches : LCtx → Typ → List Exp → Set where
  []   : vbranches [] T []
  _∷_  : ∀ {ts} →
         ¬ (S ≡ T) →
         vbranches Γ T ts →
         vbranches (S ∷ Γ) T ts
  _∷′_ : ∀ {ts} →
         S ≡ T →
         vbranches Γ T ts →
         vbranches (S ∷ Γ) T (t ∷ ts)

infix 4 _⊢s_∶_ _﹔_⊢[_]_∶_ _﹔_⊢[_⇒_]_∶_ _﹔_⊢s[_]_∶_

mutual

  data _﹔_⊢[_]_∶_ : GCtx → LCtx → Layer → Exp → Typ → Set where
    vlkup  : ∀ {x} →
             gwfs? Ψ →
             wfs? i Γ →
             x ∶ T ∈ Γ →
             ------------
             Ψ ﹔ Γ ⊢[ i ] v x ∶ T
    gvlkup : ∀ {x} →
             Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
             x ∶ Δ , T ∈ Ψ →
             -----------------------
             Ψ ﹔ Γ ⊢[ i ] gv x δ ∶ T
    ze-I   : gwfs? Ψ →
             wfs? i Γ →
             Ψ ﹔ Γ ⊢[ i ] ze ∶ N
    su-I   : Ψ ﹔ Γ ⊢[ i ] t ∶ N →
             ----------------------
             Ψ ﹔ Γ ⊢[ i ] su t ∶ N
    Λ-I    : Ψ ﹔ S ∷ Γ ⊢[ i ] t ∶ T →
             -------------------------
             Ψ ﹔ Γ ⊢[ i ] Λ t ∶ S ⟶ T
    Λ-E    : Ψ ﹔ Γ ⊢[ i ] r ∶ S ⟶ T →
             Ψ ﹔ Γ ⊢[ i ] s ∶ S →
             -----------------------
             Ψ ﹔ Γ ⊢[ i ] r $ s ∶ T
    □-I    : wfs? one Γ →
             Ψ ﹔ Δ ⊢[ zer ] t ∶ T →
             -----------------------------
             Ψ ﹔ Γ ⊢[ one ] box t ∶ □ Δ T
    □-E    : Ψ ﹔ Γ ⊢[ one ] t ∶ □ Δ T →
             (Δ , T) ∷ Ψ ﹔ Γ ⊢[ one ] s ∶ S →
             ---------------------------------
             Ψ ﹔ Γ ⊢[ one ] letbox t s ∶ S
    □-E′   : ∀ {ts} →
             Ψ ﹔ Γ ⊢[ one ] t ∶ □ Δ T →
             Ψ ﹔ Γ ⊢[ Δ ⇒ T ] ts ∶ S →
             ---------------------------------
             Ψ ﹔ Γ ⊢[ one ] case t ts ∶ S
    t[δ]   : Ψ ﹔ Δ ⊢[ i ] t ∶ T →
             Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
             -------------------------
             Ψ ﹔ Γ ⊢[ i ] t [ δ ] ∶ T
    t[σ]   : Φ ﹔ Γ ⊢[ i ] t ∶ T →
             Ψ ⊢s σ ∶ Φ →
             ---------------------------
             Ψ ﹔ Γ ⊢[ i ] t [[ σ ]] ∶ T

  data _﹔_⊢[_⇒_]_∶_ : GCtx → LCtx → LCtx → Typ → List Exp → Typ → Set where
    bs-N : ∀ {tz tsu t$ tvs} →
           vbranches Δ N tvs →
           Ψ ﹔ Γ ⊢[ one ] tz ∶ T →
           (Δ , N) ∷ Ψ ﹔ Γ ⊢[ one ] tsu ∶ T →
           (∀ {S} → wf? zer S → (Δ , S) ∷ (Δ , S ⟶ N) ∷ Ψ ﹔ Γ ⊢[ one ] t$ ∶ T) →
           (∀ {tv} → tv ∈ tvs → Ψ ﹔ Γ ⊢[ one ] tv ∶ T) →
           Ψ ﹔ Γ ⊢[ Δ ⇒ N ] tz ∷ tsu ∷ t$ ∷ tvs ∶ T
    bs-⟶ : ∀ {tΛ t$ tvs} →
           vbranches Δ N tvs →
           (S ∷ Δ , S′) ∷ Ψ ﹔ Γ ⊢[ one ] tΛ ∶ T →
           (∀ {S″} → wf? zer S″ → (Δ , S″) ∷ (Δ , S″ ⟶ S ⟶ S′) ∷ Ψ ﹔ Γ ⊢[ one ] t$ ∶ T) →
           (∀ {tv} → tv ∈ tvs → Ψ ﹔ Γ ⊢[ one ] tv ∶ T) →
           Ψ ﹔ Γ ⊢[ Δ ⇒ S ⟶ S′ ] tΛ ∷ t$ ∷ tvs ∶ T

  data _﹔_⊢s[_]_∶_ : GCtx → LCtx → Layer → LSubst → LCtx → Set where
    s-↑ : gwfs? Ψ →
          wfs? i Γ →
          wf? i T →
          Ψ ﹔ T ∷ Γ ⊢s[ i ] ↑ ∶ Γ
    s-I : gwfs? Ψ →
          wfs? i Γ →
          Ψ ﹔ Γ ⊢s[ i ] I ∶ Γ
    s-∘ : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Γ′ →
          Ψ ﹔ Γ′ ⊢s[ i ] δ′ ∶ Γ″ →
          --------------------------
          Ψ ﹔ Γ ⊢s[ i ] δ′ ∘ δ ∶ Γ″
    s-, : Ψ ﹔ Γ ⊢s[ i ] δ ∶ Δ →
          Ψ ﹔ Γ ⊢[ i ] s ∶ S →
          ----------------------------
          Ψ ﹔ Γ ⊢s[ i ] δ , s ∶ S ∷ Δ

  data _⊢s_∶_ : GCtx → GSubst → GCtx → Set where
    S-I : gwfs? Ψ →
          ----------
          Ψ ⊢s I ∶ Ψ
    S-↑ : gwfs? Ψ →
          gwf? (Γ , T) →
          --------------------
          (Γ , T) ∷ Ψ ⊢s ↑ ∶ Ψ
    S-, : Ψ ⊢s σ ∶ Φ →
          Ψ ﹔ Γ ⊢[ zer ] t ∶ T →
          ------------------------
          Ψ ⊢s σ , t ∶ (Γ , T) ∷ Φ
    S-∘ : Ψ ⊢s σ ∶ Ψ′ →
          Ψ′ ⊢s σ′ ∶ Ψ″ →
          ----------------
          Ψ ⊢s σ′ ∘ σ ∶ Ψ″
