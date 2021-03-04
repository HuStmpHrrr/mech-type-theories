{-# OPTIONS --without-K --safe #-}

module T.Soundness where

open import Lib
open import T.Statics
open import T.TypedSem

open Typing

record Top Γ T : Set where
  field
    tm   : Exp
    ⟦tm⟧ : D
    tm∶T : Γ ⊢ tm ∶ T
    krip : (σ : Weaken Δ Γ) → ∃ λ w → Rf List′.length Δ - ↓ T ⟦tm⟧ ↘ w × Δ ⊢ tm [ Weaken⇒Subst σ ] ≈ Nf⇒Exp w ∶ T

record Bot Γ T : Set where
  field
    tm   : Exp
    ⟦tm⟧ : Dn
    tm∶T : Γ ⊢ tm ∶ T
    krip : (σ : Weaken Δ Γ) → ∃ λ u → Re List′.length Δ - ⟦tm⟧ ↘ u × Δ ⊢ tm [ Weaken⇒Subst σ ] ≈ Ne⇒Exp u ∶ T
