{-# OPTIONS --without-K --safe #-}

module Untyped.Sem where

open import Lib
open import Untyped.Syntax

infix 5 _∙_↘_ ⟦_⟧_↘_
data _∙_↘_ : D → D → D → Set
data ⟦_⟧_↘_ : Exp → Ctx → D → Set

data _∙_↘_ where
  Λ∙ : ⟦ t ⟧ ρ ↦ a ↘ b →
       -- --------------
       Λ t ρ ∙ a ↘ b
  $∙ : ∀ e d → ne e ∙ d ↘ e $′ d

data ⟦_⟧_↘_ where
  ⟦v⟧ : ∀ n → ⟦ v n ⟧ ρ ↘ ρ n
  ⟦Λ⟧ : ∀ t → ⟦ Λ t ⟧ ρ ↘ Λ t ρ
  ⟦$⟧ : ⟦ r ⟧ ρ ↘ f →
        ⟦ s ⟧ ρ ↘ a →
        f ∙ a ↘ b →
        -- ---------------------
        ⟦ r $ s ⟧ ρ ↘ b

infix 5 Rf_-_↘_ Re_-_↘_
data Rf_-_↘_ : ℕ → D → Nf → Set
data Re_-_↘_ : ℕ → Dn → Ne → Set

data Rf_-_↘_ where
  RΛ  : ∀ n x →
        ⟦ t ⟧ ρ ↦ l′ x ↘ b →
        Rf suc n - b ↘ w →
        Rf n - Λ t ρ ↘ Λ w
  Rne : ∀ n →
        Re n - e ↘ u →
        Rf n - ne e ↘ ne u

data Re_-_↘_ where
  Rl : ∀ n x →
       Re n - l x ↘ v (n ∸ x ∸ 1)
  R$ : ∀ n →
       Re n - e ↘ u →
       Rf n - d ↘ w →
       Re n - e $ d ↘ u $ w

InitCtx : ℕ → Ctx
InitCtx n i = l′ (n ∸ i ∸ 1)

NormalForm : ℕ → Exp → Nf → Set
NormalForm n t w = ∃ λ d → ⟦ t ⟧ InitCtx n ↘ d × Rf n - d ↘ w
