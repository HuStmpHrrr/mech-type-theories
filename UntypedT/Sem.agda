{-# OPTIONS --without-K --safe #-}

module UntypedT.Sem where

open import Lib
open import UntypedT.Syntax

infix 5 _∙_↘_ ⟦_⟧_↘_ rec_,_,_↘_
data _∙_↘_ : D → D → D → Set
data ⟦_⟧_↘_ : Exp → Env → D → Set
data rec_,_,_↘_ : D → D → D → D → Set

data _∙_↘_ where
  Λ∙ : ⟦ t ⟧ ρ ↦ a ↘ b →
       -- --------------
       Λ t ρ ∙ a ↘ b
  $∙ : ∀ e d → ne e ∙ d ↘ e $′ d

data ⟦_⟧_↘_ where
  ⟦v⟧   : ∀ n → ⟦ v n ⟧ ρ ↘ ρ n
  ⟦ze⟧  : ⟦ ze ⟧ ρ ↘ ze
  ⟦su⟧  : ⟦ t ⟧ ρ ↘ d →
          -- --------------
          ⟦ su t ⟧ ρ ↘ su d
  ⟦rec⟧ : ⟦ s ⟧ ρ ↘ d′ →
          ⟦ r ⟧ ρ ↘ d″ →
          ⟦ t ⟧ ρ ↘ d →
          rec d′ , d″ , d ↘ a →
          -- --------------------
          ⟦ rec s r t ⟧ ρ ↘ a
  ⟦Λ⟧   : ∀ t → ⟦ Λ t ⟧ ρ ↘ Λ t ρ
  ⟦$⟧   : ⟦ r ⟧ ρ ↘ f →
          ⟦ s ⟧ ρ ↘ a →
          f ∙ a ↘ b →
          -- ---------------------
          ⟦ r $ s ⟧ ρ ↘ b

data rec_,_,_↘_ where
  rze : rec d′ , d″ , ze ↘ d′
  rsu : rec d′ , d″ , d ↘ a →
        d″ ∙ d ↘ f →
        f ∙ a ↘ b →
        -- -------------------
        rec d′ , d″ , su d ↘ b
  rec : rec d′ , d″ , ne e ↘ rec′ d′ d″ e

infix 5 Rf_-_↘_ Re_-_↘_
data Rf_-_↘_ : ℕ → D → Nf → Set
data Re_-_↘_ : ℕ → Dn → Ne → Set

data Rf_-_↘_ where
  Rze : ∀ n →
        Rf n - ze ↘ ze
  Rsu : ∀ n →
        Rf n - d ↘ w →
        Rf suc n - su d ↘ su w
  RΛ  : ∀ n x →
        ⟦ t ⟧ ρ ↦ l′ x ↘ b →
        Rf suc n - b ↘ w →
        -- ------------------
        Rf n - Λ t ρ ↘ Λ w
  Rne : ∀ n →
        Re n - e ↘ u →
        -- ------------------
        Rf n - ne e ↘ ne u

data Re_-_↘_ where
  Rl : ∀ n x →
       Re n - l x ↘ v (n ∸ x ∸ 1)
  Rr : ∀ n →
       Rf n - d′ ↘ w′ →
       Rf n - d″ ↘ w″ →
       Re n - e ↘ u →
       -- -------------------------------
       Re n - rec d′ d″ e ↘ rec w′ w″ u
  R$ : ∀ n →
       Re n - e ↘ u →
       Rf n - d ↘ w →
       -- ------------------
       Re n - e $ d ↘ u $ w

InitEnv : ℕ → Env
InitEnv n i = l′ (n ∸ i ∸ 1)

NormalForm : ℕ → Exp → Nf → Set
NormalForm n t w = ∃ λ d → ⟦ t ⟧ InitEnv n ↘ d × Rf n - d ↘ w
