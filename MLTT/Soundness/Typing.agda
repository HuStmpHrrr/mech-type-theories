{-# OPTIONS --without-K --safe #-}

-- A special set of typing rules just for soundness (the Sound formulation)
--
-- It appears that to establish the soundness proof, we need a bit strengthening of
-- induction hypothesis in the fundamental theorems, particularly in Λ-E and □-E
-- case. This set of rules only adds to the Concise formulation two premises. This set
-- of rules are defined to expose this strengthening and the added premises are marked
-- by
--
--     -- expose typing judgments for soundness proof
--
-- We then can show this formulation and the Concise formulation (i.e. the golden
-- formulation) is equivalent (actually we just need one directly),
-- c.f. MLTT.Soundness.Equiv for the proof.
module MLTT.Soundness.Typing where

open import Lib

open import MLTT.Statics.Syntax public
import MLTT.Statics.Concise as C


infix 4 ⊢_ _⊢_∶_ _⊢s_∶_


mutual
  data ⊢_ : Ctx → Set where
    ⊢[] : ⊢ []
    ⊢∷  : ∀ {i} →
          ⊢ Γ →
          Γ ⊢ T ∶ Se i →
          --------------
          ⊢ T ∷ Γ

  data _⊢_∶_ : Ctx → Exp → Typ → Set where
    N-wf    : ∀ i →
              ⊢ Γ →
              -------------
              Γ ⊢ N ∶ Se i
    Se-wf   : ∀ i →
              ⊢ Γ →
              ----------------
              Γ ⊢ Se i ∶ Se (1 + i)
    Π-wf    : ∀ {i} →
              Γ ⊢ S ∶ Se i →
              S ∷ Γ ⊢ T ∶ Se i →
              --------------------
              Γ ⊢ Π S T ∶ Se i
    vlookup : ∀ {x} →
              ⊢ Γ →
              x ∶ T ∈! Γ →
              ------------
              Γ ⊢ v x ∶ T
    ze-I    : ⊢ Γ →
              -----------
              Γ ⊢ ze ∶ N
    su-I    : Γ ⊢ t ∶ N →
              -------------
              Γ ⊢ su t ∶ N
    N-E     : ∀ {i} →
              N ∷ Γ ⊢ T ∶ Se i →
              Γ ⊢ s ∶ T [| ze ] →
              T ∷ N ∷ Γ ⊢ r ∶ T [ (wk ∘ wk) , su (v 1) ] →
              Γ ⊢ t ∶ N →
              --------------------------
              Γ ⊢ rec T s r t ∶ T [| t ]
    Λ-I     : S ∷ Γ ⊢ t ∶ T →
              ------------------
              Γ ⊢ Λ t ∶ Π S T
    Λ-E     : ∀ {i} →
              -- expose typing judgments for soundness proof
              S ∷ Γ ⊢ T ∶ Se i →
              Γ ⊢ r ∶ Π S T →
              Γ ⊢ s ∶ S →
              ---------------------
              Γ ⊢ r $ s ∶ T [| s ]
    t[σ]    : Δ ⊢ t ∶ T →
              Γ ⊢s σ ∶ Δ →
              ---------------------
              Γ ⊢ t [ σ ] ∶ T [ σ ]
    cumu    : ∀ {i} →
              Γ ⊢ T ∶ Se i →
              ------------------
              Γ ⊢ T ∶ Se (1 + i)
    conv    : ∀ {i} →
              Γ ⊢ t ∶ S →
              Γ C.⊢ S ≈ T ∶ Se i →
              ------------------
              Γ ⊢ t ∶ T

  data _⊢s_∶_ : Ctx → Subst → Ctx → Set where
    s-I    : ⊢ Γ →
             ------------
             Γ ⊢s I ∶ Γ
    s-wk   : ⊢ T ∷ Γ →
             ------------------
             T ∷ Γ ⊢s wk ∶ Γ
    s-∘    : Γ ⊢s τ ∶ Γ′ →
             Γ′ ⊢s σ ∶ Γ″ →
             ----------------
             Γ ⊢s σ ∘ τ ∶ Γ″
    s-,    : ∀ {i} →
             Γ ⊢s σ ∶ Δ →
             Δ ⊢ T ∶ Se i →
             Γ ⊢ t ∶ T [ σ ] →
             -------------------
             Γ ⊢s σ , t ∶ T ∷ Δ
    s-conv : Γ ⊢s σ ∶ Δ →
             C.⊢ Δ ≈ Δ′ →
             -------------
             Γ ⊢s σ ∶ Δ′
